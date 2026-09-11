"""Blogger Chrome 세션: 수동 로그인 후 블로그 인식."""
from __future__ import annotations

import os
import re
import shutil
import socket
import subprocess
import threading
import time
import urllib.request
from dataclasses import dataclass, field

from selenium import webdriver
from selenium.common.exceptions import WebDriverException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager

from paths import get_data_dir

BLOGGER_HOME = "https://www.blogger.com/"
BLOGGER_DEBUG_PORT = 9337


def _exc_text(exc: BaseException) -> str:
    name = type(exc).__name__
    msg = str(exc).replace("Message:", "").strip()
    if not msg:
        return f"{name}: 화면 요소를 찾지 못했거나 대기 시간이 지났습니다"
    return f"{name}: {msg}"

_BLOG_ID_RE = re.compile(r"^\d{10,}$")

_DETECT_JS = """
return (function() {
  const account = document.querySelector('meta[name="og-profile-acct"]')?.content || "";
  const isBlogId = (id) => /^\\d{10,}$/.test(id);
  const root = document.querySelector('[aria-label="Blog Selection"]') || document;
  const options = [...root.querySelectorAll('[role="option"][data-value]')];
  const blogs = [];
  const seen = new Set();
  for (const el of options) {
    const id = (el.getAttribute("data-value") || "").trim();
    if (!isBlogId(id) || seen.has(id)) continue;
    const name = (el.getAttribute("aria-label") || el.textContent || "").trim();
    if (!name || name.startsWith("새 블로그")) continue;
    seen.add(id);
    blogs.push({
      id,
      name,
      selected: el.getAttribute("aria-selected") === "true",
      address: "",
    });
  }
  const m = location.href.match(/\\/blog\\/(?:posts|post\\/edit|settings)\\/(\\d{10,})/);
  if (m && !seen.has(m[1])) {
    blogs.push({id: m[1], name: document.title.replace(/^Blogger:\\s*/, ""), selected: true, address: ""});
  }
  const addrEl = document.querySelector('[jscontroller="vo4Jme"] [jsname="bUNG7d"]');
  const address = (addrEl?.textContent || "").trim();
  const settingsId = (location.href.match(/\\/blog\\/settings\\/(\\d{10,})/) || [])[1] || "";
  if (address && settingsId) {
    const hit = blogs.find((b) => b.id === settingsId);
    if (hit) hit.address = address;
  }
  const isPostUrl = (href) => /https?:\\/\\/[^\\s/]+\\.blogspot\\.com\\/\\d{4}\\/\\d{2}\\/[^/?#\\s]+\\.html(?:[?#].*)?$/i.test(href || "");
  const postsId = (location.href.match(/\\/blog\\/posts\\/(\\d{10,})/) || [])[1] || "";
  const posts = [];
  const seenPost = new Set();
  if (postsId) {
    const items = [...document.querySelectorAll('[role="listitem"]')];
    for (const item of items) {
      const link = item.querySelector('a[aria-label="보기"][href], a.FKF6mc[href]');
      const href = link?.href || "";
      if (!isPostUrl(href) || seenPost.has(href)) continue;
      seenPost.add(href);
      const titleEl = item.querySelector('[id^="post-title-"]') || item.querySelector(".UHwcef");
      posts.push({url: href, title: (titleEl?.textContent || "").trim()});
    }
    const hit = blogs.find((b) => b.id === postsId);
    if (hit) hit.posts = posts;
  }
  return {
    account,
    blogs,
    url: location.href,
    title: document.title || "",
    address,
    posts,
    postsId,
  };
})();
"""


_POST_PERMALINK_RE = re.compile(
    r"^https?://[^/\s]+\.blogspot\.com/\d{4}/\d{2}/[^/?#\s]+\.html(?:[?#].*)?/?$",
    re.I,
)


def is_post_permalink(url: str) -> bool:
    return bool(_POST_PERMALINK_RE.match((url or "").strip()))


def normalize_post_url(url: str) -> str:
    url = (url or "").strip()
    return url if is_post_permalink(url) else ""


def normalize_posts(items) -> list[dict]:
    out: list[dict] = []
    seen: set[str] = set()
    for item in items or []:
        if isinstance(item, str):
            url = normalize_post_url(item)
            title = ""
        elif isinstance(item, dict):
            url = normalize_post_url(str(item.get("url") or item.get("postUrl") or ""))
            title = str(item.get("title") or item.get("postTitle") or "").strip()
        else:
            continue
        key = url.rstrip("/").lower()
        if not url or key in seen:
            continue
        seen.add(key)
        out.append({"url": url, "title": title})
    return out


def merge_posts(*groups) -> list[dict]:
    merged: list[dict] = []
    for group in groups:
        merged.extend(group or [])
    return normalize_posts(merged)


def host_from_post_url(url: str) -> str:
    match = re.search(r"https?://([^/\s]+\.blogspot\.com)", url or "", flags=re.I)
    return match.group(1).lower() if match else ""


def build_robots_txt(address: str) -> str:
    host = re.sub(r"^https?://", "", (address or "").strip(), flags=re.I).rstrip("/")
    if not host:
        raise RuntimeError("블로그 주소가 없어 robots.txt를 만들 수 없습니다.")
    base = f"https://{host}"
    return (
        "User-agent: *\n"
        "Allow: /\n"
        "\n"
        f"Sitemap: {base}/sitemap.xml\n"
        f"Sitemap: {base}/atom.xml\n"
    )


class StopRequested(Exception):
    pass


class RunControl:
    def __init__(self):
        self._pause = threading.Event()
        self._stop = threading.Event()

    def request_pause(self) -> None:
        self._pause.set()

    def request_resume(self) -> None:
        self._pause.clear()

    def request_stop(self) -> None:
        self._stop.set()
        self._pause.clear()

    def reset(self) -> None:
        self._pause.clear()
        self._stop.clear()

    @property
    def paused(self) -> bool:
        return self._pause.is_set()

    @property
    def stopped(self) -> bool:
        return self._stop.is_set()

    def checkpoint(self) -> None:
        while self._pause.is_set() and not self._stop.is_set():
            time.sleep(0.05)
        if self._stop.is_set():
            raise StopRequested("중지되었습니다.")


def _find_chrome() -> str:
    candidates = [
        os.path.expandvars(r"%PROGRAMFILES%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%PROGRAMFILES(X86)%\Google\Chrome\Application\chrome.exe"),
        os.path.expandvars(r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe"),
    ]
    for path in candidates:
        if path and os.path.isfile(path):
            return path
    found = shutil.which("chrome") or shutil.which("chrome.exe")
    if found:
        return found
    raise RuntimeError("Chrome을 찾지 못했습니다.")


def _free_port() -> int:
    sock = socket.socket()
    sock.bind(("127.0.0.1", 0))
    port = sock.getsockname()[1]
    sock.close()
    return port


def _wait_debug_port(port: int, timeout: float = 15) -> None:
    url = f"http://127.0.0.1:{port}/json/version"
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            with urllib.request.urlopen(url, timeout=0.4) as resp:
                if resp.status == 200:
                    return
        except Exception:
            time.sleep(0.08)
    raise RuntimeError("실제 Chrome 창에 연결하지 못했습니다.")


def _displayed(elements):
    for el in elements:
        try:
            if el.is_displayed():
                return el
        except Exception:
            continue
    return None


SETTING_ITEMS = (
    ("description", "디스크립션"),
    ("search_desc", "검색설명"),
    ("favicon", "파비콘"),
    ("timezone", "시간대"),
    ("robots", "robots.txt"),
    ("headers", "헤더태그"),
    ("naver_verify", "소유확인"),
    ("theme_head", "테마헤더"),
    ("crawl_fast", "수집주기"),
    ("naver_robots", "로봇수집"),
    ("sitemap", "사이트맵"),
    ("collect", "블로그수집"),
    ("collect_post", "글수집"),
)

_FIND_THEME_CM_JS = """
function findThemeCM() {
  let best = null;
  let bestScore = -1;
  for (const el of document.querySelectorAll(".CodeMirror")) {
    const cm = el.CodeMirror;
    if (!cm || typeof cm.getValue !== "function") continue;
    const v = cm.getValue() || "";
    let score = v.length;
    if (/<head\\b|&lt;head/i.test(v)) score += 1000000;
    if (/xmlns:b|all-head-content|b:version/i.test(v)) score += 200000;
    if (/DOCTYPE html/i.test(v)) score += 50000;
    if (score > bestScore) { bestScore = score; best = cm; }
  }
  if (best) return best;
  const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
  let p = ta ? ta.parentElement : null;
  while (p) {
    if (p.CodeMirror && typeof p.CodeMirror.getValue === "function") return p.CodeMirror;
    p = p.parentElement;
  }
  return null;
}
"""


@dataclass
class BlogInfo:
    id: str
    name: str
    selected: bool = False
    address: str = ""
    posts: list[dict] = field(default_factory=list)
    done: set[str] = field(default_factory=set)

    @property
    def post_url(self) -> str:
        return str(self.posts[0].get("url") or "") if self.posts else ""

    @property
    def post_title(self) -> str:
        return str(self.posts[0].get("title") or "") if self.posts else ""


@dataclass
class SessionState:
    account: str = ""
    blogs: list[BlogInfo] = field(default_factory=list)
    url: str = ""
    title: str = ""

    @property
    def logged_in(self) -> bool:
        if self.account:
            return True
        if self.blogs:
            return True
        return "/blog/posts/" in (self.url or "")


class BloggerSession:
    def __init__(self, log):
        self.log = log
        self.driver: webdriver.Chrome | None = None
        self.state = SessionState()
        self._lock = threading.Lock()
        self.control = RunControl()
        self._on_progress = None
        self._on_item_done = None
        self._chrome_proc: subprocess.Popen | None = None
        self._chrome_user_dir: str | None = None

    def profile_dir(self) -> str:
        path = os.path.join(get_data_dir(), "chrome-blogger-session")
        os.makedirs(path, exist_ok=True)
        return path

    def chrome_running(self) -> bool:
        try:
            with urllib.request.urlopen(
                f"http://127.0.0.1:{BLOGGER_DEBUG_PORT}/json/version", timeout=0.4
            ) as resp:
                return resp.status == 200
        except Exception:
            return False

    def is_alive(self) -> bool:
        driver = self.driver
        if driver is None:
            return False
        for _ in range(3):
            try:
                _ = driver.current_url
                return True
            except Exception:
                time.sleep(0.15)
        return False

    def start_incognito(self) -> None:
        self.start_browser()

    def start_browser(self) -> None:
        with self._lock:
            if self.driver is not None and self.is_alive():
                self.log("이미 열려 있는 블로그스팟 Chrome 창을 앞으로 가져옵니다.")
                try:
                    self.driver.switch_to.window(self.driver.current_window_handle)
                except Exception:
                    pass
                return

            chrome = _find_chrome()
            profile = self.profile_dir()
            self._chrome_user_dir = profile
            if self.chrome_running():
                self.log("기존 블로그스팟 Chrome에 다시 연결합니다.")
            else:
                self.log("블로그스팟 Chrome 창을 여는 중...")
                cmd = [
                    chrome,
                    f"--remote-debugging-port={BLOGGER_DEBUG_PORT}",
                    f"--user-data-dir={profile}",
                    "--no-first-run",
                    "--no-default-browser-check",
                    "--disable-popup-blocking",
                    "--disable-blink-features=AutomationControlled",
                    "--window-size=1400,900",
                    BLOGGER_HOME,
                ]
                self._chrome_proc = subprocess.Popen(cmd)
                _wait_debug_port(BLOGGER_DEBUG_PORT)

            options = Options()
            options.add_experimental_option("debuggerAddress", f"127.0.0.1:{BLOGGER_DEBUG_PORT}")
            service = Service(ChromeDriverManager().install())
            driver = webdriver.Chrome(service=service, options=options)
            try:
                driver.execute_cdp_cmd(
                    "Page.addScriptToEvaluateOnNewDocument",
                    {
                        "source": "Object.defineProperty(navigator, 'webdriver', {get: () => undefined});"
                    },
                )
            except Exception:
                pass
            self.driver = driver
            self.state = SessionState()

        self.log("실제 Chrome 창에 연결했습니다. 직접 로그인해 주세요.")

    def detect(self) -> SessionState:
        if not self.is_alive():
            return SessionState()
        try:
            raw = self.driver.execute_script(_DETECT_JS)
        except WebDriverException:
            return SessionState()
        previous = {blog.id: blog for blog in self.state.blogs}
        blogs = []
        seen = set()
        for item in (raw or {}).get("blogs") or []:
            blog_id = str(item.get("id") or "").strip()
            name = str(item.get("name") or "").strip()
            if not _BLOG_ID_RE.match(blog_id) or blog_id in seen:
                continue
            if not name or name.startswith("새 블로그"):
                continue
            seen.add(blog_id)
            old = previous.get(blog_id)
            address = str(item.get("address") or "").strip()
            if not address and old:
                address = old.address
            page_posts = normalize_posts(item.get("posts") or [])
            if not page_posts and item.get("postUrl"):
                page_posts = normalize_posts(
                    [{"url": item.get("postUrl"), "title": item.get("postTitle")}]
                )
            if page_posts:
                posts = page_posts
            elif old:
                posts = list(old.posts)
            else:
                posts = []
            if posts and not address:
                address = host_from_post_url(str(posts[0].get("url") or ""))
            blogs.append(
                BlogInfo(
                    id=blog_id,
                    name=name,
                    selected=bool(item.get("selected")),
                    address=address,
                    posts=posts,
                    done=set(old.done) if old else set(),
                )
            )
        if not blogs and previous:
            blogs = list(previous.values())
        state = SessionState(
            account=str((raw or {}).get("account") or ""),
            blogs=blogs,
            url=str((raw or {}).get("url") or ""),
            title=str((raw or {}).get("title") or ""),
        )
        self.state = state
        return state

    def wait_until_logged_in(self, poll_sec: float = 1.0, timeout: float | None = None) -> SessionState:
        started = time.time()
        while self.is_alive():
            state = self.detect()
            if state.logged_in:
                return state
            if timeout is not None and time.time() - started >= timeout:
                break
            time.sleep(poll_sec)
        return self.state

    def open_blog_posts(self, blog_id: str) -> None:
        if not self.is_alive():
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        url = f"https://www.blogger.com/blog/posts/{blog_id}"
        self.log(f"블로그 글 목록으로 이동: {blog_id}")
        self.driver.get(url)
        self._wait_posts_list()
        self.detect()
        self.read_published_post(blog_id)

    def click_new_post(self) -> None:
        if not self.is_alive():
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        wait = WebDriverWait(self.driver, 20)
        button = wait.until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, '[aria-label="새 글 작성"]'))
        )
        button.click()
        self.log("새 글 작성 화면을 열었습니다.")

    def fill_post(self, title: str, body: str, publish: bool = False) -> bool:
        if not self.is_alive():
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        wait = WebDriverWait(self.driver, 25)
        wait.until(lambda d: "/blog/post/edit" in (d.current_url or ""))
        wait.until(
            EC.presence_of_element_located(
                (
                    By.CSS_SELECTOR,
                    '[contenteditable="true"], [aria-label="제목"], [placeholder="제목"], input, textarea',
                )
            )
        )

        title_el = self._find_first(
            [
                '[aria-label="제목"]',
                '[placeholder="제목"]',
                'input[aria-label="Title"]',
                '[placeholder="Title"]',
            ],
        )
        if title_el is None:
            self.log("제목 입력란을 찾지 못했습니다. 편집기 HTML이 필요합니다.")
            return False
        self._set_text(title_el, title)

        body_el = self._find_first(
            [
                '[aria-label="내용"]',
                '[aria-label="본문"]',
                '[role="textbox"][contenteditable="true"]',
                'div[contenteditable="true"]',
            ],
        )
        if body_el is None:
            self.log("본문 입력란을 찾지 못했습니다. 편집기 HTML이 필요합니다.")
            return False
        self._set_text(body_el, body)
        self.log("원고를 편집기에 입력했습니다.")

        if not publish:
            return True

        publish_el = self._find_first(
            [
                '[aria-label="게시"]',
                'button[aria-label="게시"]',
                '[data-tooltip="게시"]',
            ],
        )
        if publish_el is None:
            self.log("게시 버튼을 찾지 못해 초안으로 남겨 두었습니다.")
            return True
        self._click_jsaction(publish_el)
        self._tick(0.4)
        self._confirm_publish_dialog()
        self.log("게시를 클릭했습니다.")
        return True

    def _confirm_publish_dialog(self) -> None:
        try:
            dialog = self._wait_dialog(timeout=3)
        except Exception:
            dialog = self._visible_dialog()
        if dialog is None:
            return
        try:
            self._click_named_button(dialog, "게시", wait_enabled=False)
        except Exception:
            try:
                self._click_jsaction(dialog)
            except Exception:
                pass

    def _wait_posts_list(self) -> None:
        self._wait(20).until(lambda d: "/blog/posts/" in (d.current_url or ""))
        self._wait(15).until(
            lambda d: bool(
                d.find_elements(
                    By.CSS_SELECTOR,
                    '[role="listitem"], [aria-label="새 글 작성"], a[aria-label="보기"]',
                )
            )
        )
        self._tick(0.3)

    def read_published_posts(self, blog_id: str = "") -> list[dict]:
        raw = self.driver.execute_script(
            """
            const isPostUrl = (href) => /https?:\\/\\/[^\\s/]+\\.blogspot\\.com\\/\\d{4}\\/\\d{2}\\/[^/?#\\s]+\\.html(?:[?#].*)?$/i.test(href || "");
            const items = [...document.querySelectorAll('[role="listitem"]')];
            const posts = [];
            const seen = new Set();
            for (const item of items) {
              const link = item.querySelector('a[aria-label="보기"][href], a.FKF6mc[href]');
              const href = link?.href || "";
              if (!isPostUrl(href) || seen.has(href)) continue;
              seen.add(href);
              const titleEl = item.querySelector('[id^="post-title-"]') || item.querySelector(".UHwcef");
              posts.push({url: href, title: (titleEl?.textContent || "").trim()});
            }
            return posts;
            """
        ) or []
        posts = normalize_posts(raw)
        current = blog_id or ""
        if not current:
            match = re.search(r"/blog/posts/(\d{10,})", self.driver.current_url or "")
            current = match.group(1) if match else ""
        if current:
            for blog in self.state.blogs:
                if blog.id != current:
                    continue
                if posts:
                    blog.posts = posts
                    if not blog.address:
                        blog.address = host_from_post_url(str(posts[0].get("url") or ""))
                break
        return posts

    def read_published_post(self, blog_id: str = "") -> dict:
        posts = self.read_published_posts(blog_id)
        if not posts:
            return {"url": "", "title": ""}
        return {"url": str(posts[0].get("url") or ""), "title": str(posts[0].get("title") or "")}

    def wait_and_read_post_url(self, blog_id: str) -> str:
        try:
            self._wait(25).until(lambda d: "/blog/posts/" in (d.current_url or ""))
        except Exception:
            self.open_blog_posts(blog_id)
            posts = self.read_published_posts(blog_id)
            return str(posts[0].get("url") or "") if posts else ""
        self._wait_posts_list()
        self.detect()
        try:
            self._wait(12).until(lambda d: bool(self.read_published_posts(blog_id)))
        except Exception:
            pass
        posts = self.read_published_posts(blog_id)
        return str(posts[0].get("url") or "") if posts else ""

    def fetch_published_post_urls(self, force: bool = False) -> None:
        pending = []
        skipped = 0
        for blog in list(self.state.blogs):
            if not force and blog.posts:
                skipped += 1
                continue
            pending.append(blog)
        if skipped:
            self.log(f"글 목록을 이미 아는 블로그 {skipped}개는 다시 들어가지 않습니다.")
        if not pending:
            if skipped:
                self.log("확인할 새 글 목록이 없습니다.")
            return
        self.log(f"글 목록을 확인할 블로그 {len(pending)}개")
        for blog in pending:
            if not self.is_alive():
                return
            try:
                self.open_blog_posts(blog.id)
                posts = self.read_published_posts(blog.id)
                if posts:
                    self.log(f"글 {len(posts)}개 인식: {blog.name}")
                    for post in posts:
                        self.log(f"  · {post.get('url')}")
                else:
                    self.log(f"게시된 글 주소를 찾지 못했습니다: {blog.name}")
            except Exception as exc:
                self.log(f"글 주소 읽기 실패 ({blog.name}): {exc}")

    def open_settings(self, blog_id: str) -> None:
        if not self.is_alive():
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        url = f"https://www.blogger.com/blog/settings/{blog_id}"
        self.log(f"설정 페이지로 이동: {blog_id}")
        self.driver.get(url)
        self._wait(12).until(
            EC.presence_of_element_located(
                (By.CSS_SELECTOR, '[jscontroller="vo4Jme"], [jscontroller="sHhTg"]')
            )
        )
        self._tick()
        self.detect()

    def read_blog_address(self) -> str:
        try:
            el = self.driver.find_element(
                By.CSS_SELECTOR, '[jscontroller="vo4Jme"] [jsname="bUNG7d"]'
            )
            address = (el.text or "").strip()
        except Exception:
            address = ""
        if address:
            current = self._current_settings_blog_id()
            for blog in self.state.blogs:
                if blog.id == current:
                    blog.address = address
                    break
        return address

    def fetch_blog_addresses(self, force: bool = False) -> None:
        pending = []
        skipped = 0
        for blog in list(self.state.blogs):
            if not force and (blog.address or "").strip():
                skipped += 1
                continue
            pending.append(blog)
        if skipped:
            self.log(f"주소가 있는 블로그 {skipped}개는 설정 페이지를 다시 열지 않습니다.")
        if pending:
            self.log(f"주소를 확인할 블로그 {len(pending)}개")
        for blog in pending:
            if not self.is_alive():
                return
            try:
                self.open_settings(blog.id)
                address = self.read_blog_address()
                blog.address = address
                if address:
                    self.log(f"블로그 주소 인식: {blog.name} → {address}")
                else:
                    self.log(f"블로그 주소를 찾지 못했습니다: {blog.name}")
            except Exception as exc:
                self.log(f"블로그 주소 읽기 실패 ({blog.name}): {exc}")
        self.fetch_published_post_urls(force=force)

    def inject_theme_head(self, blog_id: str, snippet: str) -> None:
        if not self.is_alive():
            raise RuntimeError("블로그스팟 브라우저가 닫혀 있습니다.")
        if not (snippet or "").strip():
            raise RuntimeError("테마에 넣을 HTML 코드가 없습니다.")
        self.control.checkpoint()
        self.log(f"테마에 넣을 코드: {snippet.strip()[:180]}")
        self.open_theme_html_editor(blog_id)
        try:
            self._wait_theme_head()
        except Exception:
            sample = re.sub(r"\s+", " ", (self._read_theme_html() or ""))[:180]
            raise RuntimeError(f"테마 HTML에서 <head>를 찾지 못했습니다. {sample}")
        inserted = ""
        last_error = "empty"
        for attempt in range(4):
            result = self._insert_head_snippet(snippet)
            inserted = str(result.get("how") or "")
            if result.get("ok"):
                break
            last_error = str(result.get("reason") or "unknown")
            sample = str(result.get("sample") or "")
            extra = f" / {sample}" if sample else ""
            self.log(f"테마 head 삽입 재시도 ({attempt + 1}/4): {last_error}{extra}")
            self._tick(0.6)
        else:
            raise RuntimeError(f"테마 HTML을 수정하지 못했습니다: {last_error}")
        if inserted == "already":
            self.log("테마 <head> 바로 아래에 소유확인 코드가 이미 있습니다.")
        else:
            self.log(f"테마 <head> 바로 아래에 소유확인 HTML을 넣었습니다. ({inserted})")
        self._save_theme_html()
        saved = self._read_theme_html()
        if not re.search(r"naver-site-verification", saved or "", re.I):
            raise RuntimeError("저장 후에도 테마 head에 소유확인 코드가 없습니다.")
        self.log("테마 HTML을 저장했습니다.")

    def open_theme_html_editor(self, blog_id: str) -> None:
        url = f"https://www.blogger.com/blog/themes/{blog_id}"
        self.log(f"테마 페이지로 이동: {blog_id}")
        self.driver.get(url)
        self._wait(15).until(
            lambda d: f"/blog/themes/{blog_id}" in (d.current_url or "")
        )
        self._tick(0.8)
        if self._theme_editor_ready():
            self.log("테마 HTML 편집기가 이미 열려 있습니다.")
            return
        last_error = ""
        for attempt in range(4):
            if self._theme_editor_ready():
                break
            more = self._find_theme_more_button()
            if more is None:
                last_error = "추가 작업 버튼을 찾지 못했습니다."
                self._tick(0.5)
                continue
            self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", more)
            self._tick(0.15)
            expanded = (more.get_attribute("aria-expanded") or "").lower() == "true"
            if not expanded:
                self._click_jsaction(more)
                self._tick(0.45)
            edit = self._find_html_edit_item()
            if edit is None:
                last_error = "HTML 편집 메뉴를 찾지 못했습니다."
                self.log(f"HTML 편집 메뉴 대기 중 ({attempt + 1}/4)")
                continue
            self.log("HTML 편집 메뉴를 클릭합니다.")
            self._click_jsaction(edit)
            try:
                self._wait(12).until(lambda d: self._theme_editor_ready())
                break
            except Exception:
                last_error = "HTML 편집 창이 열리지 않았습니다."
                self.log(f"HTML 편집 클릭 후 편집기 대기 실패 ({attempt + 1}/4)")
        else:
            raise RuntimeError(last_error or "HTML 편집을 열지 못했습니다.")
        self._tick(0.4)
        self.log("HTML 편집 창을 열었습니다.")

    def _find_theme_more_button(self):
        return self.driver.execute_script(
            """
            const sels = [
              '[aria-label="추가 작업"]',
              '[aria-label="More actions"]',
              '[jsname="Lu0Fq"]',
            ];
            let best = null;
            let bestScore = -1;
            for (const sel of sels) {
              for (const el of document.querySelectorAll(sel)) {
                const r = el.getBoundingClientRect();
                const style = getComputedStyle(el);
                if (r.width < 8 || r.height < 8) continue;
                if (style.visibility === "hidden" || style.display === "none") continue;
                const score = r.width * r.height + (r.top < 160 ? 400 : 0);
                if (score > bestScore) {
                  bestScore = score;
                  best = el;
                }
              }
            }
            return best;
            """
        )

    def _find_html_edit_item(self):
        return self.driver.execute_script(
            """
            function visible(el) {
              if (!el) return false;
              const r = el.getBoundingClientRect();
              const style = getComputedStyle(el);
              if (r.width < 8 || r.height < 8) return false;
              if (r.bottom < 0 || r.top > innerHeight) return false;
              if (style.visibility === "hidden" || style.display === "none" || style.opacity === "0") return false;
              return true;
            }
            const exact = document.querySelector('[role="menuitem"][aria-label="현재 테마의 소스 코드 수정"]');
            if (visible(exact)) return exact;
            const named = document.querySelector('[jsname="GcaN6c"]');
            if (named) {
              const item = named.closest('[role="menuitem"]') || named;
              if (visible(item)) return item;
            }
            for (const el of document.querySelectorAll('[role="menuitem"]')) {
              const aria = (el.getAttribute("aria-label") || "").trim();
              const text = (el.textContent || "").replace(/\\s+/g, " ").trim();
              if (aria === "현재 테마의 소스 코드 수정" || text === "HTML 편집" || text === "Edit HTML") {
                if (visible(el)) return el;
              }
            }
            return null;
            """
        )

    def _click_jsaction(self, element) -> None:
        self.driver.execute_script(
            """
            const el = arguments[0];
            el.scrollIntoView({block: "center"});
            const r = el.getBoundingClientRect();
            const x = r.left + r.width / 2;
            const y = r.top + r.height / 2;
            const opts = {bubbles: true, cancelable: true, view: window, clientX: x, clientY: y, button: 0};
            el.dispatchEvent(new PointerEvent("pointerdown", opts));
            el.dispatchEvent(new MouseEvent("mousedown", opts));
            el.dispatchEvent(new PointerEvent("pointerup", opts));
            el.dispatchEvent(new MouseEvent("mouseup", opts));
            el.dispatchEvent(new MouseEvent("click", opts));
            try { el.click(); } catch (e) {}
            """,
            element,
        )
        try:
            element.click()
        except Exception:
            pass

    def _theme_editor_ready(self) -> bool:
        try:
            html = self._read_theme_html()
            if not html or len(html) < 200:
                return False
            return bool(re.search(r"<head\b|&lt;head", html, re.I))
        except Exception:
            return False

    def _read_theme_html(self) -> str:
        try:
            return (
                self.driver.execute_script(
                    _FIND_THEME_CM_JS
                    + """
                    const cm = findThemeCM();
                    if (cm) {
                      const v = cm.getValue() || "";
                      if (v.length > 20) return v;
                    }
                    const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
                    return ta ? (ta.value || "") : "";
                    """
                )
                or ""
            )
        except Exception:
            return ""

    def _wait_theme_head(self) -> None:
        self._wait(20).until(
            lambda d: bool(re.search(r"<head\b|&lt;head", self._read_theme_html(), re.I))
        )
        self._tick(0.3)

    def _insert_head_snippet(self, snippet: str) -> dict:
        result = self.driver.execute_script(
            _FIND_THEME_CM_JS
            + """
            const snippet = arguments[0];
            const contentMatch = String(snippet).match(/content=["']([^"']+)["']/i);
            const contentVal = contentMatch ? contentMatch[1] : "";
            const clean = String(snippet).trim();

            function getHtml() {
              const cm = findThemeCM();
              if (cm) {
                const v = cm.getValue() || "";
                if (v.length > 20) return v;
              }
              const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
              return ta ? (ta.value || "") : "";
            }
            function setTextarea(html) {
              const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
              if (!ta) return false;
              const setter = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, "value")?.set;
              if (setter) setter.call(ta, html);
              else ta.value = html;
              ta.dispatchEvent(new Event("input", {bubbles: true}));
              ta.dispatchEvent(new Event("change", {bubbles: true}));
              return true;
            }
            function setHtml(html) {
              const cm = findThemeCM();
              setTextarea(html);
              if (cm) {
                cm.setValue(html);
                try { cm.save(); } catch (e) {}
                try { cm.refresh(); } catch (e) {}
                try { cm.focus(); } catch (e) {}
                try {
                  cm.replaceRange(" ", {line: 0, ch: 0}, {line: 0, ch: 0});
                  cm.replaceRange("", {line: 0, ch: 0}, {line: 0, ch: 1});
                  if (cm.getValue() !== html) cm.setValue(html);
                } catch (e) {}
                return "cm";
              }
              return setTextarea(html) ? "textarea" : "";
            }
            function insertAfterHead(html, tag) {
              const headRe = /(<head\\b[^>]*>)/i;
              if (headRe.test(html)) return html.replace(headRe, "$1\\n    " + tag);
              const entRe = /(&lt;head(?:\\s[^&]*)?&gt;)/i;
              if (entRe.test(html)) return html.replace(entRe, "$1\\n    " + tag);
              const htmlRe = /(<html\\b[^>]*>)/i;
              if (htmlRe.test(html)) return html.replace(htmlRe, "$1\\n<head>\\n    " + tag + "\\n</head>");
              return "";
            }

            let html = getHtml();
            if (!html || html.length < 20) {
              return {ok: false, reason: "empty", len: (html || "").length};
            }
            if (contentVal && new RegExp("naver-site-verification[^>]{0,160}" + contentVal.replace(/[.*+?^${}()|[\\]\\\\]/g, "\\\\$&"), "i").test(html)) {
              return {ok: true, how: "already"};
            }
            html = html.replace(/\\s*<meta[^>]*naver-site-verification[^>]*>\\s*/ig, "\\n");
            html = html.replace(/\\s*&lt;meta[^&]*naver-site-verification[^&]*&gt;\\s*/ig, "\\n");
            const next = insertAfterHead(html, clean);
            if (!next) {
              const sample = html.replace(/\\s+/g, " ").slice(0, 180);
              return {ok: false, reason: "no-head", sample: sample};
            }
            const how = setHtml(next);
            if (!how) return {ok: false, reason: "set"};
            const after = getHtml();
            const placed = /naver-site-verification/i.test(after);
            if (!placed) return {ok: false, reason: "not-applied", how: how, len: after.length};
            return {ok: true, how: how, len: after.length};
            """,
            snippet,
        ) or {}
        return result if isinstance(result, dict) else {"ok": False, "reason": "script"}

    def _save_theme_html(self) -> None:
        save = self._wait(10).until(
            lambda d: self._find_first(
                [
                    '[aria-label="저장"]',
                    '[jsname="UtZwdf"]',
                    '[jsname="ktSouf"] [aria-label="저장"]',
                ]
            )
        )
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", save)
        self._tick()
        disabled = (save.get_attribute("aria-disabled") or "").lower()
        if disabled == "true":
            try:
                self._wait(8).until(
                    lambda d: (
                        (self._find_first(['[aria-label="저장"]', '[jsname="UtZwdf"]']) or save)
                        .get_attribute("aria-disabled")
                        or ""
                    ).lower()
                    != "true"
                )
                save = self._find_first(['[aria-label="저장"]', '[jsname="UtZwdf"]']) or save
            except Exception:
                self.log("저장 버튼이 비활성화되어 있어 편집기 변경 감지를 한 번 더 시도합니다.")
                self.driver.execute_script(
                    _FIND_THEME_CM_JS
                    + """
                    const cm = findThemeCM();
                    if (cm) {
                      const v = cm.getValue();
                      cm.setValue(v);
                      try { cm.save(); } catch (e) {}
                    }
                    """
                )
                self._tick(0.4)
                save = self._find_first(['[aria-label="저장"]', '[jsname="UtZwdf"]']) or save
        self._click_jsaction(save)
        self.driver.execute_script(
            """
            const save = document.querySelector('[jsname="UtZwdf"], [aria-label="저장"]');
            if (save) save.click();
            """
        )
        self._tick(1.2)
        try:
            WebDriverWait(self.driver, 12, poll_frequency=0.2).until(
                lambda d: "저장" in (d.page_source or "") or True
            )
        except Exception:
            pass

    def apply_basic_settings(
        self,
        blog_id: str,
        description: str,
        favicon_path: str,
        control: RunControl | None = None,
        on_progress=None,
        on_item_done=None,
    ) -> str:
        self.control = control or RunControl()
        self._on_progress = on_progress
        self._on_item_done = on_item_done
        total = 8
        self._report(1, total, "설정 페이지")
        self.open_settings(blog_id)
        address = self.read_blog_address()
        if address:
            self.log(f"블로그 주소: {address}")

        self._report(2, total, "구글,네이버 디스크립션")
        if description:
            self.set_google_description(description)
            self._mark_done(blog_id, "description")
        self._report(3, total, "검색 설명")
        self.enable_search_description()
        if description:
            self.set_search_description(description)
            self._mark_done(blog_id, "search_desc")
        self._report(4, total, "파비콘")
        if favicon_path:
            self.set_favicon(favicon_path)
            self._mark_done(blog_id, "favicon")
        self._report(5, total, "시간대")
        if self._try_setting_step("시간대", self.set_timezone_seoul):
            self._mark_done(blog_id, "timezone")
        self._report(6, total, "robots.txt")
        if self._try_setting_step("robots.txt", lambda: self.apply_robots_settings(address)):
            self._mark_done(blog_id, "robots")
        self._report(7, total, "로봇 헤더 태그")
        if self._try_setting_step("로봇 헤더 태그", self.apply_robot_header_settings):
            self._mark_done(blog_id, "headers")
        self._report(8, total, "완료")
        return address

    def _try_setting_step(self, label: str, fn) -> bool:
        try:
            fn()
            return True
        except Exception as exc:
            self.log(f"{label} 적용 실패, 다음 단계로 넘어갑니다: {_exc_text(exc)}")
            try:
                self._close_open_dialogs()
            except Exception:
                pass
            return False

    def set_google_description(self, text: str) -> None:
        self._close_open_dialogs()
        self._click_setting_row("sHhTg", "설명")
        self._fill_visible_dialog(text, title_hint="설명")
        self.log(f"구글,네이버 디스크립션을 입력했습니다: {text}")

    def set_search_description(self, text: str) -> None:
        self._wait_setting_unlocked("mM3Kjc")
        self._close_open_dialogs()
        self._click_setting_row("mM3Kjc", "검색 설명")
        self._fill_visible_dialog(text, title_hint="검색 설명")
        self.log(f"검색 설명을 입력했습니다: {text}")

    def set_favicon(self, image_path: str) -> None:
        path = os.path.abspath(image_path)
        if not os.path.isfile(path):
            raise RuntimeError(f"파비콘 파일이 없습니다: {path}")
        self._close_open_dialogs()
        self._click_setting_row("siI7L", "파비콘")
        dialog = self._wait_dialog("파비콘")
        file_input = self._wait(8).until(
            EC.presence_of_element_located(
                (By.CSS_SELECTOR, 'input[jsname="yy8Dje"], form[jsname="kC0yHd"] input[type="file"]')
            )
        )
        file_input.send_keys(path)
        self._click_named_button(dialog, "저장", wait_enabled=True)
        self._wait_dialog_closed(dialog)
        self.log(f"파비콘을 올렸습니다: {os.path.basename(path)}")

    def set_timezone_seoul(self) -> None:
        self._close_open_dialogs()
        row = self._find_setting_row("DbluJc", "시간대")
        if row is None:
            raise RuntimeError("시간대 설정 항목을 찾지 못했습니다.")
        current = (row.get_attribute("data-value") or "").strip()
        row_text = ""
        try:
            row_text = row.text or ""
        except Exception:
            pass
        if current == "Asia/Seoul" or "서울" in row_text:
            self.log("시간대는 이미 서울입니다.")
            return
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", row)
        self._tick()
        self._click_jsaction(row)
        self._wait(12).until(
            lambda d: bool(
                d.find_elements(By.CSS_SELECTOR, '[role="radio"][data-value], [role="listbox"]')
            )
        )
        picked = self.driver.execute_script(
            """
            const radios = [...document.querySelectorAll('[role="radio"]')];
            const seoul = radios.find((r) => {
              const value = r.getAttribute("data-value") || "";
              const label = r.getAttribute("aria-label") || r.textContent || "";
              return value === "Asia/Seoul" || label.includes("서울");
            });
            if (!seoul) return "missing";
            let box = seoul.parentElement;
            while (box) {
              const st = getComputedStyle(box);
              if ((st.overflowY === "auto" || st.overflowY === "scroll") && box.scrollHeight > box.clientHeight + 8) {
                const top = seoul.getBoundingClientRect().top - box.getBoundingClientRect().top + box.scrollTop;
                box.scrollTop = Math.max(0, top - box.clientHeight / 2);
                break;
              }
              box = box.parentElement;
            }
            seoul.scrollIntoView({block: "center"});
            if (seoul.getAttribute("aria-checked") === "true") return "already";
            const r = seoul.getBoundingClientRect();
            const opts = {bubbles: true, cancelable: true, view: window, clientX: r.left + r.width / 2, clientY: r.top + r.height / 2, button: 0};
            seoul.dispatchEvent(new PointerEvent("pointerdown", opts));
            seoul.dispatchEvent(new MouseEvent("mousedown", opts));
            seoul.dispatchEvent(new PointerEvent("pointerup", opts));
            seoul.dispatchEvent(new MouseEvent("mouseup", opts));
            seoul.dispatchEvent(new MouseEvent("click", opts));
            try { seoul.click(); } catch (e) {}
            return seoul.getAttribute("aria-checked") === "true" ? "checked" : "clicked";
            """
        )
        if picked == "missing":
            raise RuntimeError("시간대 목록에서 서울을 찾지 못했습니다.")
        self.log(f"시간대 서울 선택: {picked}")
        self._tick(0.35)
        dialog = self._visible_dialog()
        try:
            self._click_save(dialog)
        except Exception:
            saved = self.driver.execute_script(
                """
                const buttons = [...document.querySelectorAll('[role="button"]')];
                const save = buttons.find((b) => (b.textContent || "").includes("저장") && b.offsetParent);
                if (!save) return false;
                save.click();
                return true;
                """
            )
            if not saved:
                raise RuntimeError("시간대 저장 버튼을 찾지 못했습니다.")
        if dialog is not None:
            self._wait_dialog_closed(dialog)
        try:
            self._wait(10).until(
                lambda d: (
                    (self._find_setting_row("DbluJc", "시간대") or row).get_attribute("data-value")
                    or ""
                ).strip()
                == "Asia/Seoul"
                or "서울" in ((self._find_setting_row("DbluJc", "시간대") or row).text or "")
            )
        except Exception as exc:
            raise RuntimeError("시간대를 서울로 저장했는지 확인하지 못했습니다.") from exc
        self.log("시간대를 서울로 변경하고 저장했습니다.")

    def enable_search_description(self) -> None:
        self._enable_aria_checkbox("검색 설명 사용 설정")

    def apply_robots_settings(self, address: str) -> None:
        self._enable_aria_checkbox("맞춤 robots.txt 사용 설정")
        self._wait_setting_unlocked("AyIhkc")
        self.set_custom_robots_txt(address)

    def apply_robot_header_settings(self) -> None:
        self._enable_aria_checkbox("맞춤 로봇 헤더 태그 사용 설정")
        self._wait_setting_unlocked("ZVRmn")
        self.enable_homepage_all_tag()

    def set_custom_robots_txt(self, address: str) -> None:
        content = build_robots_txt(address)
        self._close_open_dialogs()
        self._click_setting_row("AyIhkc", "맞춤 robots.txt")
        dialog = self._wait_dialog("맞춤 robots.txt")
        field = None
        for selector in (
            'textarea[aria-label="맞춤 robots.txt"]',
            'textarea[jsname="YPqjbf"]',
            "textarea",
        ):
            for el in dialog.find_elements(By.CSS_SELECTOR, selector):
                try:
                    if el.is_displayed():
                        field = el
                        break
                except Exception:
                    continue
            if field is not None:
                break
        if field is None:
            raise RuntimeError("맞춤 robots.txt 입력란을 찾지 못했습니다.")
        self._set_text(field, content)
        self._tick()
        self._click_named_button(dialog, "저장", wait_enabled=True)
        self._wait_dialog_closed(dialog)
        self.log("맞춤 robots.txt를 저장했습니다.")

    def enable_homepage_all_tag(self) -> None:
        self._close_open_dialogs()
        self._click_setting_row("ZVRmn", "홈페이지 태그")
        dialog = self._wait_dialog("홈페이지")
        self._enable_aria_checkbox("all", scope=dialog)
        self._click_named_button(dialog, "저장", wait_enabled=True)
        self._wait_dialog_closed(dialog)
        self.log("홈페이지 태그 all을 켜고 저장했습니다.")

    def _enable_aria_checkbox(self, aria_label: str, scope=None) -> None:
        if scope is None:
            self._close_open_dialogs()
        selector = f'[aria-label="{aria_label}"][role="checkbox"]'
        root = scope if scope is not None else self.driver
        box = self._wait(10).until(
            lambda d: _displayed(root.find_elements(By.CSS_SELECTOR, selector))
        )
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", box)
        self._tick()
        checked = (box.get_attribute("aria-checked") or "").lower() == "true"
        if checked:
            self.log(f"{aria_label}은(는) 이미 켜져 있습니다.")
            return
        try:
            box.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", box)
        self._wait(6).until(
            lambda d: (
                (_displayed(root.find_elements(By.CSS_SELECTOR, selector))
                 or box).get_attribute("aria-checked")
                or ""
            ).lower()
            == "true"
        )
        self.log(f"{aria_label}을(를) 켰습니다.")

    def _wait_setting_unlocked(self, controller: str, timeout: float = 10) -> None:
        def unlocked(driver):
            els = driver.find_elements(By.CSS_SELECTOR, f'[jscontroller="{controller}"]')
            if not els:
                return False
            return (els[0].get_attribute("data-is-disable-dialog") or "").lower() != "true"

        self._wait(timeout).until(unlocked)
        self._tick()

    def _current_settings_blog_id(self) -> str:
        match = re.search(r"/blog/settings/(\d{10,})", self.driver.current_url or "")
        return match.group(1) if match else ""

    def _find_setting_row(self, controller: str, label: str):
        el = self._find_first([f'[jscontroller="{controller}"]'])
        if el is not None:
            return el
        return self.driver.execute_script(
            """
            const label = arguments[0];
            const rows = [...document.querySelectorAll('.cI5zJb')];
            return rows.find((row) => {
              const first = row.querySelector('.EDnCLe');
              return first && first.textContent.trim() === label;
            }) || null;
            """,
            label,
        )

    def _click_setting_row(self, controller: str, label: str) -> None:
        el = self._find_setting_row(controller, label)
        if el is None:
            raise RuntimeError(f"설정 항목을 찾지 못했습니다: {label}")
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
        self._tick()
        try:
            el.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", el)

    def _visible_dialog(self):
        for dialog in self.driver.find_elements(By.CSS_SELECTOR, '[role="dialog"]'):
            try:
                if dialog.is_displayed():
                    return dialog
            except Exception:
                continue
        return None

    def _wait_dialog(self, title_hint: str | None = None, timeout: float = 15):
        def found(driver):
            for dialog in driver.find_elements(By.CSS_SELECTOR, '[role="dialog"]'):
                try:
                    if not dialog.is_displayed():
                        continue
                    if title_hint and title_hint not in (dialog.text or ""):
                        continue
                    return dialog
                except Exception:
                    continue
            return False

        return self._wait(timeout).until(found)

    def _wait_dialog_closed(self, dialog, timeout: float = 6) -> None:
        try:
            self._wait(timeout).until(EC.staleness_of(dialog))
        except Exception:
            try:
                self._wait(2).until(lambda d: not dialog.is_displayed())
            except Exception:
                pass
        self._tick()

    def _close_open_dialogs(self) -> None:
        dialog = self._visible_dialog()
        if dialog is None:
            return
        try:
            self._click_named_button(dialog, "취소", wait_enabled=False)
            self._wait_dialog_closed(dialog)
        except Exception:
            try:
                self.driver.find_element(By.TAG_NAME, "body").send_keys(Keys.ESCAPE)
            except Exception:
                pass
            self._tick()

    def _fill_visible_dialog(self, text: str, title_hint: str | None = None) -> None:
        dialog = self._wait_dialog(title_hint)
        field = None
        for selector in (
            "textarea",
            'input[type="text"]',
            'input:not([type="hidden"]):not([type="file"])',
            '[contenteditable="true"]',
        ):
            for el in dialog.find_elements(By.CSS_SELECTOR, selector):
                try:
                    if el.is_displayed():
                        field = el
                        break
                except Exception:
                    continue
            if field is not None:
                break
        if field is None:
            raise RuntimeError("설정 입력란을 찾지 못했습니다.")
        self._set_text(field, text)
        self._tick()
        self._click_named_button(dialog, "저장", wait_enabled=True)
        self._wait_dialog_closed(dialog)

    def _click_save(self, dialog=None) -> None:
        scope = dialog or self._visible_dialog()
        try:
            self._click_named_button(scope, "저장", wait_enabled=True)
            return
        except Exception:
            pass
        button = self._wait(8).until(
            lambda d: _displayed(
                d.find_elements(By.CSS_SELECTOR, '[role="button"][data-id="ktSouf"]')
            )
        )
        if (button.get_attribute("aria-disabled") or "").lower() == "true":
            self._wait(6).until(
                lambda d: (
                    (_displayed(d.find_elements(By.CSS_SELECTOR, '[role="button"][data-id="ktSouf"]'))
                     or button).get_attribute("aria-disabled")
                    or ""
                ).lower()
                != "true"
            )
            button = _displayed(
                self.driver.find_elements(By.CSS_SELECTOR, '[role="button"][data-id="ktSouf"]')
            ) or button
        try:
            button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", button)

    def _click_named_button(self, root, name: str, wait_enabled: bool = False):
        def match(driver):
            scope = root if root is not None else driver
            try:
                buttons = scope.find_elements(By.CSS_SELECTOR, '[role="button"]')
            except Exception:
                return False
            for button in buttons:
                try:
                    if name not in (button.text or ""):
                        continue
                    disabled = (button.get_attribute("aria-disabled") or "").lower()
                    if wait_enabled and disabled == "true":
                        continue
                    if button.is_displayed():
                        return button
                except Exception:
                    continue
            return False

        button = self._wait(8).until(match)
        try:
            button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", button)

    def _find_first(self, selectors: list[str]):
        driver = self.driver
        for selector in selectors:
            try:
                short = WebDriverWait(driver, 0.5, poll_frequency=0.05)
                return short.until(EC.presence_of_element_located((By.CSS_SELECTOR, selector)))
            except Exception:
                continue
        return None

    def _set_text(self, element, text: str) -> None:
        try:
            element.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", element)
        try:
            element.send_keys(Keys.CONTROL, "a")
            element.send_keys(text)
            return
        except Exception:
            pass
        self.driver.execute_script(
            """
            const el = arguments[0];
            const value = arguments[1];
            el.focus();
            if ('value' in el) {
              el.value = value;
              el.dispatchEvent(new Event('input', {bubbles: true}));
              el.dispatchEvent(new Event('change', {bubbles: true}));
            } else {
              el.innerText = value;
              el.dispatchEvent(new Event('input', {bubbles: true}));
            }
            """,
            element,
            text,
        )

    def _wait(self, timeout: float = 8):
        return WebDriverWait(self.driver, timeout, poll_frequency=0.08)

    def _tick(self, seconds: float = 0.0) -> None:
        self.control.checkpoint()
        if seconds:
            time.sleep(seconds)

    def _mark_done(self, blog_id: str, key: str) -> None:
        for blog in self.state.blogs:
            if blog.id == blog_id:
                blog.done.add(key)
                break
        if self._on_item_done:
            self._on_item_done(blog_id, key)

    def _report(self, step: int, total: int, label: str) -> None:
        self.control.checkpoint()
        if self._on_progress:
            self._on_progress(step, total, label)
        self.log(f"[{step}/{total}] {label}")

    def close(self) -> None:
        with self._lock:
            driver = self.driver
            self.driver = None
            self.state = SessionState()
            proc = self._chrome_proc
            self._chrome_proc = None
            self._chrome_user_dir = None
        if driver is not None:
            try:
                driver.quit()
            except Exception:
                pass
        if proc is not None:
            try:
                proc.terminate()
                proc.wait(timeout=3)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        self.log("브라우저를 종료했습니다. Chrome 프로필은 유지됩니다.")
