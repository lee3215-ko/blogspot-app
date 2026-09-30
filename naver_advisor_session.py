"""네이버 서치어드바이저 세션: 로그인 유지, 사이트 수, 소유확인·수집."""
from __future__ import annotations

import os
import re
import subprocess
import threading
import time
import urllib.request
from dataclasses import dataclass, field
from urllib.parse import quote

from selenium import webdriver
from selenium.common.exceptions import (
    NoAlertPresentException,
    UnexpectedAlertPresentException,
    WebDriverException,
)
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager

from blogger_session import RunControl, StopRequested, _find_chrome, _wait_debug_port
from paths import get_data_dir

BOARD = "https://searchadvisor.naver.com/console/board"
NAVER_DEBUG_PORT = 9336
UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

NAVER_ITEMS = (
    ("naver_verify", "소유확인"),
    ("theme_head", "테마헤더"),
    ("crawl_fast", "수집주기"),
    ("naver_robots", "로봇수집"),
    ("sitemap", "사이트맵"),
    ("collect", "블로그수집"),
    ("collect_post", "글수집"),
)

_COUNT_JS = """
return (function() {
  const body = document.body?.innerText || "";
  const patterns = [
    /등록(?:된)?\\s*사이트\\s*[:：]?\\s*(\\d{1,3})/i,
    /사이트\\s*수\\s*[:：]?\\s*(\\d{1,3})/i,
    /(\\d{1,3})\\s*\\/\\s*100\\b/,
    /총\\s*(\\d{1,3})\\s*(?:개|건)/,
    /전체\\s*(\\d{1,3})\\s*(?:개|건)/,
  ];
  for (const re of patterns) {
    const m = body.match(re);
    if (m) {
      const n = parseInt(m[1], 10);
      if (Number.isFinite(n) && n >= 0 && n <= 100) return {n, how: "label"};
    }
  }
  const normHostPath = (raw) => {
    try {
      const u = new URL(String(raw || "").trim());
      if (!/^https?:$/i.test(u.protocol)) return "";
      if (/(^|\\.)naver\\.com$/i.test(u.hostname)) return "";
      if (/(^|\\.)naver\\.me$/i.test(u.hostname)) return "";
      return (u.hostname + u.pathname).replace(/\\/$/, "").toLowerCase();
    } catch { return ""; }
  };
  const urls = new Set();
  const add = (raw) => { const key = normHostPath(raw); if (key) urls.add(key); };
  const rowSel = 'table tbody tr, .v-data-table tbody tr, [class*="site-list"] li, [class*="SiteList"] li, .v-list-item';
  for (const tr of document.querySelectorAll(rowSel)) {
    const text = (tr.innerText || "").trim();
    for (const a of tr.querySelectorAll("a[href]")) {
      add(a.getAttribute("href"));
      add(a.textContent);
    }
    const m = text.match(/https?:\\/\\/[^\\s<>"']+/i);
    if (m) add(m[0]);
  }
  if (urls.size) return {n: urls.size, how: "table"};
  for (const a of document.querySelectorAll("main a[href], .v-main a[href], [class*=\\"content\\"] a[href], a[href]")) {
    add(a.getAttribute("href"));
    add(a.textContent);
  }
  return {n: urls.size, how: "links"};
})();
"""

_META_JS = """
return (function() {
  const decode = (s) => String(s || "")
    .replace(/\\u00a0/g, " ")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'")
    .trim();
  const box = document.querySelector(".url_g6MTW, [class*='url_g6MTW']");
  if (box) {
    const t = decode(box.innerText || box.textContent || "");
    const m = t.match(/content=["']([a-zA-Z0-9_-]{16,})["']/i) || t.match(/([a-f0-9]{20,})/i);
    if (m && m[1]) return {value: m[1], how: "url_g6MTW", raw: t};
  }
  const el = document.querySelector('meta[name="naver-site-verification"]');
  if (el) {
    const c = el.getAttribute("content") || "";
    if (c.length >= 16) return {value: c, how: "DOM"};
  }
  const nodes = [...document.querySelectorAll('code, pre, textarea, input[type="text"], input[readonly], .v-text-field input')];
  for (const node of nodes) {
    const t = (node.value || node.textContent || node.innerText || "").trim();
    if (!t) continue;
    const m = t.match(/naver-site-verification["'\\s][^>]{0,80}content=["']([a-zA-Z0-9_-]{16,})["']/i)
      || t.match(/content=["']([a-zA-Z0-9_-]{16,})["'][^>]{0,80}naver-site-verification/i)
      || t.match(/name=["']naver-site-verification["'][^>]*content=["']([a-zA-Z0-9_-]{16,})["']/i);
    if (m && m[1]) return {value: m[1], how: "BOX"};
    if (/^[a-f0-9]{20,}$/i.test(t)) return {value: t, how: "HEX"};
  }
  const fullText = (document.body?.innerText || "") + "\\n" + (document.body?.textContent || "");
  let m = fullText.match(/<meta[^>]*name=["']naver-site-verification["'][^>]*content=["']([^"']+)["']/i)
    || fullText.match(/<meta[^>]*content=["']([^"']+)["'][^>]*name=["']naver-site-verification["']/i);
  if (m && m[1] && m[1].length >= 16) return {value: m[1], how: "TEXT"};
  const idx = fullText.indexOf("naver-site-verification");
  if (idx !== -1) {
    const snippet = fullText.substring(Math.max(0, idx - 120), idx + 400);
    m = snippet.match(/content=["']([a-zA-Z0-9_-]{16,})["']/i) || snippet.match(/([a-f0-9]{20,})/i);
    if (m && m[1]) return {value: m[1], how: "SNIPPET"};
  }
  return {value: "", how: ""};
})();
"""


def normalize_site_url(raw: str) -> str:
    text = (raw or "").strip()
    if not text:
        return ""
    if not re.match(r"^https?://", text, re.I):
        text = "https://" + text
    try:
        from urllib.parse import urlparse, urlunparse

        parsed = urlparse(text)
        path = parsed.path.rstrip("/")
        return urlunparse((parsed.scheme, parsed.netloc, path, "", "", ""))
    except Exception:
        return text.rstrip("/")


def to_board_host_url(site_url: str) -> str:
    text = normalize_site_url(site_url)
    try:
        from urllib.parse import urlparse

        parsed = urlparse(text)
        return f"{parsed.scheme}://{parsed.netloc}"
    except Exception:
        return text


def site_host_key(site_url: str) -> str:
    text = to_board_host_url(site_url)
    return re.sub(r"^https?://", "", text, flags=re.I).replace("www.", "").lower()


def build_verify_url(site_url: str) -> str:
    return f"https://searchadvisor.naver.com/console/verify?site={quote(normalize_site_url(site_url), safe='')}"


def build_meta_tag(content: str) -> str:
    return f'<meta name="naver-site-verification" content="{content}"/>'


def _debug_port_open(port: int) -> bool:
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{port}/json/version", timeout=0.4) as resp:
            return resp.status == 200
    except Exception:
        return False


_ACCOUNT_JS = """
return (function() {
  const pick = (s) => String(s || "").trim();
  const skip = /사이트|로그인|로그아웃|검색|네이버|서치|어드바이저|등록|도움말|설정|콘솔|홈|내정보|프로필|layout_|sitecheck|site_check/;
  const looksId = (s) => /^[a-zA-Z][a-zA-Z0-9._-]{2,39}$/.test(s);

  const fromObj = (obj, depth) => {
    if (!obj || depth > 4) return "";
    if (typeof obj === "string" && looksId(obj) && !skip.test(obj)) return obj;
    if (typeof obj !== "object") return "";
    for (const key of ["loginId", "userId", "naverId", "user_id", "nclick_id", "id"]) {
      const v = pick(obj[key]);
      if (looksId(v) && !skip.test(v)) return v;
    }
    for (const v of Object.values(obj)) {
      const hit = fromObj(v, depth + 1);
      if (hit) return hit;
    }
    return "";
  };

  const stateHit = fromObj(window.__NUXT__ || window.__INITIAL_STATE__ || window.__APP_STATE__ || {}, 0);
  if (stateHit) return {id: stateHit, how: "state"};

  const dump = JSON.stringify(window.__NUXT__ || window.__INITIAL_STATE__ || {});
  const sm = dump.match(/"(?:loginId|userId|naverId|user_id)"\\s*:\\s*"([a-zA-Z][a-zA-Z0-9._-]{2,39})"/);
  if (sm && !skip.test(sm[1])) return {id: sm[1], how: "json"};

  for (const el of document.querySelectorAll("[data-user-id], [data-userid], [data-login-id], [data-account]")) {
    const v = pick(el.getAttribute("data-user-id") || el.getAttribute("data-userid") || el.getAttribute("data-login-id") || el.getAttribute("data-account"));
    if (looksId(v) && !skip.test(v)) return {id: v, how: "attr"};
  }

  const nodes = document.querySelectorAll("header *, .v-app-bar *, .v-toolbar *, nav *, [class*='user'] *, [class*='profile'] *");
  for (const el of nodes) {
    const r = el.getBoundingClientRect();
    if (r.top > 90 || r.width < 8) continue;
    const t = pick(el.textContent);
    if (looksId(t) && !skip.test(t) && t.length <= 24) return {id: t, how: "header"};
  }
  return {id: "", how: ""};
})();
"""


class OwnershipPending(RuntimeError):
    """사이트 목록에 소유확인 진행 링크가 남아 있음."""


@dataclass
class NaverState:
    logged_in: bool = False
    account: str = ""
    site_count: int | None = None
    url: str = ""
    error: str = ""
    done: set[str] = field(default_factory=set)


class NaverAdvisorSession:
    def __init__(self, log):
        self.log = log
        self.driver: webdriver.Chrome | None = None
        self.state = NaverState()
        self._lock = threading.Lock()
        self.control = RunControl()
        self._on_progress = None
        self._on_item_done = None
        self._chrome_proc: subprocess.Popen | None = None
        self._owns_chrome = False

    def profile_dir(self) -> str:
        path = os.path.join(get_data_dir(), "chrome-naver-session")
        os.makedirs(path, exist_ok=True)
        return path

    def chrome_running(self) -> bool:
        return _debug_port_open(NAVER_DEBUG_PORT)

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

    def reattach(self) -> bool:
        if self.is_alive():
            if self._on_advisor_console():
                self.state.logged_in = True
                self.read_account()
            return True
        if not self.chrome_running():
            return False
        try:
            options = Options()
            options.add_experimental_option("debuggerAddress", f"127.0.0.1:{NAVER_DEBUG_PORT}")
            service = Service(ChromeDriverManager().install())
            self.driver = webdriver.Chrome(service=service, options=options)
            if self._on_advisor_console():
                self.state.logged_in = True
                self.state.error = ""
                self.read_account()
                self.log("서치어드바이저 Chrome에 다시 연결했습니다. 로그인 유지.")
            else:
                self.log("서치어드바이저 Chrome에 다시 연결했습니다.")
            return True
        except Exception as exc:
            self.log(f"서치어드바이저 재연결 실패: {exc}")
            self.driver = None
            return False

    def start_login(self) -> None:
        with self._lock:
            if self.driver is not None and self.is_alive():
                self.log("이미 열려 있는 서치어드바이저 창을 앞으로 가져옵니다.")
                try:
                    self.driver.switch_to.window(self.driver.current_window_handle)
                    self._goto_board()
                except Exception:
                    pass
                return

            chrome = _find_chrome()
            profile = self.profile_dir()
            if _debug_port_open(NAVER_DEBUG_PORT):
                self.log("기존 서치어드바이저 Chrome에 다시 연결합니다.")
                self._owns_chrome = False
            else:
                self.log("서치어드바이저 Chrome 창을 여는 중...")
                cmd = [
                    chrome,
                    f"--remote-debugging-port={NAVER_DEBUG_PORT}",
                    f"--user-data-dir={profile}",
                    "--no-first-run",
                    "--no-default-browser-check",
                    "--disable-popup-blocking",
                    "--disable-blink-features=AutomationControlled",
                    "--window-size=1400,900",
                    BOARD,
                ]
                self._chrome_proc = subprocess.Popen(cmd)
                self._owns_chrome = True
                _wait_debug_port(NAVER_DEBUG_PORT, timeout=20)

            options = Options()
            options.add_experimental_option("debuggerAddress", f"127.0.0.1:{NAVER_DEBUG_PORT}")
            service = Service(ChromeDriverManager().install())
            driver = webdriver.Chrome(service=service, options=options)
            try:
                driver.execute_cdp_cmd(
                    "Page.addScriptToEvaluateOnNewDocument",
                    {"source": "Object.defineProperty(navigator, 'webdriver', {get: () => undefined});"},
                )
            except Exception:
                pass
            self.driver = driver
            self.state = NaverState()

        if not self._on_advisor_console():
            self._goto_board()
        self.log("서치어드바이저 창에 연결했습니다. 직접 로그인해 주세요.")

    def wait_until_logged_in(self, poll_sec: float = 1.0, timeout: float | None = None) -> NaverState:
        started = time.time()
        while self.is_alive():
            if self._on_advisor_console():
                self.state.logged_in = True
                self.state.error = ""
                self._accept_alerts()
                try:
                    self._accept_consent()
                except Exception:
                    pass
                count = self.count_sites()
                self.read_account()
                account = self.state.account or "-"
                if count is not None:
                    self.log(f"서치어드바이저 로그인 확인. 아이디 {account} · 등록 사이트 {count}개")
                else:
                    self.log(f"서치어드바이저 로그인 확인. 아이디 {account}")
                return self.state
            if timeout is not None and time.time() - started >= timeout:
                break
            time.sleep(poll_sec)
        return self.state

    def count_sites(self, force_reload: bool = False) -> int | None:
        if not self.is_alive():
            return self.state.site_count
        try:
            url = self._url()
            if "/auth/" in url:
                self._goto_board()
            on_board = "/console/board" in url
            if not on_board or force_reload:
                self._goto_board()
            else:
                try:
                    self.driver.refresh()
                except Exception:
                    self._goto_board()
            self._tick(1.2)
            self._accept_consent()
            count = 0
            how = ""
            deadline = time.time() + 12
            while time.time() < deadline:
                got = self.driver.execute_script(_COUNT_JS) or {}
                count = int(got.get("n") or 0)
                how = str(got.get("how") or "")
                if how in {"label", "table"} or count > 0:
                    break
                time.sleep(0.5)
            self.state.site_count = count
            self.state.logged_in = True
            self.state.url = self._url()
            self.read_account()
            self.log(f"등록 사이트 {count}개 ({how or 'unknown'})")
            return count
        except Exception as exc:
            self.log(f"사이트 수 인식 실패: {exc}")
            return self.state.site_count

    def read_account(self) -> str:
        if not self.is_alive():
            return self.state.account
        account = ""
        how = ""
        try:
            got = self.driver.execute_script(_ACCOUNT_JS) or {}
            account = str(got.get("id") or "").strip()
            how = str(got.get("how") or "")
        except Exception:
            account = ""
        if not account:
            try:
                for cookie in self.driver.get_cookies() or []:
                    name = str(cookie.get("name") or "")
                    value = str(cookie.get("value") or "").strip()
                    if name.lower() in {"nid_inf", "nloginid", "naverid"} and 3 <= len(value) <= 40:
                        if re.match(r"^[a-zA-Z][a-zA-Z0-9._-]+$", value):
                            account, how = value, "cookie"
                            break
            except Exception:
                pass
        prev = self.state.account
        if account:
            self.state.account = account
            if account != prev:
                extra = f" ({how})" if how else ""
                self.log(f"서치어드바이저 아이디: {account}{extra}")
        return self.state.account

    def _require_login(self, site_url: str) -> str:
        site = normalize_site_url(site_url)
        if not site:
            raise RuntimeError("블로그 주소가 없습니다. 먼저 블로그스팟 설정을 적용해 주세요.")
        if not self.is_alive() and not self.reattach():
            raise RuntimeError("서치어드바이저에 먼저 로그인해 주세요.")
        if not self._on_advisor_console():
            raise RuntimeError("서치어드바이저에 먼저 로그인해 주세요.")
        self.read_account()
        return site

    def insert_verify_html(
        self,
        site_url: str,
        inject_theme,
        blog_id: str = "",
        control: RunControl | None = None,
        on_progress=None,
        on_item_done=None,
    ) -> dict:
        self.control = control or RunControl()
        self._on_progress = on_progress
        self._on_item_done = on_item_done
        site = self._require_login(site_url)
        total = 2
        self._report(1, total, "소유확인 HTML 복사")
        meta = self.register_and_get_meta(site)
        self._report(2, total, "테마 HTML 저장")
        if inject_theme is None:
            raise RuntimeError("테마 삽입 함수가 없습니다.")
        inject_theme(meta["tag"])
        self.log("HTML 코드를 테마에 넣었습니다. 소유확인은 사이트 목록에서 직접 진행해 주세요.")
        if blog_id:
            self._mark_done(blog_id, "theme_head")
        self.cancel_verify()
        self._goto_board()
        return {"site": site, "meta": meta}

    def apply_first_collect(
        self,
        site_url: str,
        blog_id: str = "",
        post_urls: list[str] | None = None,
        control: RunControl | None = None,
        on_progress=None,
        on_item_done=None,
    ) -> dict:
        self.control = control or RunControl()
        self._on_progress = on_progress
        self._on_item_done = on_item_done
        site = self._require_login(site_url)
        posts = [str(url).strip() for url in (post_urls or []) if str(url).strip()]

        total = 5 + len(posts) if posts else 5
        self._report(1, total, "사이트 목록 확인")
        status = self.check_site_ownership(site)
        if not status.get("found"):
            raise RuntimeError("사이트 목록에서 블로그를 찾지 못했습니다. 먼저 HTML 코드를 넣어 주세요.")
        if status.get("pending"):
            raise OwnershipPending("소유확인을 진행 해주세요. 사이트 목록에 '소유확인 진행' 링크가 있습니다.")
        self.log("소유확인이 완료된 것을 확인했습니다. 대시보드에서 수집을 진행합니다.")
        if blog_id:
            self._mark_done(blog_id, "naver_verify")

        self._report(2, total, "수집주기 빠르게")
        if self.select_fast_crawl(site) and blog_id:
            self._mark_done(blog_id, "crawl_fast")

        self._report(3, total, "robots.txt 수집")
        robots = self.request_robots(site)
        if robots.get("ok") and blog_id:
            self._mark_done(blog_id, "naver_robots")

        self._report(4, total, "sitemap.xml 제출")
        sitemap_url = f"{site.rstrip('/')}/sitemap.xml"
        sm = self.submit_text_request(self._sitemap_page(site), sitemap_url)
        if sm.get("ok") and blog_id:
            self._mark_done(blog_id, "sitemap")
        elif not sm.get("ok"):
            self.log(f"사이트맵 제출 실패: {sm.get('reason') or 'unknown'}")

        self._report(5, total, "블로그 주소 수집")
        crawl = self.request_blog_crawl(site)
        if crawl.get("ok") and blog_id:
            self._mark_done(blog_id, "collect")

        posts_result = None
        if posts:
            self._report(6, total, f"글페이지 수집 {len(posts)}개")
            posts_result = self.request_post_crawls(
                site,
                posts,
                blog_id=blog_id,
                progress_base=5,
                progress_total=total,
            )
        else:
            self.log("인식된 글이 없어 블로그 주소만 수집 요청했습니다.")

        self._goto_board()
        try:
            self.count_sites(force_reload=True)
        except Exception:
            pass
        return {"site": site, "robots": robots, "sitemap": sm, "crawl": crawl, "posts": posts_result}

    def check_site_ownership(self, site_url: str) -> dict:
        site = normalize_site_url(site_url)
        host = site_host_key(site)
        if "/console/board" not in self._url():
            self._goto_board()
        self._wait_site_board()
        self._accept_alerts()
        status = self._inspect_site_row(host)
        if not status.get("found"):
            if not self._type_site_search(site):
                raise RuntimeError("사이트 목록 검색창을 찾지 못했습니다.")
            self._tick(0.4)
            try:
                self.driver.switch_to.active_element.send_keys(Keys.ENTER)
            except Exception:
                pass
            status = {"found": False, "pending": False, "text": ""}
            for _ in range(10):
                self.control.checkpoint()
                status = self._inspect_site_row(host)
                if status.get("found"):
                    break
                time.sleep(0.5)
        if status.get("found"):
            extra = "소유확인 진행 링크 있음" if status.get("pending") else "소유확인 완료"
            self.log(f"사이트 목록 확인: {host} · {extra}")
        else:
            self.log(f"사이트 목록에서 찾지 못함: {host}")
        return status

    def _wait_site_board(self) -> None:
        deadline = time.time() + 15
        while time.time() < deadline:
            self.control.checkpoint()
            ready = self.driver.execute_script(
                """
                if (document.querySelector("tbody tr")) return true;
                return !!document.querySelector('input[type="text"], input[type="search"]');
                """
            )
            if ready:
                return
            time.sleep(0.4)

    def _find_site_search(self):
        return self.driver.execute_script(
            """
            const inputs = Array.from(document.querySelectorAll('input[type="text"], input[type="search"], input:not([type])'));
            for (const input of inputs) {
              const id = input.id || "";
              const lab = id ? document.querySelector('label[for="' + id + '"]') : null;
              const slot = input.closest(".v-text-field__slot, .v-input, label") || input.parentElement;
              const meta = [
                lab ? lab.textContent : "",
                input.placeholder || "",
                input.getAttribute("aria-label") || "",
                slot ? slot.innerText : "",
              ].join(" ");
              if (/URL을 입력|example\\.com/.test(meta)) continue;
              const r = input.getBoundingClientRect();
              if (r.width < 40 || r.height < 10) continue;
              if (/검색/.test(meta)) return input;
            }
            return null;
            """
        )

    def _type_site_search(self, site_url: str) -> bool:
        value = to_board_host_url(site_url)
        element = None
        deadline = time.time() + 12
        while time.time() < deadline and element is None:
            self.control.checkpoint()
            element = self._find_site_search()
            if element is None:
                time.sleep(0.4)
        if element is None:
            return False
        ok = self.driver.execute_script(
            """
            const el = arguments[0];
            const value = arguments[1];
            el.focus();
            el.click();
            const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value")?.set;
            if (setter) setter.call(el, value);
            else el.value = value;
            el.dispatchEvent(new Event("input", {bubbles: true}));
            el.dispatchEvent(new Event("change", {bubbles: true}));
            return (el.value || "") === value;
            """,
            element,
            value,
        )
        if ok:
            self.log(f"사이트 목록 검색: {value}")
        return bool(ok)

    def _inspect_site_row(self, host: str) -> dict:
        got = self.driver.execute_script(
            """
            const host = String(arguments[0] || "").toLowerCase();
            const rows = Array.from(document.querySelectorAll('tbody tr, table tr, .v-data-table tbody tr'));
            for (const row of rows) {
              const text = (row.innerText || row.textContent || "").replace(/\\s+/g, " ").trim();
              if (!host || !text.toLowerCase().includes(host)) continue;
              let pending = false;
              for (const el of row.querySelectorAll('a, button, span, [role="button"]')) {
                const t = (el.textContent || "").replace(/\\s+/g, " ").trim();
                if (/소유확인\\s*진행/.test(t)) { pending = true; break; }
              }
              return {found: true, pending: pending, text: text.slice(0, 220)};
            }
            return {found: false, pending: false, text: ""};
            """,
            host,
        ) or {}
        return {
            "found": bool(got.get("found")),
            "pending": bool(got.get("pending")),
            "text": str(got.get("text") or ""),
        }

    def request_blog_crawl(self, site_url: str, blog_id: str = "") -> dict:
        site = normalize_site_url(site_url)
        crawl_url = site if site.endswith("/") else site + "/"
        self.log(f"블로그 수집요청: {crawl_url}")
        crawl = self.submit_text_request(self._crawl_page(site), crawl_url)
        if crawl.get("ok") and blog_id:
            self._mark_done(blog_id, "collect")
        elif not crawl.get("ok"):
            self.log(f"블로그 수집요청 실패: {crawl.get('reason') or 'unknown'}")
        return crawl

    def request_post_crawls(
        self,
        site_url: str,
        post_urls: list[str],
        blog_id: str = "",
        progress_base: int = 0,
        progress_total: int | None = None,
    ) -> dict:
        site = normalize_site_url(site_url)
        urls = []
        seen = set()
        for raw in post_urls or []:
            url = str(raw or "").strip()
            if not url or url in seen:
                continue
            seen.add(url)
            urls.append(url)
        if not urls:
            raise RuntimeError("수집할 글 주소가 없습니다. 먼저 글 목록을 인식해 주세요.")
        ok = 0
        fail = 0
        done_urls: list[str] = []
        total = len(urls)
        grand = progress_total or (progress_base + total)
        for index, url in enumerate(urls, start=1):
            self._report(progress_base + index, grand, f"글페이지 수집 {index}/{total}")
            self.log(f"글페이지 수집요청: {url}")
            result = self.submit_text_request(self._crawl_page(site), url)
            if result.get("ok"):
                ok += 1
                done_urls.append(url)
            else:
                fail += 1
                self.log(f"글페이지 수집 실패: {result.get('reason') or 'unknown'}")
        if ok and blog_id:
            self._mark_done(blog_id, "collect_post")
        return {"ok": ok > 0, "success": ok, "fail": fail, "urls": done_urls}

    def _sitemap_page(self, site: str) -> str:
        return f"https://searchadvisor.naver.com/console/site/request/sitemap?site={quote(site, safe='')}"

    def _crawl_page(self, site: str) -> str:
        return f"https://searchadvisor.naver.com/console/site/request/crawl?site={quote(site, safe='')}"

    def cancel_verify(self) -> bool:
        clicked = self.driver.execute_script(
            """
            const nodes = document.querySelectorAll('button, a, [role="button"], .v-btn');
            for (const el of nodes) {
              const t = (el.textContent || "").replace(/\\s+/g, " ").trim();
              if (t !== "취소") continue;
              const r = el.getBoundingClientRect();
              if (r.width < 20 || r.height < 10) continue;
              if (el.disabled || el.getAttribute("aria-disabled") === "true") continue;
              el.scrollIntoView({block: "center"});
              el.click();
              return true;
            }
            return false;
            """
        )
        if clicked:
            self.log("서치어드바이저에서 취소를 눌렀습니다.")
            self._tick(0.6)
            self._accept_alerts()
            return True
        self.log("취소 버튼을 찾지 못했습니다.")
        return False

    def register_and_get_meta(self, site_url: str) -> dict:
        site = normalize_site_url(site_url)
        host = site_host_key(site)
        self._goto_board()
        self._tick(1.2)
        self._accept_alerts()
        if not self._wait_board_url_input(20):
            self.log("보드 입력창이 없어 소유확인 페이지로 바로 이동합니다.")
            self._open_verify(site)
        else:
            self._type_board_url(site)
            self._tick(0.3)
            self.driver.switch_to.active_element.send_keys(Keys.ENTER)
            self._tick(1.2)
            self._accept_alerts()
            if not self._on_verify_screen(site):
                if self._click_ownership_row(host):
                    self._tick(1.5)
                if not self._on_verify_screen(site):
                    self._open_verify(site)
        if not self._on_verify_screen(site):
            raise RuntimeError(f"소유확인 화면에 들어가지 못했습니다: {self._url()}")

        self._select_html_tag()
        got = self._get_meta_box()
        content = str(got.get("content") or "").strip()
        if not content:
            raise RuntimeError("소유확인 HTML 태그 코드를 읽지 못했습니다.")
        tag = str(got.get("tag") or "").strip() or build_meta_tag(content)
        self.log(f"소유확인 코드: {tag}")
        return {"content": content, "tag": tag, "site": site}

    def confirm_ownership(self, site_url: str, content: str = "") -> bool:
        site = normalize_site_url(site_url)
        if not self._on_verify_screen(site):
            self._open_verify(site)
        self._select_html_tag()
        self._tick(0.8)
        clicked = self.driver.execute_script(
            """
            const keys = ["소유확인", "소유 확인", "확인"];
            for (const el of document.querySelectorAll('button, a, [role="button"], .v-btn')) {
              const t = (el.textContent || "").replace(/\\s+/g, " ").trim();
              if (!keys.some((k) => t.includes(k))) continue;
              if (/취소|닫기|내역/.test(t) && t !== "확인") continue;
              const r = el.getBoundingClientRect();
              if (r.width < 20 || r.height < 10) continue;
              if (el.disabled || el.getAttribute("aria-disabled") === "true") continue;
              el.scrollIntoView({block: "center"});
              el.click();
              return t.slice(0, 30);
            }
            return "";
            """
        )
        if clicked:
            self.log(f"소유확인 클릭: {clicked}")
        else:
            self.log("소유확인 버튼을 찾지 못했습니다. 이미 완료됐을 수 있습니다.")
        self._tick(1.5)
        self._accept_alerts()
        self._click_modal_confirm()
        url = self._url()
        if "/console/site/" in url and "/verify" not in url:
            self.log("소유확인이 완료된 것으로 보입니다.")
            return True
        body = self._body_text()
        if re.search(r"소유\s*확인이\s*완료|사이트\s*소유\s*확인이\s*완료", body):
            self.log("소유확인 완료 문구를 확인했습니다.")
            return True
        if "캡챠" in body or "보안문자" in body:
            self.log("캡챠가 있으면 브라우저에서 직접 풀어 주세요. 잠시 기다립니다.")
            deadline = time.time() + 90
            while time.time() < deadline and self.is_alive():
                self.control.checkpoint()
                if "/console/site/" in self._url() and "/verify" not in self._url():
                    self.log("소유확인이 완료되었습니다.")
                    return True
                time.sleep(2)
        self.log("소유확인은 계속 진행합니다. 필요하면 창에서 직접 확인해 주세요.")
        return False

    def select_fast_crawl(self, site_url: str) -> bool:
        site = normalize_site_url(site_url)
        url = f"https://searchadvisor.naver.com/console/site/option?site={quote(site, safe='')}"
        self.log("수집주기 설정으로 이동...")
        self._safe_get(url)
        self._tick(2.0)
        self._escape_oauth(url)
        clicked = self.driver.execute_script(
            """
            const radio = document.querySelector('input[type="radio"][value="fast"]');
            if (radio) { radio.click(); return "radio[value=fast]"; }
            for (const lbl of document.querySelectorAll("label")) {
              if (/빠르게/.test(lbl.textContent || "")) {
                const inp = lbl.querySelector('input[type="radio"]') || document.getElementById(lbl.getAttribute("for"));
                if (inp) { inp.click(); return "label 빠르게"; }
                lbl.click();
                return "label 빠르게(텍스트)";
              }
            }
            for (const el of document.querySelectorAll('input[type="radio"]')) {
              const wrap = el.closest("label, .v-radio, .v-selection-control, li, div") || el.parentElement;
              if (wrap && /빠르게/.test(wrap.textContent || "")) {
                el.click();
                return "wrap 빠르게";
              }
            }
            return "";
            """
        )
        self._tick(0.8)
        self._drain_alerts()
        if clicked:
            self.log(f"수집주기 빠르게 선택: {clicked}")
            return True
        self.log("수집주기 빠르게를 찾지 못했습니다.")
        return False

    def request_robots(self, site_url: str) -> dict:
        site = normalize_site_url(site_url)
        robots_page = f"https://searchadvisor.naver.com/console/site/check/robots?site={quote(site, safe='')}"
        self.log("robots.txt 수집 요청 페이지로 이동...")
        self._safe_get(robots_page)
        self._tick(1.5)
        self._escape_oauth(robots_page)
        self._accept_alerts()
        if "/check/robots" not in self._url():
            self.driver.execute_script(
                """
                const nodes = document.querySelectorAll('.item_title_DdItX, .submenu_item_DSGA1, .v-list-item__title, .v-list-item, a, button, div');
                for (const el of nodes) {
                  const t = (el.textContent || "").replace(/\\s+/g, " ").trim();
                  if (/^robots\\.txt$/i.test(t)) { el.click(); return true; }
                }
                return false;
                """
            )
            self._tick(0.8)
            self._accept_alerts()
        clicked = self.driver.execute_script(
            """
            const body = document.body?.innerText || "";
            if (/등록되지\\s*않은\\s*사이트|권한이\\s*없/.test(body) && !/robots\\.txt|수집\\s*요청/.test(body)) {
              return {ok: false, reason: "사이트 미등록/권한 없음"};
            }
            const candidates = [];
            for (const btn of document.querySelectorAll('button, a, [role="button"], .v-btn, input[type="button"], input[type="submit"]')) {
              const txt = (btn.textContent || btn.value || "").replace(/\\s+/g, " ").trim();
              if (!/수집\\s*요청/.test(txt)) continue;
              if (/삭제|취소|내역/.test(txt) && !/^수집\\s*요청$/.test(txt)) continue;
              const r = btn.getBoundingClientRect();
              if (r.width < 20 || r.height < 10 || r.bottom < 0 || r.top > innerHeight) continue;
              if (btn.disabled || btn.getAttribute("aria-disabled") === "true" || btn.classList.contains("v-btn--disabled")) continue;
              candidates.push({el: btn, txt, y: r.top, score: r.width});
            }
            candidates.sort((a, b) => b.score - a.score || a.y - b.y);
            if (!candidates.length) return {ok: false, reason: "수집 요청 버튼 없음"};
            candidates[0].el.click();
            return {ok: true, button: candidates[0].txt};
            """
        ) or {"ok": False, "reason": "unknown"}
        self._tick(0.8)
        self._drain_alerts()
        self._click_modal_confirm()
        self._drain_alerts()
        if clicked.get("ok"):
            self.log(f"robots.txt {clicked.get('button') or '수집 요청'} 완료")
        else:
            self.log(f"robots.txt 수집 요청 실패: {clicked.get('reason') or 'unknown'}")
        return clicked

    def submit_text_request(self, form_url: str, value: str) -> dict:
        self._safe_get(form_url)
        self._tick(1.5)
        self._escape_oauth(form_url)
        found = self._wait_form_input(18)
        if not found.get("ok"):
            return {"ok": False, "reason": found.get("reason") or "input 없음", "value": ""}
        submitted = self.driver.execute_script(
            """
            const targetUrl = arguments[0];
            const inputs = Array.from(document.querySelectorAll('input[type="text"], input[type="url"], input:not([type]), textarea'));
            let input = null;
            let best = -1;
            for (const el of inputs) {
              const r = el.getBoundingClientRect();
              if (r.width < 60 || r.height < 10) continue;
              if (el.disabled || el.readOnly) continue;
              const meta = `${el.id || ""} ${el.placeholder || ""} ${el.className || ""}`;
              let score = r.width;
              if (/url|사이트|주소|http|sitemap|수집|요청/i.test(meta)) score += 800;
              if (score > best) { best = score; input = el; }
            }
            if (!input) return {ok: false, reason: "input 없음"};
            const setter = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, "value")?.set
              || Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, "value")?.set;
            input.focus();
            input.click();
            if (setter) setter.call(input, targetUrl);
            else input.value = targetUrl;
            input.dispatchEvent(new Event("input", {bubbles: true}));
            input.dispatchEvent(new Event("change", {bubbles: true}));
            let node = input;
            let site = null;
            while (node) {
              const vm = node.__vue__;
              if (vm && vm.$options && vm.$options.name === "SiteBaseInput" && typeof vm.clickConfirm === "function") {
                site = vm;
                break;
              }
              node = node.parentElement;
            }
            if (site) {
              site.value = targetUrl;
              site.clickConfirm();
              return {ok: true, button: "확인", vue: true, value: site.value || input.value};
            }
            for (const btn of document.querySelectorAll('button, a, [role="button"], input[type="button"], input[type="submit"]')) {
              const txt = (btn.textContent || btn.value || "").replace(/\\s+/g, " ").trim();
              if (/^(확인|제출|등록|추가|요청|수집\\s*요청|재수집)$/.test(txt)) {
                const r = btn.getBoundingClientRect();
                if (r.width > 0 && r.height > 0) {
                  btn.click();
                  return {ok: true, button: txt, value: input.value};
                }
              }
            }
            return {ok: false, reason: "확인 버튼 없음", value: input.value};
            """,
            value,
        ) or {"ok": False, "reason": "unknown"}
        self._tick(1.2)
        if submitted.get("vue"):
            alert = self.driver.execute_script(
                """
                const inputs = Array.from(document.querySelectorAll('input[type="text"], input[type="url"], textarea'));
                for (const input of inputs) {
                  let node = input;
                  while (node) {
                    const vm = node.__vue__;
                    if (vm && vm.$options && vm.$options.name === "SiteBaseInput") {
                      if (vm.showAlert && vm.alertMessageText) return String(vm.alertMessageText);
                      return "";
                    }
                    node = node.parentElement;
                  }
                }
                return "";
                """
            ) or ""
            if alert:
                submitted = {"ok": False, "reason": str(alert), "value": value}
        self._drain_alerts()
        self._click_modal_confirm()
        self._drain_alerts()
        if submitted.get("ok"):
            self.log(f"제출 완료: {submitted.get('button')} → {value}")
        return submitted

    def _open_verify(self, site_url: str) -> None:
        self._safe_get(build_verify_url(site_url))
        self._tick(2.0)
        self._escape_oauth(build_verify_url(site_url))

    def _on_verify_screen(self, site_url: str = "") -> bool:
        url = self._url()
        if re.search(r"/console/verify", url):
            if site_url:
                host = site_host_key(site_url)
                from urllib.parse import unquote

                decoded = unquote(url).lower()
                if host and host not in url.lower() and host not in decoded:
                    return False
            return True
        return bool(
            self.driver.execute_script(
                """
                if (document.querySelector('input[type="radio"][value="meta"]')) return true;
                for (const lbl of document.querySelectorAll("label")) {
                  if (/HTML\\s*태그/i.test(lbl.textContent || "")) return true;
                }
                const text = document.body?.innerText || "";
                if (/naver-site-verification/i.test(text)) return true;
                if (/HTML\\s*태그/.test(text) && /소유\\s*확인/.test(text) && !/사이트\\s*목록/.test(text)) return true;
                return false;
                """
            )
        )

    def _select_html_tag(self) -> None:
        hit = self.driver.execute_script(
            """
            const norm = (s) => (s || "").replace(/\\s+/g, " ").trim();
            let titleEl = null;
            for (const el of document.querySelectorAll(".title.black--text, .title, div.title")) {
              const t = norm(el.textContent);
              if (t === "HTML 태그" || /^HTML\\s*태그$/.test(t)) { titleEl = el; break; }
            }
            const radio = document.querySelector('input[type="radio"][value="meta"]');
            if (radio) {
              radio.click();
              radio.checked = true;
              radio.dispatchEvent(new Event("change", {bubbles: true}));
            }
            if (titleEl) {
              const target = titleEl.closest('label, .v-radio, .v-card, [role="radio"], .v-list-item') || titleEl;
              target.scrollIntoView({block: "center"});
              try { target.click(); } catch (e) {}
              return "title";
            }
            if (radio) return "radio";
            for (const lbl of document.querySelectorAll("label")) {
              if (/HTML\\s*태그/i.test(lbl.textContent || "")) { lbl.click(); return "label"; }
            }
            return "";
            """
        )
        if hit:
            self.log(f"HTML 태그 선택: {hit}")
        self._tick(1.5)
        for _ in range(8):
            ready = self.driver.execute_script(
                """
                const t = document.body?.innerText || "";
                return /naver-site-verification/i.test(t)
                  || !!document.querySelector('.url_g6MTW, [class*="url_g6MTW"]')
                  || !!document.querySelector('meta[name="naver-site-verification"]')
                  || Array.from(document.querySelectorAll("code, pre, textarea")).some((el) =>
                    /naver-site-verification|content=/i.test(el.textContent || el.value || ""));
                """
            )
            if ready:
                break
            time.sleep(0.6)

    def _get_meta_box(self) -> dict:
        for attempt in range(5):
            got = self.driver.execute_script(_META_JS) or {}
            value = str(got.get("value") or "").strip()
            if value:
                raw = str(got.get("raw") or "")
                tag = ""
                match = re.search(r"<meta[^>]*naver-site-verification[^>]*>", raw, re.I)
                if match:
                    tag = re.sub(r"\s*/?>$", "/>", match.group(0))
                self.log(f"메타 추출 ({got.get('how')}): {value}")
                return {"content": value, "tag": tag or build_meta_tag(value)}
            self.log(f"메타 미검출 (시도 {attempt + 1}/5)")
            self._select_html_tag()
            time.sleep(1.2)
        return {"content": "", "tag": ""}

    def _get_meta_content(self) -> str:
        return str(self._get_meta_box().get("content") or "")

    def _wait_board_url_input(self, timeout: float = 20) -> bool:
        deadline = time.time() + timeout
        while time.time() < deadline:
            self.control.checkpoint()
            if "nid.naver.com" in self._url():
                time.sleep(1.5)
                continue
            found = self.driver.execute_script(
                """
                const inputs = Array.from(document.querySelectorAll('input[type="text"], input[type="url"], input[type="search"], input:not([type]), textarea'));
                let best = null;
                let bestScore = -1;
                for (const el of inputs) {
                  const r = el.getBoundingClientRect();
                  if (r.width < 80 || r.height < 12 || r.bottom < 0 || r.top > innerHeight) continue;
                  if (el.disabled || el.readOnly) continue;
                  const meta = `${el.id || ""} ${el.name || ""} ${el.placeholder || ""} ${el.getAttribute("aria-label") || ""} ${el.className || ""}`;
                  if (/검색/.test(meta) && !/url|사이트|등록/i.test(meta)) continue;
                  let score = r.width;
                  if (/url|사이트|주소|http|도메인|등록/i.test(meta)) score += 1000;
                  if (/input-\\d+/i.test(el.id || "")) score += 200;
                  if (score > bestScore) { bestScore = score; best = el; }
                }
                if (!best) return false;
                document.querySelectorAll("[data-nrc-board-input]").forEach((el) => el.removeAttribute("data-nrc-board-input"));
                best.setAttribute("data-nrc-board-input", "1");
                return true;
                """
            )
            if found:
                return True
            time.sleep(0.4)
        return False

    def _type_board_url(self, site_url: str) -> None:
        value = to_board_host_url(site_url)
        self.driver.execute_script(
            """
            const value = arguments[0];
            const el = document.querySelector('[data-nrc-board-input="1"]')
              || document.querySelector('input[type="text"]')
              || document.querySelector('input[type="url"]');
            if (!el) return false;
            el.focus();
            el.click();
            const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, "value")?.set;
            if (setter) setter.call(el, value);
            else el.value = value;
            el.dispatchEvent(new Event("input", {bubbles: true}));
            el.dispatchEvent(new Event("change", {bubbles: true}));
            return true;
            """,
            value,
        )
        self.log(f"사이트 URL 입력: {value}")

    def _click_ownership_row(self, host: str) -> bool:
        return bool(
            self.driver.execute_script(
                """
                const host = arguments[0];
                const rows = Array.from(document.querySelectorAll('tr, [role="row"], .v-data-table__tr, li'));
                for (const row of rows) {
                  const text = (row.textContent || "").toLowerCase();
                  if (!host || !text.includes(host)) continue;
                  for (const b of row.querySelectorAll('button, a, span, [role="button"], .v-btn')) {
                    const t = (b.textContent || "").replace(/\\s+/g, " ").trim();
                    if (/소유확인\\s*진행/.test(t)) { b.click(); return t.slice(0, 40); }
                  }
                }
                return "";
                """,
                host,
            )
        )

    def _wait_form_input(self, timeout: float = 18) -> dict:
        deadline = time.time() + timeout
        while time.time() < deadline:
            self.control.checkpoint()
            found = self.driver.execute_script(
                """
                const body = document.body?.innerText || "";
                if (/등록되지\\s*않은\\s*사이트|소유\\s*확인|권한이\\s*없|사이트\\s*등록\\s*후/.test(body)
                  && !document.querySelector('input[type="text"], input[type="url"], textarea')) {
                  return {ok: false, blocked: true, reason: "사이트 미등록/권한 없음 화면"};
                }
                const inputs = Array.from(document.querySelectorAll('input[type="text"], input[type="url"], input:not([type]), textarea'));
                let best = null;
                let bestScore = -1;
                for (const el of inputs) {
                  const r = el.getBoundingClientRect();
                  if (r.width < 60 || r.height < 10 || r.bottom < 0 || r.top > innerHeight) continue;
                  if (el.disabled || el.readOnly) continue;
                  const meta = `${el.id || ""} ${el.name || ""} ${el.placeholder || ""} ${el.className || ""}`;
                  let score = r.width;
                  if (/url|사이트|주소|http|sitemap|수집|요청/i.test(meta)) score += 800;
                  if (score > bestScore) { bestScore = score; best = {id: el.id || "", placeholder: el.placeholder || ""}; }
                }
                if (!best) return {ok: false, blocked: false, reason: "input 없음"};
                return {ok: true, ...best};
                """
            ) or {"ok": False}
            if found.get("blocked"):
                return found
            if found.get("ok"):
                return found
            time.sleep(0.4)
        return {"ok": False, "reason": "input 없음 (대기 시간 초과)"}

    def _goto_board(self) -> None:
        if not self.is_alive():
            return
        self._safe_get(BOARD)
        self._tick(1.5)
        self._escape_oauth(BOARD)
        self._accept_alerts()

    def _escape_oauth(self, dest: str) -> None:
        url = self._url()
        if "/auth/" not in url:
            return
        self.log("OAuth 콜백에서 탈출합니다.")
        try:
            self._safe_get(dest or BOARD)
        except Exception:
            pass
        time.sleep(1.2)

    def _accept_consent(self) -> None:
        self.driver.execute_script(
            """
            const body = document.body?.innerText || "";
            if (!/동의|이용약관|개인정보/.test(body)) return false;
            for (const box of document.querySelectorAll('input[type="checkbox"], [role="checkbox"]')) {
              const wrap = box.closest("label, .v-input, div") || box.parentElement;
              if (wrap && /동의|약관/.test(wrap.textContent || "")) {
                if (box.getAttribute("aria-checked") !== "true" && !box.checked) box.click();
              }
            }
            for (const btn of document.querySelectorAll("button, .v-btn, [role='button']")) {
              const t = (btn.textContent || "").replace(/\\s+/g, " ").trim();
              if (/^(확인|동의하기|동의)$/.test(t)) { btn.click(); return true; }
            }
            return false;
            """
        )
        self._tick(0.4)

    def _click_modal_confirm(self) -> None:
        hit = self.driver.execute_script(
            """
            const buttons = Array.from(document.querySelectorAll('button, .v-btn, [role="button"]'));
            for (const btn of buttons) {
              const txt = (btn.textContent || "").replace(/\\s+/g, " ").trim();
              if (!/^(확\\s*인|확인|닫기|OK|예)$/i.test(txt)) continue;
              const dlg = btn.closest('.v-dialog, [role="dialog"], .v-overlay__content, .modal, .ly_pop');
              if (!dlg) continue;
              const r = btn.getBoundingClientRect();
              if (r.width < 10 || r.height < 10) continue;
              btn.click();
              return txt;
            }
            return "";
            """
        )
        if hit:
            self.log(f"안내 창 확인: {hit}")
            self._tick(0.4)

    def _safe_get(self, url: str) -> None:
        self._accept_alerts()
        try:
            self.driver.get(url)
        except UnexpectedAlertPresentException:
            self._accept_alerts()
            try:
                self.driver.get(url)
            except UnexpectedAlertPresentException:
                self._accept_alerts()
                self.driver.get(url)
        self._accept_alerts()

    def _drain_alerts(self) -> None:
        for _ in range(8):
            self._accept_alerts()
            self._click_modal_confirm()
            time.sleep(0.2)

    def _accept_alerts(self) -> None:
        for _ in range(6):
            try:
                alert = self.driver.switch_to.alert
                msg = (alert.text or "").strip()
                alert.accept()
                if msg:
                    self.log(f"안내 창: {msg[:80]}")
                time.sleep(0.2)
            except NoAlertPresentException:
                return
            except UnexpectedAlertPresentException:
                try:
                    self.driver.switch_to.alert.accept()
                except Exception:
                    return
                time.sleep(0.2)
            except Exception:
                return

    def _on_advisor_console(self) -> bool:
        url = self._url()
        if not url:
            return bool(self.state.logged_in)
        if "nid.naver.com" in url or "oauth2.0/authorize" in url:
            return False
        if "searchadvisor.naver.com" in url and "/auth/" not in url:
            return True
        return False

    def _url(self) -> str:
        try:
            return self.driver.current_url or ""
        except UnexpectedAlertPresentException:
            self._accept_alerts()
            try:
                return self.driver.current_url or ""
            except Exception:
                return ""
        except Exception:
            return ""

    def _body_text(self) -> str:
        try:
            return self.driver.execute_script("return document.body?.innerText || '';") or ""
        except Exception:
            return ""

    def _tick(self, seconds: float = 0.0) -> None:
        self.control.checkpoint()
        if seconds:
            time.sleep(seconds)

    def _mark_done(self, blog_id: str, key: str) -> None:
        self.state.done.add(key)
        if self._on_item_done:
            self._on_item_done(blog_id, key)

    def _report(self, step: int, total: int, label: str) -> None:
        self.control.checkpoint()
        if self._on_progress:
            self._on_progress(step, total, label)
        self.log(f"[{step}/{total}] {label}")

    def close(self, kill_chrome: bool = False) -> None:
        with self._lock:
            driver = self.driver
            self.driver = None
            self.state = NaverState()
            proc = self._chrome_proc
            self._chrome_proc = None
        if driver is not None:
            try:
                if kill_chrome or not _debug_port_open(NAVER_DEBUG_PORT):
                    driver.quit()
            except Exception:
                pass
        if kill_chrome and proc is not None:
            try:
                proc.terminate()
                proc.wait(timeout=3)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        self.log("서치어드바이저 연결을 종료했습니다. Chrome 프로필은 유지됩니다.")
