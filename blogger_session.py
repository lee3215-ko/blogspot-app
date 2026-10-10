"""Blogger Chrome 세션: 수동 로그인 후 블로그 인식."""
from __future__ import annotations

import hashlib
import json
import os
import random
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
from selenium.webdriver.common.action_chains import ActionChains
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
    msg = msg.split("Stacktrace:")[0].strip()
    low = msg.lower()
    if "no such window" in low or "web view not found" in low or "target window already closed" in low:
        return "Chrome 탭이 이미 닫혀 있어 페이지로 이동하지 못했습니다"
    if not msg or name == "TimeoutException":
        return f"{name}: 화면 요소를 찾지 못했거나 대기 시간이 지났습니다"
    if len(msg) > 240:
        msg = msg[:240]
    return f"{name}: {msg}"

_BLOG_ID_RE = re.compile(r"^\d{10,}$")


def insert_meta_under_head(html: str, tag: str) -> str:
    source = html or ""
    clean = (tag or "").strip()
    if not source.strip():
        raise RuntimeError("HTML 편집 코드가 비어 있습니다.")
    if not clean:
        raise RuntimeError("넣을 메타 태그가 없습니다.")
    source = re.sub(r"[ \t]*<meta[^>]*naver-site-verification[^>]*>[ \t]*\r?\n?", "", source, flags=re.I)
    source = re.sub(
        r"[ \t]*&lt;meta[^&]*naver-site-verification[^&]*&gt;[ \t]*\r?\n?",
        "",
        source,
        flags=re.I,
    )
    head = re.search(r"(<head\b[^>]*>)", source, re.I)
    if head:
        return source[: head.end()] + "\n    " + clean + source[head.end() :]
    encoded = re.search(r"(&lt;head(?:\s[^&]*)?&gt;)", source, re.I)
    if encoded:
        return source[: encoded.end()] + "\n    " + clean + source[encoded.end() :]
    raise RuntimeError("편집 코드에서 <head>를 찾지 못했습니다.")


def _set_windows_clipboard(text: str) -> None:
    import ctypes

    CF_UNICODETEXT = 13
    GMEM_MOVEABLE = 0x0002
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    kernel32.GlobalAlloc.argtypes = [ctypes.c_uint, ctypes.c_size_t]
    kernel32.GlobalAlloc.restype = ctypes.c_void_p
    kernel32.GlobalLock.argtypes = [ctypes.c_void_p]
    kernel32.GlobalLock.restype = ctypes.c_void_p
    kernel32.GlobalUnlock.argtypes = [ctypes.c_void_p]
    kernel32.GlobalUnlock.restype = ctypes.c_int
    kernel32.GlobalFree.argtypes = [ctypes.c_void_p]
    kernel32.GlobalFree.restype = ctypes.c_void_p
    user32.OpenClipboard.argtypes = [ctypes.c_void_p]
    user32.OpenClipboard.restype = ctypes.c_int
    user32.EmptyClipboard.argtypes = []
    user32.EmptyClipboard.restype = ctypes.c_int
    user32.CloseClipboard.argtypes = []
    user32.CloseClipboard.restype = ctypes.c_int
    user32.SetClipboardData.argtypes = [ctypes.c_uint, ctypes.c_void_p]
    user32.SetClipboardData.restype = ctypes.c_void_p
    data = (text or "").encode("utf-16-le") + b"\x00\x00"
    last = "클립보드에 복사하지 못했습니다."
    for _ in range(4):
        opened = False
        handle = None
        try:
            if not user32.OpenClipboard(None):
                last = "클립보드를 열지 못했습니다."
                time.sleep(0.15)
                continue
            opened = True
            user32.EmptyClipboard()
            handle = kernel32.GlobalAlloc(GMEM_MOVEABLE, len(data))
            if not handle:
                last = "클립보드 메모리를 만들지 못했습니다."
                time.sleep(0.15)
                continue
            locked = kernel32.GlobalLock(handle)
            if not locked:
                last = "클립보드 메모리를 잠그지 못했습니다."
                time.sleep(0.15)
                continue
            ctypes.memmove(ctypes.c_void_p(locked), data, len(data))
            kernel32.GlobalUnlock(handle)
            if not user32.SetClipboardData(CF_UNICODETEXT, handle):
                last = "클립보드에 복사하지 못했습니다."
                time.sleep(0.15)
                continue
            handle = None
            return
        finally:
            if opened:
                user32.CloseClipboard()
            if handle:
                kernel32.GlobalFree(handle)
    raise RuntimeError(last)

_DETECT_JS = """
return (function() {
  const account = document.querySelector('meta[name="og-profile-acct"]')?.content || "";
  const isBlogId = (id) => /^\\d{10,}$/.test(id);
  const hostOf = (href) => {
    try {
      const u = new URL(href);
      return /blogspot\\.com$/i.test(u.hostname) ? u.hostname.toLowerCase() : "";
    } catch (e) {
      return "";
    }
  };
  const options = [...document.querySelectorAll('[role="option"][data-value], [jsname="wQNmvb"][data-value]')];
  const blogs = [];
  const seen = new Set();
  for (const el of options) {
    const id = (el.getAttribute("data-value") || "").trim();
    if (!isBlogId(id) || seen.has(id)) continue;
    const name = (el.getAttribute("aria-label") || el.textContent || "").trim();
    if (!name || name.startsWith("새 블로그") || name.startsWith("New blog")) continue;
    seen.add(id);
    blogs.push({
      id,
      name,
      selected: el.getAttribute("aria-selected") === "true",
      address: "",
    });
  }
  const urlId = (location.href.match(/\\/blog\\/(?:posts|post\\/edit|settings)\\/(\\d{10,})/) || [])[1] || "";
  const deletedPage = !!(
    document.querySelector('[jsname="lIt8ce"]')
    || document.querySelector('img[src*="blogger-trash"]')
  );
  if (urlId && !seen.has(urlId) && !deletedPage) {
    blogs.push({id: urlId, name: document.title.replace(/^Blogger:\\s*/, ""), selected: true, address: ""});
  }
  if (deletedPage && urlId) {
    const idx = blogs.findIndex((b) => b.id === urlId);
    if (idx >= 0) blogs.splice(idx, 1);
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
      const link = item.querySelector('a[aria-label="보기"][href], a[aria-label="View"][href], a.FKF6mc[href]');
      const href = link?.href || "";
      if (!isPostUrl(href) || seenPost.has(href)) continue;
      seenPost.add(href);
      const titleEl = item.querySelector('[id^="post-title-"]') || item.querySelector(".UHwcef");
      posts.push({url: href, title: (titleEl?.textContent || "").trim()});
    }
    const hit = blogs.find((b) => b.id === postsId);
    if (hit) {
      hit.posts = posts;
      hit.postsKnown = true;
    }
  }
  let viewHost = "";
  for (const a of document.querySelectorAll('a[href*="blogspot.com"]')) {
    const href = a.href || "";
    const host = hostOf(href);
    if (!host) continue;
    try {
      const path = new URL(href).pathname || "/";
      if (path === "/" || path === "") {
        viewHost = host;
        break;
      }
    } catch (e) {}
  }
  if (!viewHost && posts[0]) viewHost = hostOf(posts[0].url);
  if (viewHost && postsId) {
    const hit = blogs.find((b) => b.id === postsId);
    if (hit && !hit.address) hit.address = viewHost;
  }
  if (viewHost && address === "") {
    const selected = blogs.find((b) => b.selected);
    if (selected && !selected.address) selected.address = viewHost;
  }
  return {
    account,
    blogs,
    url: location.href,
    title: document.title || "",
    address: address || viewHost,
    posts,
    postsId,
    deletedId: deletedPage && urlId ? urlId : "",
  };
})();
"""

_FIND_BLOG_MENU_JS = """
function visibleEl(el) {
  if (!el) return false;
  const r = el.getBoundingClientRect();
  const s = getComputedStyle(el);
  if (r.width < 8 || r.height < 8) return false;
  if (s.visibility === "hidden" || s.display === "none" || Number(s.opacity) === 0) return false;
  if (r.bottom < 0 || r.top > innerHeight || r.right < 0 || r.left > innerWidth) return false;
  return true;
}
function openMenus() {
  return [...document.querySelectorAll(".OA0qNb, [role='listbox']")].filter((menu) => {
    const rect = menu.getBoundingClientRect();
    if (rect.width < 80 || rect.height < 40) return false;
    const visible = [...menu.querySelectorAll('[role="option"]')].filter(visibleEl);
    return visible.length >= 2;
  });
}
function menuOpen() {
  return openMenus().length > 0;
}
function closedTrigger() {
  const open = openMenus();
  const insideOpen = (el) => open.some((menu) => menu.contains(el));
  const selected = [...document.querySelectorAll(
    '.MocG8c.KKjvXb[data-value], [role="option"][aria-selected="true"][data-value]'
  )].filter((el) => {
    const id = (el.getAttribute("data-value") || "").trim();
    return /^\\d{10,}$/.test(id) && visibleEl(el) && !insideOpen(el);
  });
  selected.sort((a, b) => a.getBoundingClientRect().top - b.getBoundingClientRect().top);
  if (selected.length) {
    const el = selected[0];
    const parent = el.closest(".e2CuFe");
    if (parent && visibleEl(parent)) return parent;
    const r = el.getBoundingClientRect();
    const boxes = [...document.querySelectorAll(".e2CuFe")].filter((box) => visibleEl(box) && !insideOpen(box));
    boxes.sort((a, b) => {
      const ar = a.getBoundingClientRect();
      const br = b.getBoundingClientRect();
      return (Math.abs(ar.top - r.top) + Math.abs(ar.left - r.left))
        - (Math.abs(br.top - r.top) + Math.abs(br.left - r.left));
    });
    if (boxes.length) {
      const br = boxes[0].getBoundingClientRect();
      if (Math.abs(br.top - r.top) < 90 && Math.abs(br.left - r.left) < 420) return boxes[0];
    }
    return el;
  }
  const boxes = [...document.querySelectorAll(".e2CuFe")].filter((el) => visibleEl(el) && !insideOpen(el));
  boxes.sort((a, b) => a.getBoundingClientRect().top - b.getBoundingClientRect().top);
  return boxes[0] || null;
}
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


def posts_for_address(posts, address: str = "") -> list[dict]:
    cleaned = normalize_posts(posts)
    host = normalize_blog_address(address)
    if not host:
        return cleaned
    out = []
    for item in cleaned:
        item_host = host_from_post_url(str(item.get("url") or ""))
        if item_host and item_host != host:
            continue
        out.append(item)
    return out


def compact_blog_host(value: str) -> str:
    host = re.sub(r"^https?://", "", (value or "").strip(), flags=re.I)
    host = host.split("/")[0].split("?")[0].strip().strip(".")
    if host.lower().startswith("www."):
        host = host[4:]
    return host.lower()


def same_blog_host(left: str, right: str) -> bool:
    a, b = compact_blog_host(left), compact_blog_host(right)
    return bool(a) and a == b


def live_blog_address(value: str) -> str:
    blogspot = normalize_blog_address(value)
    if blogspot:
        return blogspot
    host = compact_blog_host(value)
    if host and "." in host:
        return host
    return ""


def normalize_blog_address(value: str) -> str:
    host = re.sub(r"^https?://", "", (value or "").strip(), flags=re.I).rstrip("/")
    host = re.sub(r"/.*$", "", host)
    if host.lower().endswith(".blogspot.com"):
        return host.lower()
    return ""


def _gdata_text(node) -> str:
    if node is None:
        return ""
    if isinstance(node, str):
        return node.strip()
    if isinstance(node, dict):
        return str(node.get("$t") or node.get("href") or "").strip()
    return str(node).strip()


def _gdata_links(node) -> list[dict]:
    if not node:
        return []
    if isinstance(node, dict):
        return [node]
    if isinstance(node, list):
        return [item for item in node if isinstance(item, dict)]
    return []


def _gdata_entries(payload) -> list[dict]:
    feed = payload.get("feed") if isinstance(payload, dict) else None
    if not isinstance(feed, dict):
        return []
    entry = feed.get("entry")
    if isinstance(entry, dict):
        return [entry]
    if isinstance(entry, list):
        return [item for item in entry if isinstance(item, dict)]
    return []


def parse_blogs_feed(text: str) -> list[dict]:
    payload = None
    raw = (text or "").strip()
    if raw.startswith("{") or raw.startswith("["):
        try:
            payload = json.loads(raw)
        except Exception:
            payload = None
    out: list[dict] = []
    if payload:
        for entry in _gdata_entries(payload):
            blog_id = ""
            ident = _gdata_text(entry.get("id"))
            match = re.search(r"blog-(\d{10,})", ident)
            if match:
                blog_id = match.group(1)
            address = ""
            for link in _gdata_links(entry.get("link")):
                href = str(link.get("href") or "")
                rel = str(link.get("rel") or "")
                host = host_from_post_url(href) or normalize_blog_address(href)
                if host and ("alternate" in rel or href.endswith(".blogspot.com/") or href.endswith(".blogspot.com")):
                    address = host
                    if "alternate" in rel:
                        break
            name = _gdata_text(entry.get("title"))
            if blog_id:
                out.append({"id": blog_id, "name": name, "address": address})
        return out
    for block in re.findall(r"<entry\b.*?</entry>", raw, flags=re.I | re.S):
        ident = re.search(r"blog-(\d{10,})", block)
        if not ident:
            continue
        title = re.search(r"<title[^>]*>([^<]+)</title>", block, flags=re.I)
        hrefs = re.findall(r'href="(https?://[^"]*blogspot\.com[^"]*)"', block, flags=re.I)
        address = ""
        for href in hrefs:
            host = normalize_blog_address(href) or host_from_post_url(href)
            if host:
                address = host
                break
        out.append(
            {
                "id": ident.group(1),
                "name": (title.group(1).strip() if title else ""),
                "address": address,
            }
        )
    return out


def parse_posts_feed(text: str) -> tuple[str, list[dict]]:
    payload = None
    raw = (text or "").strip()
    if raw.startswith("{") or raw.startswith("["):
        try:
            payload = json.loads(raw)
        except Exception:
            payload = None
    address = ""
    posts: list[dict] = []
    if payload:
        feed = payload.get("feed") if isinstance(payload, dict) else {}
        for link in _gdata_links((feed or {}).get("link")):
            host = normalize_blog_address(str(link.get("href") or "")) or host_from_post_url(str(link.get("href") or ""))
            if host:
                address = host
                if "alternate" in str(link.get("rel") or ""):
                    break
        for entry in _gdata_entries(payload):
            title = _gdata_text(entry.get("title"))
            url = ""
            for link in _gdata_links(entry.get("link")):
                href = str(link.get("href") or "")
                if is_post_permalink(href):
                    url = href
                    break
            if url:
                posts.append({"url": url, "title": title})
        return address, normalize_posts(posts)
    alt = re.search(r'rel="alternate"[^>]*href="(https?://[^"]+blogspot\.com[^"]*)"', raw, flags=re.I)
    if not alt:
        alt = re.search(r'href="(https?://[^"]+\.blogspot\.com/?)"', raw, flags=re.I)
    if alt:
        address = normalize_blog_address(alt.group(1)) or host_from_post_url(alt.group(1))
    for block in re.findall(r"<entry\b.*?</entry>", raw, flags=re.I | re.S):
        hrefs = re.findall(r'href="(https?://[^"]+\.blogspot\.com/[^"]+)"', block, flags=re.I)
        title = re.search(r"<title[^>]*>([^<]+)</title>", block, flags=re.I)
        url = next((href for href in hrefs if is_post_permalink(href)), "")
        if url:
            posts.append({"url": url, "title": title.group(1).strip() if title else ""})
    return address, normalize_posts(posts)


_CHO = "g,kk,n,d,tt,r,m,b,pp,s,ss,,j,jj,ch,k,t,p,h".split(",")
_JUNG = "a,ae,ya,yae,eo,e,yeo,ye,o,wa,wae,oe,yo,u,wo,we,wi,yu,eu,ui,i".split(",")
_JONG = ",g,kk,gs,n,nj,nh,d,l,lg,lm,lb,ls,lt,lp,lh,m,b,bs,s,ss,ng,j,ch,k,t,p,h".split(",")


def random_blog_address() -> str:
    letters = "abcdefghijklmnopqrstuvwxyz"
    length = random.randint(10, 14)
    digit_at = set(random.sample(range(1, length), k=3))
    chars = [random.choice(letters)]
    for index in range(1, length):
        chars.append(random.choice("0123456789") if index in digit_at else random.choice(letters))
    return "".join(chars)


def blog_address_slug(title: str, extra: str = "") -> str:
    raw = f"{(title or '').strip()}{extra}"
    roman: list[str] = []
    for ch in raw:
        code = ord(ch)
        if 0xAC00 <= code <= 0xD7A3:
            x = code - 0xAC00
            roman.append(_CHO[x // 588] + _JUNG[(x % 588) // 28] + _JONG[x % 28])
        elif ch.isascii() and ch.isalnum():
            roman.append(ch.lower())
    slug = re.sub(r"[^a-z0-9]+", "", "".join(roman))
    if len(slug) < 4:
        digest = hashlib.sha1(raw.encode("utf-8", "ignore")).hexdigest()[:10]
        slug = (slug + digest)[:12]
    slug = slug[:20] or "blog"
    if slug[0].isdigit():
        slug = "b" + slug[:19]
    return slug


def build_robots_txt(address: str) -> str:
    host = re.sub(r"^https?://", "", (address or "").strip(), flags=re.I).rstrip("/")
    if not host:
        raise RuntimeError("블로그 주소가 없어 robots.txt를 만들 수 없습니다.")
    base = f"https://{host}"
    return (
        "User-agent: Mediapartners-Google\n"
        "Disallow:\n"
        "\n"
        "User-agent: *\n"
        "Disallow: /share-widget\n"
        "Allow: /\n"
        "\n"
        f"Sitemap: {base}/sitemap.xml\n"
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


def _run_hidden(cmd: list[str]) -> str:
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0) if os.name == "nt" else 0
    try:
        return subprocess.check_output(
            cmd, timeout=8, stderr=subprocess.STDOUT, creationflags=flags
        ).decode("utf-8", errors="replace")
    except Exception:
        return ""


def _chrome_major_version() -> int:
    chrome = _find_chrome()
    if not chrome:
        return 0
    folder = os.path.dirname(chrome)
    majors: list[int] = []
    try:
        for name in os.listdir(folder):
            if re.match(r"^\d+\.\d+", name) and os.path.isdir(os.path.join(folder, name)):
                try:
                    majors.append(int(name.split(".")[0]))
                except ValueError:
                    pass
    except Exception:
        pass
    if majors:
        return max(majors)
    match = re.search(r"\b(\d+)\.\d+\.\d+", _run_hidden([chrome, "--version"]))
    return int(match.group(1)) if match else 0


def _chromedriver_major_version(path: str) -> int:
    if not path or not os.path.isfile(path):
        return 0
    match = re.search(r"ChromeDriver\s+(\d+)", _run_hidden([path, "--version"]), re.I)
    return int(match.group(1)) if match else 0


def _find_cached_chromedriver(need_major: int = 0) -> str:
    roots = [
        os.path.join(os.path.expanduser("~"), ".wdm", "drivers", "chromedriver"),
        os.path.join(get_data_dir(), "chromedriver"),
    ]
    found: list[str] = []
    for root in roots:
        if not os.path.isdir(root):
            continue
        for dirpath, _dirs, files in os.walk(root):
            if "chromedriver.exe" in files:
                found.append(os.path.join(dirpath, "chromedriver.exe"))
    if not found:
        return ""
    if need_major:
        found = [path for path in found if _chromedriver_major_version(path) == need_major]
        if not found:
            return ""
    found.sort(key=lambda path: (0 if os.path.basename(os.path.dirname(path)) != "chromedriver-win64" else 1, -os.path.getmtime(path)))
    return found[0]


def _chrome_driver_service() -> Service:
    need = _chrome_major_version()
    cached = _find_cached_chromedriver(need)
    if cached:
        return Service(cached)
    try:
        path = ChromeDriverManager().install()
        if path and os.path.isfile(path):
            have = _chromedriver_major_version(path)
            if not need or not have or have == need:
                return Service(path)
    except Exception:
        pass
    return Service()


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


_OPEN_BLOG_DELETE_JS = """
const norm = (el) => (el.innerText || el.textContent || el.getAttribute("aria-label") || "").replace(/\\s+/g, " ").trim();
const scroller = document.querySelector("[role='main']") || document.scrollingElement || document.body;
if (scroller) scroller.scrollTop = scroller.scrollHeight;
window.scrollTo(0, document.body.scrollHeight || 0);
const nodes = [...document.querySelectorAll("button, a, [role='button'], span, div, h1, h2, h3")];
const hits = [];
for (const el of nodes) {
  if (el.children && el.children.length > 4) continue;
  const text = norm(el);
  if (!text || text.length > 60) continue;
  if (
    text === "내 블로그 삭제" ||
    text === "블로그 삭제" ||
    text === "이 블로그 삭제" ||
    /^블로그\\s*삭제/.test(text) ||
    /delete blog/i.test(text)
  ) {
    hits.push(el);
  }
}
hits.sort((a, b) => norm(a).length - norm(b).length);
const hit = hits[0];
if (!hit) {
  const sample = [];
  for (const el of nodes) {
    if (el.children && el.children.length > 2) continue;
    const text = norm(el);
    if (text && text.length < 40 && /삭제|delete/i.test(text) && sample.length < 8) sample.push(text);
  }
  return {ok: false, sample};
}
const target = hit.closest("button, a, [role='button']") || hit;
target.scrollIntoView({block: "center"});
target.click();
return {ok: true, text: norm(target)};
"""


_CONFIRM_BLOG_DELETE_JS = """
const name = String(arguments[0] || "");
const want = String(arguments[1] || "delete");
const visible = (el) => {
  if (!el) return false;
  const r = el.getBoundingClientRect();
  if (r.width < 4 || r.height < 4) return false;
  const style = getComputedStyle(el);
  return style.visibility !== "hidden" && style.display !== "none" && style.opacity !== "0";
};
const visit = (root, sink, selector) => {
  if (!root || !root.querySelectorAll) return;
  try { sink.push(...root.querySelectorAll(selector)); } catch (e) {}
  for (const el of root.querySelectorAll("*")) {
    if (el.shadowRoot) visit(el.shadowRoot, sink, selector);
  }
};
const textOf = (el) => (
  (el.innerText || el.textContent || el.getAttribute("aria-label") || "") + ""
).replace(/\\s+/g, " ").trim();
const pack = (btn, text, kind, labels) => ({ok: true, button: btn, text, kind, labels});
const labels = [];
const nodes = [];
visit(document, nodes, 'button, [role="button"], a, span.RveJvd, span.snByac, [jsname="lIt8ce"]');
for (const el of nodes) {
  const t = textOf(el);
  if (t && t.length < 40 && visible(el) && labels.length < 16 && !labels.includes(t)) labels.push(t);
}

if (want === "permanent") {
  const marked = [];
  visit(document, marked, '[jsname="lIt8ce"]');
  for (const el of marked) {
    const btn = el.closest("[role='button'], button") || el;
    if (!visible(btn)) continue;
    if ((btn.getAttribute("aria-disabled") || "") === "true") continue;
    return pack(btn, textOf(btn) || "영구적으로 삭제", "permanent", labels);
  }
}

if (want === "forever") {
  const dialogs = [];
  visit(document, dialogs, '[role="dialog"], [role="alertdialog"]');
  const dialog = dialogs.find((el) => visible(el) && /완전히 삭제|영구적으로 삭제|delete permanently/i.test(textOf(el))) || null;
  const roots = dialog ? [dialog] : [];
  for (const root of roots) {
    const buttons = [];
    visit(root, buttons, 'button, [role="button"], span.RveJvd, span.snByac');
    for (const el of buttons) {
      const t = textOf(el);
      if (t !== "영구적으로 삭제" && t !== "영구 삭제" && t.toLowerCase() !== "delete permanently") continue;
      if (/삭제 취소/.test(t)) continue;
      const btn = el.closest("button, [role='button']") || el;
      if (!visible(btn)) continue;
      if ((btn.getAttribute("aria-disabled") || "") === "true") continue;
      return pack(btn, t, "forever", labels);
    }
  }
  return {ok: false, button: null, text: "", kind: "", labels, dialog: !!dialog};
}

const dialogs = [];
visit(document, dialogs, '[role="dialog"], [role="alertdialog"]');
const dialog = dialogs.find((el) => {
  if (!visible(el)) return false;
  const t = textOf(el);
  return /완전히 삭제|영구적으로 삭제|블로그 삭제|delete/i.test(t);
}) || null;

if (want === "delete") {
  if (!dialog) return {ok: false, button: null, text: "", kind: "", labels};
  const buttons = [];
  visit(dialog, buttons, 'button, [role="button"], span.RveJvd, span.snByac');
  for (const el of buttons) {
    const t = textOf(el);
    if (t !== "삭제" && t.toLowerCase() !== "delete") continue;
    const btn = el.closest("button, [role='button']") || el;
    if (!visible(btn)) continue;
    if ((btn.getAttribute("aria-disabled") || "") === "true") continue;
    return pack(btn, t, "delete", labels);
  }
  return {ok: false, button: null, text: "", kind: "", labels, dialog: true};
}

const roots = dialog ? [dialog, document] : [document];
for (const root of roots) {
  const buttons = [];
  visit(root, buttons, 'button, [role="button"], a, span.RveJvd, span.snByac, [jsname="lIt8ce"]');
  for (const el of buttons) {
    const t = textOf(el);
    if (t !== "영구적으로 삭제" && t !== "영구 삭제" && t.toLowerCase() !== "delete permanently") continue;
    if (/삭제 취소/.test(t)) continue;
    const btn = el.getAttribute("jsname") === "lIt8ce" ? el : (el.closest("[role='button'], button, [jsname='lIt8ce']") || el);
    if (!visible(btn)) continue;
    if ((btn.getAttribute("aria-disabled") || "") === "true") continue;
    return pack(btn, t, "permanent", labels);
  }
}
return {ok: false, button: null, text: "", kind: "", labels, dialog: !!dialog};
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
        self._lock = threading.RLock()
        self.control = RunControl()
        self._on_progress = None
        self._on_item_done = None
        self._chrome_proc: subprocess.Popen | None = None
        self._chrome_user_dir: str | None = None
        self._gone_ids: set[str] = set()

    def profile_dir(self) -> str:
        path = os.path.join(get_data_dir(), "chrome-blogger-session")
        os.makedirs(path, exist_ok=True)
        return path

    def chrome_running(self) -> bool:
        try:
            with urllib.request.urlopen(
                f"http://127.0.0.1:{BLOGGER_DEBUG_PORT}/json/version", timeout=0.15
            ) as resp:
                return resp.status == 200
        except Exception:
            return False

    def is_alive(self) -> bool:
        return self.driver is not None and self.chrome_running()

    def _window_alive(self) -> bool:
        if self.driver is None:
            return False
        try:
            if not self.driver.current_window_handle:
                return False
            _ = self.driver.title
            return True
        except Exception as exc:
            text = str(exc).lower()
            if "no such window" in text or "web view not found" in text or "target window already closed" in text:
                return False
            return True

    def _focus_open_window(self) -> None:
        if self.driver is None:
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        if self._window_alive():
            return
        try:
            handles = list(self.driver.window_handles)
        except Exception as exc:
            raise RuntimeError("블로그스팟 Chrome 창이 닫혀 있습니다. 다시 로그인해 주세요.") from exc
        chosen = ""
        for handle in handles:
            try:
                self.driver.switch_to.window(handle)
                url = self.driver.current_url or ""
            except Exception:
                continue
            chosen = handle
            if "blogger.com" in url:
                self.log("닫힌 탭 대신 열려 있는 블로그스팟 탭으로 다시 연결했습니다.")
                return
        if not chosen:
            raise RuntimeError("블로그스팟 Chrome 창이 닫혀 있습니다. 다시 로그인해 주세요.")
        self.log("닫힌 탭 대신 열려 있는 Chrome 탭으로 다시 연결했습니다.")

    def _blogger_page(self, section: str, blog_id: str) -> str:
        prefix = ""
        candidates = [self.state.url or ""]
        try:
            candidates.insert(0, self.driver.current_url or "")
        except Exception:
            pass
        for url in candidates:
            match = re.search(r"/u/\d+", url or "")
            if match:
                prefix = match.group(0)
                break
        return f"https://www.blogger.com{prefix}/blog/{section}/{blog_id}"

    def start_incognito(self) -> None:
        self.ensure_window()

    def start_browser(self) -> None:
        self.ensure_window()

    def ensure_window(self) -> None:
        """저장된 프로필의 Chrome을 유지한다. 로그아웃은 하지 않는다."""
        with self._lock:
            if self.driver is not None:
                try:
                    _ = self.driver.current_url
                    return
                except Exception:
                    self.driver = None

            chrome = _find_chrome()
            profile = self.profile_dir()
            self._chrome_user_dir = profile
            if self.chrome_running():
                self.log("열려 있는 블로그스팟 창에 연결합니다.")
            else:
                self.log("저장된 블로그스팟 창을 엽니다. 로그인 상태는 그 창에 남아 있습니다.")
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
            service = _chrome_driver_service()
            driver = webdriver.Chrome(service=service, options=options)
            driver.quit = lambda *args, **kwargs: None
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

    def _on_google_login_page(self, url: str) -> bool:
        text = url or ""
        return any(part in text for part in ("ServiceLogin", "/signin", "AccountChooser", "accounts.google.com/v3/signin"))

    def _show_saved_blogger(self) -> None:
        """이미 로그인된 탭을 찾는다. 로그인 화면이면 다른 주소로 보내지 않는다."""
        self._focus_open_window()
        try:
            current = self.driver.current_window_handle
        except Exception:
            current = ""
        try:
            handles = list(self.driver.window_handles)
        except Exception:
            handles = []
        for handle in handles:
            try:
                self.driver.switch_to.window(handle)
                url = self.driver.current_url or ""
            except Exception:
                continue
            if "blogger.com" in url and not self._on_google_login_page(url):
                return
        if current:
            try:
                self.driver.switch_to.window(current)
            except Exception:
                pass
        try:
            url = self.driver.current_url or ""
        except Exception:
            url = ""
        if self._on_google_login_page(url):
            return
        if "blogger.com" in url:
            return
        self.log("저장된 로그인으로 블로그스팟을 엽니다.")
        self.driver.get(BLOGGER_HOME)

    def recognize(self) -> SessionState:
        """창을 새로 로그인시키지 않고, 그 창에 있는 계정을 읽는다."""
        self.ensure_window()
        self._show_saved_blogger()
        state = self.detect(fresh=True)
        for _ in range(8):
            if state.logged_in or self._on_google_login_page(state.url):
                break
            time.sleep(0.45)
            state = self.detect(fresh=True)
        if state.logged_in:
            self.log(f"블로그스팟 계정을 인식했습니다: {state.account or '-'}")
        else:
            self.state = SessionState(url=state.url, title=state.title)
            state = self.state
            self.log("이 블로그스팟 창에는 로그인된 계정이 없습니다. 창에서 로그인한 뒤 다시 인식을 눌러 주세요.")
        return state

    def detect(self, fresh: bool = False) -> SessionState:
        if self.driver is None or not self.chrome_running():
            return SessionState()
        if not self._lock.acquire(timeout=0.05):
            return self.state
        try:
            raw = self.driver.execute_script(_DETECT_JS)
        except WebDriverException:
            return self.state
        finally:
            try:
                self._lock.release()
            except RuntimeError:
                pass
        previous = {blog.id: blog for blog in self.state.blogs}
        gone = getattr(self, "_gone_ids", None)
        if gone is None:
            self._gone_ids = set()
            gone = self._gone_ids
        deleted_id = str((raw or {}).get("deletedId") or "").strip()
        if deleted_id:
            gone.add(deleted_id)
        blogs = []
        seen = set()
        for item in (raw or {}).get("blogs") or []:
            blog_id = str(item.get("id") or "").strip()
            name = str(item.get("name") or "").strip()
            if not _BLOG_ID_RE.match(blog_id) or blog_id in seen:
                continue
            if not name or name.startswith("새 블로그"):
                continue
            if blog_id in gone:
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
            known = bool(item.get("postsKnown"))
            if known:
                posts = page_posts
                posts_live = True
            elif page_posts:
                posts = page_posts
                posts_live = True
            elif old:
                posts = list(old.posts)
                posts_live = bool(getattr(old, "posts_live", False))
            else:
                posts = []
                posts_live = False
            if posts and not address:
                address = host_from_post_url(str(posts[0].get("url") or ""))
            posts = posts_for_address(posts, address)
            blog = BlogInfo(
                id=blog_id,
                name=name,
                selected=bool(item.get("selected")),
                address=address,
                posts=posts,
                done=set(old.done) if old else set(),
            )
            blog.posts_live = posts_live
            blogs.append(blog)
        if not blogs and previous and not fresh:
            blogs = [blog for blog in previous.values() if blog.id not in gone]
        blogs = [blog for blog in blogs if blog.id not in gone]
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
        self._focus_open_window()
        url = self._blogger_page("posts", blog_id)
        self.log(f"블로그 글 목록으로 이동: {blog_id}")
        self.driver.get(url)
        self._wait_posts_list()
        self.detect()
        self.read_published_post(blog_id)

    def posts_page_url(self, blog_id: str) -> str:
        url = self._blogger_page("posts", blog_id)
        if "/u/" not in url:
            url = f"https://www.blogger.com/u/1/blog/posts/{blog_id}"
        if "hl=" not in url:
            url += "?hl=ko"
        return url

    def open_posts_in_new_tab(self, blog_id: str) -> str:
        if not self.is_alive():
            raise RuntimeError("블로그스팟 Chrome이 연결되어 있지 않습니다. 먼저 로그인해 주세요.")
        url = self.posts_page_url(blog_id)
        with self._lock:
            self._focus_open_window()
            try:
                self.driver.execute_cdp_cmd("Target.createTarget", {"url": url})
            except Exception:
                self.driver.execute_script("window.open(arguments[0], '_blank');", url)
        return url

    def click_new_post(self) -> None:
        if not self.is_alive():
            raise RuntimeError("브라우저가 닫혀 있습니다.")
        button = self._wait(20).until(
            lambda d: d.execute_script(
                """
                const nodes = [...document.querySelectorAll('[aria-label="새 글 작성"]')];
                return nodes.find(el => {
                  const r = el.getBoundingClientRect();
                  return r.width > 8 && r.height > 8 && (el.getAttribute("aria-disabled") || "") !== "true";
                }) || null;
                """
            )
        )
        self._click_jsaction(button)
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
        script = """
        const visible = (el) => {
          if (!el) return false;
          const r = el.getBoundingClientRect();
          if (r.width < 8 || r.height < 8) return false;
          const style = getComputedStyle(el);
          return style.visibility !== "hidden" && style.display !== "none";
        };
        const visit = (root, sink, selector) => {
          if (!root || !root.querySelectorAll) return;
          sink.push(...root.querySelectorAll(selector));
          for (const el of root.querySelectorAll("*")) {
            if (el.shadowRoot) visit(el.shadowRoot, sink, selector);
          }
        };
        const dialogs = [];
        visit(document, dialogs, '[role="dialog"], [role="alertdialog"]');
        const dialog = dialogs.find(el => visible(el) && (el.innerText || "").includes("게시하시겠습니까"));
        if (!dialog) return null;
        const buttons = [];
        visit(dialog, buttons, '[role="button"], button');
        return buttons.find(el => {
          if (!visible(el)) return false;
          if (el.getAttribute("data-id") === "EBS5u") return true;
          return (el.innerText || "").replace(/\\s+/g, " ").trim() === "확인";
        }) || null;
        """
        button = None
        deadline = time.time() + 8
        while time.time() < deadline and button is None:
            self._tick(0.2)
            button = self.driver.execute_script(script)
        if button is None:
            return
        self.log("게시 확인 창에서 확인을 클릭합니다.")
        self._click_jsaction(button)
        self._wait(12).until(
            lambda d: not d.execute_script(
                """
                const nodes = [...document.querySelectorAll('[role="dialog"], [role="alertdialog"]')];
                return nodes.some(el => {
                  const r = el.getBoundingClientRect();
                  return r.width > 8 && (el.innerText || "").includes("게시하시겠습니까");
                });
                """
            )
        )

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
                blog.posts = posts_for_address(posts, blog.address)
                blog.posts_live = True
                if blog.posts and not blog.address:
                    blog.address = host_from_post_url(str(blog.posts[0].get("url") or ""))
                break
        return posts

    def delete_published_post(self, blog_id: str, post_url: str) -> None:
        target = (post_url or "").strip().rstrip("/").lower()
        if not target:
            raise RuntimeError("삭제할 글 주소가 없습니다.")
        self.open_blog_posts(blog_id)
        button = self.driver.execute_script(
            """
            const target = String(arguments[0] || "").replace(/\\/$/, "").toLowerCase();
            const norm = (href) => String(href || "").replace(/\\/$/, "").toLowerCase();
            const items = [...document.querySelectorAll('[role="listitem"]')];
            for (const row of items) {
              const link = row.querySelector('a[aria-label="보기"][href], a.FKF6mc[href]');
              if (!link || norm(link.href) !== target) continue;
              return row.querySelector('[aria-label="이 글을 휴지통으로 이동"], [jsname="nUV0Pd"]');
            }
            return null;
            """,
            post_url,
        )
        if button is None:
            self.log("블로그스팟 글 목록에 없어 프로그램에만 남아 있던 글을 뺍니다.")
            self._drop_post_from_state(blog_id, post_url)
            return
        self.log("글을 휴지통으로 옮깁니다.")
        self._click_jsaction(button)
        confirm = self._wait(8).until(
            lambda d: d.execute_script(
                """
                const visible = (el) => {
                  const r = el.getBoundingClientRect();
                  if (r.width < 8 || r.height < 8) return false;
                  const style = getComputedStyle(el);
                  return style.visibility !== "hidden" && style.display !== "none";
                };
                const dialogs = [...document.querySelectorAll('[role="dialog"], [role="alertdialog"]')];
                const dialog = dialogs.find(el => visible(el) && (el.innerText || "").includes("휴지통으로 이동"));
                if (!dialog) return null;
                const buttons = [...dialog.querySelectorAll('[role="button"], button')];
                return buttons.find(el => {
                  if (!visible(el)) return false;
                  if (el.getAttribute("data-id") === "VkLyEc") return true;
                  return (el.innerText || "").replace(/\\s+/g, " ").trim() === "휴지통으로 이동";
                }) || null;
                """
            )
        )
        self._click_jsaction(confirm)
        self._wait(12).until(
            lambda d: not d.execute_script(
                """
                const target = String(arguments[0] || "").replace(/\\/$/, "").toLowerCase();
                const norm = (href) => String(href || "").replace(/\\/$/, "").toLowerCase();
                const dialogs = [...document.querySelectorAll('[role="dialog"], [role="alertdialog"]')];
                const open = dialogs.some(el => {
                  const r = el.getBoundingClientRect();
                  return r.width > 8 && (el.innerText || "").includes("휴지통으로 이동하시겠습니까");
                });
                if (open) return true;
                const items = [...document.querySelectorAll('[role="listitem"]')];
                return items.some(row => {
                  const link = row.querySelector('a[aria-label="보기"][href], a.FKF6mc[href]');
                  return link && norm(link.href) === target;
                });
                """,
                post_url,
            )
        )
        self.read_published_posts(blog_id)
        self.log("글을 휴지통으로 옮겼습니다.")

    def _drop_post_from_state(self, blog_id: str, post_url: str) -> None:
        key = (post_url or "").strip().rstrip("/").lower()
        if not key:
            return
        for blog in self.state.blogs:
            if blog.id != blog_id:
                continue
            blog.posts = [
                item
                for item in (blog.posts or [])
                if str(item.get("url") or "").strip().rstrip("/").lower() != key
            ]
            break

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

    def publish_manuscript(self, blog_id: str, title: str, html_body: str, image_path: str) -> str:
        self._tick()
        self.open_blog_posts(blog_id)
        before_posts = self.read_published_posts(blog_id)
        before = {str(item.get("url") or "") for item in before_posts}
        wanted = (title or "").strip()
        already = [
            item
            for item in before_posts
            if str(item.get("title") or "").strip() == wanted and str(item.get("url") or "")
        ]
        if already:
            url = str(already[0].get("url") or "")
            self.log(f"같은 제목의 글이 이미 있습니다. 다시 쓰지 않습니다: {wanted}")
            return url
        self.click_new_post()
        self._wait_compose_editor()
        if (image_path or "").strip():
            self._upload_post_image(image_path)
        self._switch_post_html_view()
        if (html_body or "").strip():
            self._append_post_html(html_body)
        self._set_post_title(title)
        self._click_post_publish()
        deadline = time.time() + 25
        refreshed = False
        while time.time() < deadline:
            self._tick(0.4)
            if "/blog/posts/" not in (self.driver.current_url or ""):
                continue
            posts = self.read_published_posts(blog_id)
            fresh = [
                item
                for item in posts
                if str(item.get("url") or "") and str(item.get("url") or "") not in before
            ]
            titled = [item for item in fresh if str(item.get("title") or "").strip() == wanted]
            pick = (titled or fresh or [None])[0]
            if pick:
                return str(pick.get("url") or "")
            if not refreshed:
                try:
                    self.driver.refresh()
                except Exception:
                    pass
                refreshed = True
                try:
                    self._wait_posts_list()
                except Exception:
                    pass
        return ""

    def _wait_compose_editor(self) -> None:
        self._wait(25).until(lambda d: "/blog/post/edit" in (d.current_url or ""))
        self._wait(15).until(
            lambda d: d.execute_script(
                'return !!document.querySelector(\'input[aria-label="제목"], input[aria-label="Title"]\')'
            )
        )
        self._tick(0.4)

    def _switch_post_html_view(self) -> None:
        state = self.driver.execute_script(
            """
            const boxes = [...document.querySelectorAll('[role="listbox"][aria-label="보기 전환"]')];
            const box = boxes.find(el => {
              const r = el.getBoundingClientRect();
              return r.width > 16 && r.height > 8;
            });
            if (!box) return "missing";
            const selected = box.querySelector('[role="option"][aria-selected="true"]');
            if (selected && selected.getAttribute("data-value") === "html") return "already";
            const trigger = box.querySelector('[jsname="LgbsSe"]') || box;
            trigger.click();
            return "opened";
            """
        )
        if state == "missing":
            raise RuntimeError("보기 전환을 찾지 못했습니다.")
        if state != "already":
            self._tick(0.35)
            option = self._wait(8).until(
                lambda d: d.execute_script(
                    """
                    const opts = [...document.querySelectorAll('[role="option"][data-value="html"]')];
                    const visible = opts.find(el => {
                      const r = el.getBoundingClientRect();
                      if (r.width < 8 || r.height < 8) return false;
                      const hidden = el.closest('[style*="display: none"], [style*="display:none"]');
                      return !hidden;
                    });
                    return visible || null;
                    """
                )
            )
            self._click_jsaction(option)
        self._wait(12).until(lambda d: self._post_html_ready())
        self.log("HTML 보기로 전환했습니다.")

    def _post_html_ready(self) -> bool:
        try:
            return bool(
                self.driver.execute_script(
                    """
                    const boxes = [...document.querySelectorAll('.CodeMirror')];
                    return boxes.some(el => {
                      if (!el.CodeMirror) return false;
                      const r = el.getBoundingClientRect();
                      return r.width > 80 && r.height > 40;
                    });
                    """
                )
            )
        except Exception:
            return False

    def _arm_file_input(self) -> None:
        self.driver.execute_script(
            """
            if (!HTMLInputElement.prototype.__bloggerSpotFile) {
              HTMLInputElement.prototype.__bloggerSpotFile = true;
              const origClick = HTMLInputElement.prototype.click;
              HTMLInputElement.prototype.click = function() {
                if ((this.type || "").toLowerCase() === "file") {
                  window.__bloggerFileInput = this;
                  return;
                }
                return origClick.apply(this, arguments);
              };
              if (typeof HTMLInputElement.prototype.showPicker === "function") {
                const origPicker = HTMLInputElement.prototype.showPicker;
                HTMLInputElement.prototype.showPicker = function() {
                  if ((this.type || "").toLowerCase() === "file") {
                    window.__bloggerFileInput = this;
                    return Promise.resolve();
                  }
                  return origPicker.apply(this, arguments);
                };
              }
            }
            window.__bloggerFileInput = null;
            """
        )

    def _find_browse_button(self):
        script = """
        const wanted = new Set(["찾아보기", "Browse"]);
        const visible = (el) => {
          if (!el) return false;
          const r = el.getBoundingClientRect();
          if (r.width < 8 || r.height < 8) return false;
          const style = getComputedStyle(el);
          return style.visibility !== "hidden" && style.display !== "none";
        };
        const visit = (root, out) => {
          if (!root || !root.querySelectorAll) return;
          out.push(...root.querySelectorAll("button, [role='button'], span.UywwFc-vQzf8d, span[jsname='V67aGc']"));
          for (const el of root.querySelectorAll("*")) {
            if (el.shadowRoot) visit(el.shadowRoot, out);
          }
        };
        const nodes = [];
        visit(document, nodes);
        for (const el of nodes) {
          const text = (el.innerText || el.textContent || "").replace(/\\s+/g, " ").trim();
          if (!wanted.has(text) || !visible(el)) continue;
          const btn = el.closest("button, [role='button']") || el;
          if (visible(btn)) return btn;
        }
        return null;
        """
        self.driver.switch_to.default_content()
        found = self.driver.execute_script(script)
        if found is not None:
            return found
        frames = self.driver.find_elements(By.CSS_SELECTOR, "iframe")
        for frame in frames:
            try:
                self.driver.switch_to.default_content()
                self.driver.switch_to.frame(frame)
                self._arm_file_input()
                found = self.driver.execute_script(script)
                if found is not None:
                    return found
            except Exception:
                continue
        self.driver.switch_to.default_content()
        return None

    def _confirm_image_layout(self) -> None:
        script = """
        const visible = (el) => {
          if (!el) return false;
          const r = el.getBoundingClientRect();
          if (r.width < 8 || r.height < 8) return false;
          const style = getComputedStyle(el);
          return style.visibility !== "hidden" && style.display !== "none";
        };
        const dialogs = [...document.querySelectorAll("[role='dialog']")];
        const dialog = dialogs.find(el => visible(el) && (el.innerText || "").includes("레이아웃"));
        if (!dialog) return null;
        const buttons = [...dialog.querySelectorAll("[role='button'], button")];
        return buttons.find(el => visible(el) && (el.innerText || "").replace(/\\s+/g, " ").trim() === "확인") || null;
        """
        button = None
        deadline = time.time() + 15
        while time.time() < deadline and button is None:
            self._tick(0.3)
            button = self.driver.execute_script(script)
        if button is None:
            return
        self.log("이미지 레이아웃에서 확인을 클릭합니다.")
        self._click_jsaction(button)
        self._wait(10).until(
            lambda d: d.execute_script(
                """
                const dialogs = [...document.querySelectorAll("[role='dialog']")];
                return !dialogs.some(el => {
                  const r = el.getBoundingClientRect();
                  return r.width > 8 && (el.innerText || "").includes("레이아웃");
                });
                """
            )
        )

    def _find_image_insert_button(self):
        script = """
        const wanted = ["이미지 삽입", "Insert image", "이미지 추가", "Insert Image", "사진 삽입"];
        const visible = (el) => {
          if (!el) return false;
          const r = el.getBoundingClientRect();
          if (r.width < 8 || r.height < 8) return false;
          const style = getComputedStyle(el);
          return style.visibility !== "hidden" && style.display !== "none";
        };
        const visit = (root, out) => {
          if (!root || !root.querySelectorAll) return;
          out.push(...root.querySelectorAll('[aria-label], [data-tooltip], [role="button"], button'));
          for (const el of root.querySelectorAll("*")) {
            if (el.shadowRoot) visit(el.shadowRoot, out);
          }
        };
        const nodes = [];
        visit(document, nodes);
        for (const el of nodes) {
          const label = (el.getAttribute("aria-label") || el.getAttribute("data-tooltip") || "").trim();
          const text = (el.innerText || "").replace(/\\s+/g, " ").trim();
          if (!wanted.includes(label) && !wanted.includes(text) && !label.includes("이미지 삽입")) continue;
          if ((el.getAttribute("aria-disabled") || "") === "true") continue;
          if (visible(el)) return el;
        }
        return null;
        """
        return self.driver.execute_script(script)

    def _open_compose_overflow(self) -> None:
        button = self.driver.execute_script(
            """
            const labels = ["더보기", "More", "더 보기"];
            const nodes = [...document.querySelectorAll('[aria-label], [data-tooltip], [role="button"]')];
            return nodes.find(el => {
              const label = (el.getAttribute("aria-label") || el.getAttribute("data-tooltip") || "").trim();
              if (!labels.includes(label)) return false;
              const r = el.getBoundingClientRect();
              return r.width > 8 && r.height > 8 && (el.getAttribute("aria-disabled") || "") !== "true";
            }) || null;
            """
        )
        if button is None:
            return
        self._click_jsaction(button)
        self._tick(0.25)

    def _post_has_image(self) -> bool:
        html = (self._post_editor_value() or "").lower()
        if "<img" in html:
            return True
        try:
            return bool(
                self.driver.execute_script(
                    """
                    const roots = [...document.querySelectorAll('[contenteditable="true"]')];
                    return roots.some(el => {
                      const r = el.getBoundingClientRect();
                      if (r.width < 40 || r.height < 20) return false;
                      return !!el.querySelector("img");
                    });
                    """
                )
            )
        except Exception:
            return False

    def _upload_post_image(self, path: str) -> None:
        path = os.path.abspath(path)
        if not os.path.isfile(path):
            raise RuntimeError(f"이미지 파일이 없습니다: {os.path.basename(path)}")
        self._arm_file_input()
        try:
            self.driver.execute_cdp_cmd("Page.setInterceptFileChooserDialog", {"enabled": True})
        except Exception:
            pass
        try:
            self.log("이미지 삽입 버튼을 찾습니다.")
            button = self._find_image_insert_button()
            if button is None:
                self._open_compose_overflow()
                try:
                    button = self._wait(8).until(lambda d: self._find_image_insert_button())
                except Exception:
                    button = None
            if button is None:
                raise RuntimeError("이미지 삽입 버튼을 찾지 못했습니다. 쓰기 화면 툴바를 확인하세요.")
            self._click_jsaction(button)
            self._tick(0.3)
            item = self._wait(6).until(
                lambda d: d.execute_script(
                    """
                    const labels = ["컴퓨터에서 업로드", "Upload from computer", "컴퓨터에서 업로드하기"];
                    const nodes = [
                      ...document.querySelectorAll('[role="menuitem"]'),
                      ...document.querySelectorAll('[data-command="imageUploadPickerV2"]'),
                    ];
                    return nodes.find(el => {
                      const r = el.getBoundingClientRect();
                      if (r.width < 8 || r.height < 8) return false;
                      const label = (el.getAttribute("aria-label") || "").trim();
                      const text = (el.innerText || "").replace(/\\s+/g, " ").trim();
                      return labels.includes(label) || labels.includes(text) || label.includes("컴퓨터에서 업로드");
                    }) || null;
                    """
                )
            )
            self._click_jsaction(item)
            self._tick(0.4)
            browse = self._wait(8).until(lambda d: self._find_browse_button())
            self.log("찾아보기 버튼을 클릭합니다.")
            self._arm_file_input()
            self._click_jsaction(browse)
            accepted = False
            deadline = time.time() + 8
            while time.time() < deadline and not accepted:
                self._tick(0.2)
                captured = self.driver.execute_script("return window.__bloggerFileInput || null")
                if captured is not None:
                    try:
                        captured.send_keys(path)
                        accepted = True
                        break
                    except Exception:
                        pass
                try:
                    self.driver.execute_cdp_cmd(
                        "Page.handleFileChooser",
                        {"action": "accept", "files": [path]},
                    )
                    accepted = True
                except Exception:
                    continue
            if not accepted:
                file_input = self.driver.execute_script(
                    "return document.querySelector('input[type=\"file\"]') || null"
                )
                if file_input is None:
                    raise RuntimeError("찾아보기를 눌렀지만 이미지 파일을 넣지 못했습니다.")
                file_input.send_keys(path)
            self.driver.switch_to.default_content()
            self.log(f"이미지 업로드 중: {os.path.basename(path)}")
            self._confirm_image_layout()
            self._wait(40).until(lambda d: self._post_has_image())
            self.log("이미지를 글에 넣었습니다.")
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
            try:
                self.driver.execute_cdp_cmd("Page.setInterceptFileChooserDialog", {"enabled": False})
            except Exception:
                pass

    def _post_editor_value(self) -> str:
        try:
            value = self.driver.execute_script(
                """
                const boxes = [...document.querySelectorAll('.CodeMirror')];
                let best = null, score = -1;
                for (const el of boxes) {
                  if (!el.CodeMirror) continue;
                  const r = el.getBoundingClientRect();
                  if (r.width < 80 || r.height < 40) continue;
                  const size = r.width * r.height;
                  if (size > score) { score = size; best = el.CodeMirror; }
                }
                return best ? (best.getValue() || "") : "";
                """
            )
        except Exception:
            return ""
        return value or ""

    def _append_post_html(self, html_body: str) -> None:
        extra = html_body or ""
        marker = extra[:40]
        ok = self.driver.execute_script(
            """
            const extra = arguments[0] || "";
            const boxes = [...document.querySelectorAll('.CodeMirror')];
            let best = null, score = -1;
            for (const el of boxes) {
              if (!el.CodeMirror) continue;
              const r = el.getBoundingClientRect();
              if (r.width < 80 || r.height < 40) continue;
              const size = r.width * r.height;
              if (size > score) { score = size; best = el.CodeMirror; }
            }
            if (!best) return false;
            const cur = best.getValue() || "";
            const next = cur.trim() ? cur.replace(/\\s*$/, "\\n") + extra : extra;
            best.setValue(next);
            try { best.save(); } catch (e) {}
            const ta = document.querySelector('textarea.Fdco1c, textarea[jsname="bqeLof"]');
            if (ta) {
              const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, "value").set;
              setter.call(ta, next);
              ta.dispatchEvent(new Event("input", {bubbles: true}));
              ta.dispatchEvent(new Event("change", {bubbles: true}));
            }
            const sample = extra.slice(0, Math.min(40, extra.length));
            return !sample || (best.getValue() || "").includes(sample);
            """,
            extra,
        )
        if not ok or (marker and marker not in (self._post_editor_value() or "")):
            raise RuntimeError("HTML 편집기에 원고를 넣지 못했습니다.")
        self.log("원고를 HTML 보기에 넣었습니다.")

    def _set_post_title(self, title: str) -> None:
        field = self._wait(8).until(
            lambda d: d.execute_script(
                """
                const nodes = [...document.querySelectorAll('input[aria-label="제목"], input[aria-label="Title"]')];
                return nodes.find(el => el.getBoundingClientRect().width > 8) || null;
                """
            )
        )
        self._set_text(field, title)
        self.log(f"제목을 넣었습니다: {title}")

    def _click_post_publish(self) -> None:
        button = self._wait(8).until(
            lambda d: d.execute_script(
                """
                const nodes = [...document.querySelectorAll('[aria-label="게시"]')];
                return nodes.find(el => {
                  const r = el.getBoundingClientRect();
                  const disabled = (el.getAttribute("aria-disabled") || "") === "true";
                  return !disabled && r.width > 8 && r.height > 8;
                }) || null;
                """
            )
        )
        self._click_jsaction(button)
        self.log("게시 버튼을 클릭했습니다.")
        self._tick(0.5)
        self._confirm_publish_dialog()

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
        self._focus_open_window()
        url = self._blogger_page("settings", blog_id)
        already = False
        try:
            already = self._current_settings_blog_id() == blog_id and bool(
                self.driver.find_elements(By.CSS_SELECTOR, '[jscontroller="vo4Jme"], [jscontroller="sHhTg"]')
            )
        except Exception:
            already = False
        if already:
            self.log(f"설정 페이지에 있습니다: {blog_id}")
            return
        self.log(f"설정 페이지로 이동: {blog_id}")
        self.driver.get(url)
        try:
            self._wait(12).until(
                EC.presence_of_element_located(
                    (By.CSS_SELECTOR, '[jscontroller="vo4Jme"], [jscontroller="sHhTg"]')
                )
            )
        except Exception as exc:
            here = ""
            try:
                here = self.driver.current_url or ""
            except Exception:
                here = ""
            raise RuntimeError(f"설정 페이지를 열지 못했습니다. 현재 주소: {here or '알 수 없음'}") from exc
        self._tick()
        self.detect()

    def delete_blog(self, blog_id: str, name: str = "") -> None:
        if not self.is_alive():
            raise RuntimeError("블로그스팟 Chrome이 연결되어 있지 않습니다.")
        self.control.checkpoint()
        self.open_settings(blog_id)
        self.control.checkpoint()
        already = self._find_blog_delete_confirm(name, "permanent")
        if already.get("ok") and already.get("button") is not None:
            self.log("삭제된 페이지가 이미 열려 있습니다.")
        else:
            opened = False
            sample = ""
            for _ in range(6):
                result = self.driver.execute_script(_OPEN_BLOG_DELETE_JS) or {}
                opened = bool(result.get("ok"))
                if opened:
                    self.log(f"블로그 삭제를 눌렀습니다: {result.get('text') or '삭제'}")
                    break
                found = result.get("sample") or []
                if found:
                    sample = ", ".join(str(item) for item in found[:8])
                self._tick(0.45)
            if not opened:
                extra = f" 화면에 보인 문구: {sample}" if sample else ""
                raise RuntimeError(f"설정 화면에서 블로그 삭제를 찾지 못했습니다.{extra}")
            self._click_named_delete_step(name, "delete", "삭제 확인 창의 삭제", 12)
        self._click_named_delete_step(name, "permanent", "삭제된 페이지의 영구적으로 삭제", 20)
        self._click_named_delete_step(name, "forever", "완전 삭제 확인 창의 영구적으로 삭제", 12)
        self._tick(1.0)
        gone = getattr(self, "_gone_ids", None)
        if gone is None:
            self._gone_ids = set()
            gone = self._gone_ids
        gone.add(str(blog_id))
        self.state.blogs = [blog for blog in self.state.blogs if blog.id != blog_id]
        self.log(f"블로그 삭제를 눌렀습니다: {name or blog_id}")

    def _click_named_delete_step(self, name: str, want: str, title: str, seconds: float, optional: bool = False) -> bool:
        self.log(f"{title}를 기다립니다.")
        seen = ""
        deadline = time.time() + seconds
        while time.time() < deadline:
            self.control.checkpoint()
            result = self._find_blog_delete_confirm(name, want)
            labels = result.get("labels") or []
            if labels:
                seen = ", ".join(str(item) for item in labels[:8])
            button = result.get("button")
            if result.get("ok") and button is not None:
                self._click_jsaction(button)
                self.log(f"{title}를 눌렀습니다: {result.get('text') or want}")
                try:
                    self.driver.switch_to.default_content()
                except Exception:
                    pass
                self._tick(0.9)
                return True
            self._tick(0.35)
        extra = f" 화면에 보인 버튼: {seen}" if seen else ""
        if optional:
            return False
        raise RuntimeError(f"{title}를 누르지 못했습니다.{extra}")

    def _find_blog_delete_confirm(self, name: str = "", want: str = "delete") -> dict:
        """삭제 단계 버튼을 찾는다. 영구 삭제는 jsname=lIt8ce를 우선한다."""
        empty = {"ok": False, "button": None, "text": "", "kind": "", "labels": []}
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        try:
            found = self.driver.execute_script(_CONFIRM_BLOG_DELETE_JS, name, want) or empty
        except Exception:
            found = empty
        if found.get("ok") and found.get("button") is not None:
            return found
        labels = list(found.get("labels") or [])
        frames = []
        try:
            frames = self.driver.find_elements(By.CSS_SELECTOR, "iframe")
        except Exception:
            frames = []
        for frame in frames:
            try:
                self.driver.switch_to.default_content()
                self.driver.switch_to.frame(frame)
                result = self.driver.execute_script(_CONFIRM_BLOG_DELETE_JS, name, want) or empty
                for item in result.get("labels") or []:
                    if item not in labels:
                        labels.append(item)
                if result.get("ok") and result.get("button") is not None:
                    result["labels"] = labels
                    return result
            except Exception:
                continue
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        if want == "permanent":
            try:
                for el in self.driver.find_elements(By.CSS_SELECTOR, '[jsname="lIt8ce"]'):
                    if not el.is_displayed():
                        continue
                    labels.append("영구적으로 삭제")
                    return {
                        "ok": True,
                        "button": el,
                        "text": (el.text or "").strip() or "영구적으로 삭제",
                        "kind": "permanent",
                        "labels": labels,
                    }
            except Exception:
                pass
        found["labels"] = labels
        found["ok"] = False
        found["button"] = None
        return found

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

    def _adopt_address(self, blog, address: str, silent: bool = False) -> bool:
        address = live_blog_address(address) or (address or "").strip()
        if not address:
            return False
        prev = (blog.address or "").strip()
        if not prev:
            blog.address = address
            if not silent:
                self.log(f"블로그 주소 인식: {blog.name} → {address}")
            return True
        if same_blog_host(prev, address):
            return False
        blog.address = address
        if not silent:
            self.log(f"블로그 주소 변경: {blog.name} → {address}")
        return True

    def refresh_blog_details(self, should_abort=None, refresh_address: bool = False) -> SessionState:
        self.detect()
        if should_abort and should_abort():
            return self.state
        catalog = self._read_blogs_catalog()
        if catalog:
            self._merge_catalog(catalog)
            self.log(f"계정 피드에서 블로그 주소 {sum(1 for item in catalog if item.get('address'))}개를 읽었습니다.")
        for blog in list(self.state.blogs):
            if should_abort and should_abort():
                self.log("다른 작업이 시작되어 상세 인식을 멈춥니다.")
                return self.state
            self.control.checkpoint()
            have_addr = bool((blog.address or "").strip())
            have_posts = bool(blog.posts or getattr(blog, "posts_live", False))
            if have_addr and have_posts and not refresh_address:
                continue
            try:
                address, posts = self._read_blog_feed(blog.id)
            except Exception as exc:
                self.log(f"피드 인식 실패 ({blog.name}): {exc}")
                continue
            if address:
                self._adopt_address(blog, address)
            if posts and not getattr(blog, "posts_live", False):
                blog.posts = posts_for_address(merge_posts(blog.posts, posts), blog.address)
                self.log(f"글 {len(blog.posts)}개 인식: {blog.name}")
        missing = [blog for blog in self.state.blogs if not (blog.address or "").strip()]
        if missing and not (should_abort and should_abort()):
            self.log(f"주소가 비어 있는 블로그 {len(missing)}개는 설정 페이지에서 이어서 확인합니다.")
            self.fetch_blog_addresses(force=False)
        return self.state

    def _fetch_in_page(self, url: str, timeout: float = 20) -> str:
        if self.driver is None:
            return ""
        if not self._lock.acquire(timeout=8):
            return ""
        try:
            self.driver.set_script_timeout(timeout + 2)
            result = self.driver.execute_async_script(
                """
                const url = arguments[0];
                const done = arguments[arguments.length - 1];
                fetch(url, {credentials: "include", redirect: "follow"})
                  .then(async (res) => done({status: res.status, text: await res.text(), href: res.url}))
                  .catch((err) => done({status: 0, text: "", href: "", error: String(err)}));
                """,
                url,
            ) or {}
            text = str(result.get("text") or "")
            if result.get("status") and int(result.get("status") or 0) >= 400:
                return ""
            return text
        except Exception:
            return ""
        finally:
            try:
                self._lock.release()
            except RuntimeError:
                pass

    def _read_blogs_catalog(self) -> list[dict]:
        for url in (
            "https://www.blogger.com/feeds/default/blogs?alt=json",
            "https://www.blogger.com/feeds/default/blogs",
        ):
            text = self._fetch_in_page(url)
            items = parse_blogs_feed(text)
            if items:
                return items
        return []

    def _read_blog_feed(self, blog_id: str) -> tuple[str, list[dict]]:
        for url in (
            f"https://www.blogger.com/feeds/{blog_id}/posts/default?max-results=25&alt=json",
            f"https://www.blogger.com/feeds/{blog_id}/posts/default?max-results=25",
        ):
            text = self._fetch_in_page(url)
            if not text:
                continue
            address, posts = parse_posts_feed(text)
            if address or posts:
                return address, posts
        return "", []

    def _merge_catalog(self, catalog: list[dict]) -> None:
        gone = getattr(self, "_gone_ids", None) or set()
        known = {blog.id: blog for blog in self.state.blogs}
        page_ids = set(known)
        for item in catalog:
            blog_id = str(item.get("id") or "").strip()
            if not _BLOG_ID_RE.match(blog_id) or blog_id in gone:
                continue
            blog = known.get(blog_id)
            address = live_blog_address(str(item.get("address") or ""))
            name = str(item.get("name") or "").strip()
            if blog is None:
                # 화면 목록에 없는 블로그는 피드로 되살리지 않는다. 삭제·휴지통 블로그가 다시 붙는 것을 막는다.
                if page_ids:
                    continue
                blog = BlogInfo(id=blog_id, name=name or blog_id[-6:], address=address)
                self.state.blogs.append(blog)
                known[blog_id] = blog
                continue
            if name and not blog.name:
                blog.name = name
            if address:
                self._adopt_address(blog, address, silent=True)
        if gone:
            self.state.blogs = [blog for blog in self.state.blogs if blog.id not in gone]

    def create_blogs(self, titles: list[str], control: RunControl | None = None, on_progress=None) -> list[dict]:
        if control is not None:
            self.control = control
        results: list[dict] = []
        clean = [str(title or "").strip() for title in titles if str(title or "").strip()]
        if not clean:
            raise RuntimeError("생성할 블로그 제목이 없습니다.")
        total = len(clean)
        for index, title in enumerate(clean, 1):
            self.control.checkpoint()
            if on_progress:
                on_progress(index - 1, total, f"생성 준비: {title}")
            self.log(f"블로그 생성 {index}/{total}: {title}")
            result = self.create_blog(title)
            results.append(result)
            if on_progress:
                on_progress(index, total, f"생성 완료: {title}" if result.get("ok") else f"생성 실패: {title}")
        return results

    def create_blog(self, title: str, address_slug: str = "") -> dict:
        title = (title or "").strip()
        if not title:
            raise RuntimeError("블로그 제목이 비어 있습니다.")
        if not self.is_alive():
            raise RuntimeError("블로그스팟 브라우저가 닫혀 있습니다.")
        slug = (address_slug or "").strip()
        before = {blog.id for blog in self.state.blogs}
        with self._lock:
            self._ensure_blogger_shell()
            dialog = self._open_create_dialog()
            self._fill_create_title(dialog, title)
            self._click_create_next(dialog)
            self._raise_if_create_refused()
            saved_slug = self._complete_create_wizard(title, slug)
            self._raise_if_create_refused()
            created = self._wait_created_blog(before, title)
            if saved_slug:
                created["address"] = f"{saved_slug}.blogspot.com"
                for blog in self.state.blogs:
                    if blog.id == created.get("id") or (blog.name == title and blog.id not in before):
                        if not (blog.address or "").strip():
                            blog.address = created["address"]
                        break
        if created.get("ok"):
            extra = f" · {created.get('address')}" if created.get("address") else ""
            if created.get("id"):
                extra += f" · {created.get('id')}"
            self.log(f"블로그를 만들었습니다: {title}{extra}")
        else:
            detail = str(created.get("error") or "블로그 생성 결과를 확인하지 못했습니다")
            self.log(f"{detail}: {title}")
        return created

    def _create_refused_message(self) -> str:
        try:
            text = self.driver.execute_script(
                """
                const body = document.body ? (document.body.innerText || "") : "";
                const needles = [
                  "블로그를 생성할 수 없습니다",
                  "블로그를 만들 수 없습니다",
                  "Couldn't create a blog",
                  "Can't create a blog",
                ];
                for (const needle of needles) {
                  if (body.includes(needle)) return needle.endsWith(".") ? needle : needle + ".";
                }
                return "";
                """
            )
        except Exception:
            return ""
        return str(text or "").strip()

    def _raise_if_create_refused(self) -> None:
        message = self._create_refused_message()
        if message:
            raise RuntimeError(message)

    def _ensure_blogger_shell(self) -> None:
        self._focus_open_window()
        try:
            url = self.driver.current_url or ""
        except Exception:
            url = ""
        need_posts = (
            "blogger.com" not in url
            or "/blog/post/edit" in url
            or "/blog/themes/" in url
            or "/blog/settings/" in url
        )
        current_id = next((blog.id for blog in self.state.blogs if blog.selected), "")
        if not current_id and self.state.blogs:
            current_id = self.state.blogs[0].id
        if need_posts and current_id:
            self.driver.get(self._blogger_page("posts", current_id))
            self._tick(0.8)
        elif "blogger.com" not in url:
            self.log("블로그스팟 홈으로 이동합니다.")
            self.driver.get(BLOGGER_HOME)
            self._tick(1.0)
        self._wait(15).until(
            lambda d: d.execute_script(
                """
                return !!(
                  document.querySelector('[aria-label="Blog Selection"]')
                  || document.querySelector('[aria-label="블로그 선택"]')
                  || document.querySelector('[role="option"][data-value]')
                  || document.querySelector('[jsname="wQNmvb"][data-value]')
                );
                """
            )
        )

    def _blog_menu_open(self) -> bool:
        try:
            return bool(
                self.driver.execute_script(
                    _FIND_BLOG_MENU_JS
                    + "return menuOpen();"
                )
            )
        except Exception:
            return False

    def _find_blog_menu_trigger(self):
        return self.driver.execute_script(_FIND_BLOG_MENU_JS + "return closedTrigger();")

    def _menu_probe(self) -> str:
        try:
            info = self.driver.execute_script(
                """
                const box = document.querySelector(".e2CuFe");
                const selected = document.querySelector('[role="option"][aria-selected="true"]');
                return {
                  boxes: document.querySelectorAll(".e2CuFe").length,
                  selected: selected ? (selected.getAttribute("aria-label") || selected.textContent || "").trim().slice(0, 40) : "",
                  options: document.querySelectorAll('[role="option"][data-value]').length,
                  menus: document.querySelectorAll(".OA0qNb").length,
                };
                """
            ) or {}
        except Exception:
            return ""
        return (
            f"선택상자 {info.get('boxes', 0)} · 메뉴 {info.get('menus', 0)} · "
            f"항목 {info.get('options', 0)} · 현재 {info.get('selected') or '-'}"
        )

    def _open_blog_menu(self) -> None:
        if self._blog_menu_open():
            return
        last_error = "블로그 선택 드롭다운을 열지 못했습니다."
        for attempt in range(4):
            trigger = self._find_blog_menu_trigger()
            if trigger is None:
                last_error = f"블로그 선택 상자를 찾지 못했습니다. {self._menu_probe()}"
                self._tick(0.3)
                continue
            label = ""
            try:
                label = (trigger.get_attribute("aria-label") or trigger.text or "").strip().replace("\n", " ")[:40]
            except Exception:
                label = ""
            self.log(f"블로그 선택 상자를 클릭합니다.{(' ' + label) if label else ''}")
            self._click_jsaction(trigger)
            try:
                self._wait(5).until(lambda d: self._blog_menu_open())
                self._tick(0.15)
                return
            except Exception:
                last_error = f"블로그 선택 드롭다운이 열리지 않았습니다. {self._menu_probe()}"
                try:
                    trigger.send_keys(Keys.ARROW_DOWN)
                except Exception:
                    pass
                if self._blog_menu_open():
                    return
                self._tick(0.25)
        raise RuntimeError(last_error)

    def _click_new_blog_option(self) -> None:
        option = self.driver.execute_script(
            _FIND_BLOG_MENU_JS
            + """
            const isNew = (el) => /새 블로그|New blog/.test((el.textContent || "").replace(/\\s+/g, " "));
            const menus = openMenus().sort((a, b) => b.getBoundingClientRect().height - a.getBoundingClientRect().height);
            for (const menu of menus) {
              const hit = [...menu.querySelectorAll('[role="option"], [jsname="wQNmvb"]')].find((el) => {
                return isNew(el) && el.getBoundingClientRect().height > 8;
              });
              if (!hit) continue;
              const box = menu.getBoundingClientRect();
              let item = hit.getBoundingClientRect();
              if (item.bottom > box.bottom - 4 || item.top < box.top + 4) {
                menu.scrollTop += item.top - box.top - 48;
                item = hit.getBoundingClientRect();
              }
              if (!visibleEl(hit)) hit.scrollIntoView({block: "nearest"});
              if (!visibleEl(hit)) continue;
              return hit;
            }
            return null;
            """
        )
        if option is None:
            raise RuntimeError(f"새 블로그... 항목을 찾지 못했습니다. {self._menu_probe()}")
        self.log("새 블로그... 를 클릭합니다.")
        self._trusted_click(option)
        self._tick(0.4)

    def _open_create_dialog(self):
        last_error = "새 블로그 제목 입력란을 찾지 못했습니다."
        for attempt in range(3):
            self.control.checkpoint()
            self._close_open_dialogs()
            if attempt:
                self.log("제목 입력란이 보이지 않아 새 블로그 창을 다시 엽니다.")
                self._tick(0.4)
            try:
                self._open_blog_menu()
                self._click_new_blog_option()
            except Exception as exc:
                last_error = str(exc)
                continue
            dialog = self._wait_create_title_dialog(timeout=6)
            if dialog is not None:
                return dialog
        raise RuntimeError(last_error)

    def _create_title_input(self):
        try:
            return self.driver.execute_script(
                """
                function shown(el) {
                  if (!el) return false;
                  const rect = el.getBoundingClientRect();
                  const style = getComputedStyle(el);
                  if (rect.width < 8 || rect.height < 8) return false;
                  if (style.visibility === "hidden" || style.display === "none") return false;
                  if (Number(style.opacity) === 0) return false;
                  return true;
                }
                const dialogs = [...document.querySelectorAll('[role="dialog"]')].filter(shown);
                const selectors = [
                  'input[aria-label="제목"]',
                  'input[aria-label="Title"]',
                  'input[aria-label*="제목"]',
                  'input[aria-label*="Title"]',
                ];
                for (const dialog of dialogs) {
                  for (const selector of selectors) {
                    for (const field of dialog.querySelectorAll(selector)) {
                      if (shown(field)) return field;
                    }
                  }
                  for (const field of dialog.querySelectorAll('input.whsOnd, input[type="text"]')) {
                    if (shown(field)) return field;
                  }
                }
                return null;
                """
            )
        except Exception:
            return None

    def _wait_create_title_dialog(self, timeout: float = 6):
        try:
            field = self._wait(timeout).until(lambda d: self._create_title_input() or False)
        except Exception:
            return None
        if not field:
            return None
        try:
            dialog = self.driver.execute_script(
                "return arguments[0].closest('[role=\"dialog\"]') || arguments[0];",
                field,
            )
        except Exception:
            dialog = None
        return dialog or self._visible_dialog()

    def _fill_create_title(self, dialog, title: str) -> None:
        field = None
        for selector in (
            'input[aria-label="제목"]',
            'input[aria-label="Title"]',
            'input[aria-label*="제목"]',
            'input[aria-label*="Title"]',
            "input.whsOnd",
            'input[type="text"]',
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
            field = self._create_title_input()
        if field is None:
            raise RuntimeError("새 블로그 제목 입력란을 찾지 못했습니다.")
        self._set_text(field, title)
        self._tick(0.2)
        try:
            self._wait(6).until(
                lambda d: (field.get_attribute("value") or "").strip() == title
            )
        except Exception:
            self.driver.execute_script(
                """
                const el = arguments[0];
                const value = arguments[1];
                el.focus();
                const desc = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, "value");
                if (desc && desc.set) desc.set.call(el, value);
                else el.value = value;
                el.dispatchEvent(new InputEvent("input", {bubbles: true, data: value, inputType: "insertText"}));
                el.dispatchEvent(new Event("change", {bubbles: true}));
                """,
                field,
                title,
            )
            self._tick(0.15)

    def _click_create_next(self, dialog=None, optional: bool = False) -> bool:
        def find_button(driver):
            return driver.execute_script(
                """
                const root = arguments[0] || document;
                const names = ["만들기", "완료", "Create", "Done", "다음", "Next"];
                const buttons = [...root.querySelectorAll('[role="button"], [jsname="tJiF1e"]')];
                for (const name of names) {
                  for (const el of buttons) {
                    const text = (el.textContent || "").replace(/\\s+/g, " ").trim();
                    const disabled = (el.getAttribute("aria-disabled") || "").toLowerCase() === "true";
                    if (!text.includes(name) || disabled) continue;
                    const r = el.getBoundingClientRect();
                    if (r.width > 8 && r.height > 8) return el;
                  }
                }
                return null;
                """,
                dialog,
            )

        try:
            button = self._wait(8).until(find_button)
        except Exception:
            button = None
        if button is None:
            if optional:
                return False
            raise RuntimeError("다음/만들기 버튼을 찾지 못했습니다.")
        self._click_jsaction(button)
        return True

    def _dialog_visible_input(self, dialog, aria_hint: str = ""):
        selectors = []
        if aria_hint:
            selectors.append(f'input[aria-label*="{aria_hint}"]')
        selectors.extend(
            (
                'input[aria-label="주소"]',
                'input[aria-label="Address"]',
                "input.whsOnd",
                'input[type="text"]',
                'input:not([type="hidden"]):not([type="file"])',
            )
        )
        for selector in selectors:
            for el in dialog.find_elements(By.CSS_SELECTOR, selector):
                try:
                    if el.is_displayed():
                        return el
                except Exception:
                    continue
        return None

    def _create_dialog_heading(self, dialog) -> str:
        try:
            for selector in ("h2", ".wGa5od", ".yO22Ne"):
                els = dialog.find_elements(By.CSS_SELECTOR, selector)
                if els:
                    return (els[0].text or "").strip()
            return (dialog.text or "")[:120]
        except Exception:
            return ""

    def _create_dialog_error(self, dialog) -> str:
        try:
            text = (dialog.text or "").replace("\n", " ")
        except Exception:
            return ""
        hints = ("이미 사용", "사용할 수 없", "taken", "not available", "존재합니다", "invalid")
        if any(hint in text.lower() or hint in text for hint in hints):
            return text[:160]
        return ""

    def _deep_find(self, kind: str):
        return self.driver.execute_script(
            """
            function visible(el) {
              if (!el || !el.getBoundingClientRect) return false;
              const r = el.getBoundingClientRect();
              const s = getComputedStyle(el);
              if (r.width < 8 || r.height < 8) return false;
              if (s.visibility === "hidden" || s.display === "none" || Number(s.opacity) === 0) return false;
              return true;
            }
            function walk(root, acc) {
              if (!root || !root.querySelectorAll) return;
              for (const el of root.querySelectorAll("*")) {
                acc.push(el);
                if (el.shadowRoot) walk(el.shadowRoot, acc);
              }
            }
            const nodes = [];
            walk(document, nodes);
            const kind = arguments[0];
            if (kind === "address") {
              return nodes.find((el) => {
                if (el.tagName !== "INPUT") return false;
                const label = (el.getAttribute("aria-label") || "").trim();
                if (label !== "주소" && label !== "Address") return false;
                const s = getComputedStyle(el);
                return s.display !== "none" && s.visibility !== "hidden";
              }) || null;
            }
            if (kind === "save") {
              const input = nodes.find((el) => el.tagName === "INPUT" && ((el.getAttribute("aria-label") || "").trim() === "주소" || (el.getAttribute("aria-label") || "").trim() === "Address"));
              const ir = input ? input.getBoundingClientRect() : null;
              let best = null;
              let bestDist = 1e12;
              for (const span of nodes) {
                if (span.tagName !== "SPAN" || !span.classList || !span.classList.contains("RveJvd")) continue;
                const text = (span.textContent || "").replace(/\\s+/g, " ").trim();
                if (text !== "저장" && text !== "Save") continue;
                const btn = span.closest('[role="button"], button') || span;
                const r = btn.getBoundingClientRect();
                const s = getComputedStyle(btn);
                if (r.width < 8 || r.height < 8) continue;
                if (s.visibility === "hidden" || s.display === "none") continue;
                const dist = ir
                  ? Math.hypot((r.left + r.width / 2) - (ir.left + ir.width / 2), (r.top + r.height / 2) - (ir.top + ir.height / 2))
                  : r.top;
                if (dist < bestDist) {
                  bestDist = dist;
                  best = btn;
                }
              }
              return best;
            }
            if (kind === "verdict") {
              const input = nodes.find((el) => el.tagName === "INPUT" && (el.getAttribute("aria-label") || "").trim() === "주소");
              const host = (input && input.closest('[role="dialog"]')) || null;
              const text = host ? (host.innerText || "") : "";
              if (/사용할 수 없|이미 사용|not available|already in use|unavailable/i.test(text)) return "taken";
              if (/사용할 수 있|is available/i.test(text)) return "ok";
              return "";
            }
            if (kind === "error") {
              for (const el of nodes) {
                const named = el.getAttribute("jsname") === "B34EJ";
                const text = (el.innerText || el.textContent || "").replace(/\\s+/g, " ").trim();
                if (!named && !text) continue;
                if (text.includes("사용할 수 없") || text.includes("사용할수 없") || text.includes("이미 사용")
                    || /not available|already|taken|unavailable/i.test(text)) {
                  return text;
                }
              }
              return "";
            }
            return null;
            """,
            kind,
        )

    def _address_taken_message(self, dialog=None) -> str:
        try:
            if self._deep_find("verdict") == "taken":
                return "사용할 수 없는 블로그 주소입니다."
            text = self._deep_find("error") or ""
        except Exception:
            text = ""
        return str(text or "")

    def _trusted_click(self, element) -> None:
        try:
            self.driver.execute_script(
                "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
                element,
            )
        except Exception:
            pass
        try:
            ActionChains(self.driver).move_to_element(element).pause(0.05).click().perform()
            return
        except Exception:
            pass
        rect = self.driver.execute_script(
            """
            const el = arguments[0];
            const r = el.getBoundingClientRect();
            return {x: r.left + Math.max(r.width, 1) / 2, y: r.top + Math.max(r.height, 1) / 2};
            """,
            element,
        )
        x = float(rect["x"])
        y = float(rect["y"])
        try:
            self.driver.execute_cdp_cmd("Input.dispatchMouseEvent", {"type": "mouseMoved", "x": x, "y": y})
            self.driver.execute_cdp_cmd(
                "Input.dispatchMouseEvent",
                {"type": "mousePressed", "x": x, "y": y, "button": "left", "clickCount": 1},
            )
            self.driver.execute_cdp_cmd(
                "Input.dispatchMouseEvent",
                {"type": "mouseReleased", "x": x, "y": y, "button": "left", "clickCount": 1},
            )
        except Exception:
            self._click_jsaction(element)

    def _fill_address_input(self, dialog, slug: str) -> None:
        field = self._deep_find("address")
        if field is None:
            raise RuntimeError("블로그 주소 입력란을 찾지 못했습니다.")
        self._set_text(field, slug)
        self._tick(0.25)
        try:
            current = (field.get_attribute("value") or "").strip()
        except Exception:
            current = ""
        if current != slug:
            self.driver.execute_script(
                """
                const el = arguments[0];
                const value = arguments[1];
                el.focus();
                const desc = Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, "value");
                if (desc && desc.set) desc.set.call(el, value);
                else el.value = value;
                el.dispatchEvent(new InputEvent("input", {bubbles: true, data: value, inputType: "insertText"}));
                el.dispatchEvent(new Event("change", {bubbles: true}));
                """,
                field,
                slug,
            )
            self._tick(0.2)

    def _save_button_ready(self, button) -> bool:
        try:
            if button is None:
                return False
            return (button.get_attribute("aria-disabled") or "").lower() != "true"
        except Exception:
            return False

    def _wait_save_button(self, timeout: float = 8):
        deadline = time.time() + timeout
        disabled_logged = False
        while time.time() < deadline:
            self.control.checkpoint()
            button = self._deep_find("save")
            if self._save_button_ready(button):
                return button
            if button is not None and not disabled_logged:
                self.log("저장 버튼이 아직 비활성화라 켜질 때까지 기다립니다.")
                disabled_logged = True
            self._tick(0.25)
        return None

    def _click_address_save(self, slug: str = "") -> bool:
        button = self._wait_save_button(5)
        if button is None and slug:
            self._fill_address_input(None, slug)
            button = self._wait_save_button(6)
        if button is None:
            return False
        self.log("저장 버튼을 클릭합니다.")
        self._trusted_click(button)
        return True

    def _address_step_open(self) -> bool:
        try:
            return self._deep_find("address") is not None
        except Exception:
            return False

    def _complete_create_wizard(self, title: str, slug: str) -> str:
        deadline = time.time() + 15
        while time.time() < deadline:
            self.control.checkpoint()
            self._raise_if_create_refused()
            if self._deep_find("address") is not None:
                break
            self._tick(0.25)
        else:
            self._raise_if_create_refused()
            raise RuntimeError("블로그 주소 입력란을 찾지 못했습니다.")
        self.log("블로그 주소 입력란을 찾았습니다.")
        for attempt in range(8):
            self.control.checkpoint()
            self._raise_if_create_refused()
            if not self._address_step_open():
                dialog = self._visible_dialog()
                if dialog is not None and self._dialog_visible_input(dialog, "제목") is not None:
                    self._fill_create_title(dialog, title)
                    self._click_create_next(dialog)
                    self._tick(0.5)
                    continue
                return slug
            used = (slug if attempt == 0 and slug else "") or random_blog_address()
            self.log(f"블로그 주소 입력: {used}.blogspot.com")
            self._fill_address_input(None, used)
            verdict = ""
            deadline = time.time() + 8
            while time.time() < deadline:
                self.control.checkpoint()
                verdict = str(self._deep_find("verdict") or "")
                if verdict in ("ok", "taken"):
                    break
                self._tick(0.25)
            if verdict == "taken":
                self.log(f"사용할 수 없는 주소라 다시 입력합니다: {used}")
                slug = ""
                continue
            clicked = False
            for _ in range(3):
                self.control.checkpoint()
                if not self._click_address_save(used):
                    break
                clicked = True
                closed = False
                for _ in range(12):
                    self._tick(0.25)
                    if str(self._deep_find("verdict") or "") == "taken":
                        self.log(f"사용할 수 없는 주소라 다시 입력합니다: {used}")
                        slug = ""
                        used = ""
                        break
                    if not self._address_step_open():
                        closed = True
                        break
                if not used:
                    break
                if closed:
                    return used
            if not clicked:
                raise RuntimeError("주소 저장 버튼을 찾지 못했습니다.")
            if not used:
                continue
        raise RuntimeError("저장 버튼을 눌렀지만 주소 단계가 끝나지 않았습니다.")

    def _wait_created_blog(self, before: set[str], title: str) -> dict:
        new_id = ""
        for _ in range(12):
            refused = self._create_refused_message()
            if refused:
                return {"ok": False, "title": title, "id": "", "error": refused}
            self._tick(0.35)
            state = self.detect()
            after = {blog.id for blog in state.blogs}
            fresh = [blog for blog in state.blogs if blog.id not in before]
            if fresh:
                hit = next((blog for blog in fresh if blog.name == title), fresh[0])
                new_id = hit.id
                break
            if title and any(blog.name == title and blog.id not in before for blog in state.blogs):
                new_id = next(blog.id for blog in state.blogs if blog.name == title)
                break
            if len(after) > len(before):
                new_id = next(iter(after - before))
                break
        refused = self._create_refused_message()
        if refused:
            return {"ok": False, "title": title, "id": "", "error": refused}
        return {"ok": bool(new_id), "title": title, "id": new_id}

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

    def replace_theme_html(self, blog_id: str, html: str) -> None:
        document = html or ""
        if not document.strip():
            raise RuntimeError("붙여 넣을 HTML이 없습니다.")
        if not re.search(r"<head\b|&lt;head", document, re.I):
            raise RuntimeError("붙여 넣을 HTML에서 <head>를 찾지 못했습니다.")
        if not self.is_alive():
            raise RuntimeError("블로그스팟 브라우저가 닫혀 있습니다.")
        self.control.checkpoint()
        self.log("편집 코드 전체를 복사해 테마 편집기에 붙여 넣습니다.")
        self.open_theme_html_editor(blog_id)
        try:
            self._wait_theme_head()
        except Exception:
            sample = re.sub(r"\s+", " ", (self._read_theme_html() or ""))[:180]
            raise RuntimeError(f"테마 HTML 편집기를 열지 못했습니다. {sample}")
        self._paste_theme_document(document)
        if not self._theme_has_document(document):
            self.log("붙여넣기가 반영되지 않아 편집기 내용 전체를 다시 넣습니다.")
            how = self._write_theme_html(document)
            if not how or not self._theme_has_document(document):
                raise RuntimeError("테마 편집기에 편집 코드 전체를 넣지 못했습니다.")
        self._save_theme_html()
        saved = self._read_theme_html()
        if not self._theme_has_document(document, saved):
            raise RuntimeError("저장 후에도 편집 코드가 테마에 없습니다.")
        self.log("편집 코드 전체를 테마에 붙여 넣고 저장했습니다.")

    def _theme_has_document(self, html: str, current: str | None = None) -> bool:
        now = self._read_theme_html() if current is None else current
        now = now or ""
        source = html or ""
        if re.search(r"naver-site-verification", source, re.I) and not re.search(
            r"naver-site-verification", now, re.I
        ):
            return False
        compact_src = re.sub(r"\s+", "", source)
        compact_now = re.sub(r"\s+", "", now)
        if len(compact_src) < 40:
            return compact_src in compact_now
        start = max(0, len(compact_src) // 2 - 40)
        sample = compact_src[start : start + 80]
        return bool(sample) and sample in compact_now

    def _paste_theme_document(self, html: str) -> None:
        _set_windows_clipboard(html)
        focused = self.driver.execute_script(
            _FIND_THEME_CM_JS
            + """
            const cm = findThemeCM();
            if (cm) {
              try { cm.focus(); } catch (e) {}
              try { cm.execCommand("selectAll"); } catch (e) {}
              const input = cm.getInputField && cm.getInputField();
              if (input) input.focus();
              return "cm";
            }
            const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
            if (!ta) return "";
            ta.focus();
            ta.select();
            return "textarea";
            """
        )
        if not focused:
            raise RuntimeError("테마 편집기에 포커스를 주지 못했습니다.")
        self._tick(0.2)
        ActionChains(self.driver).key_down(Keys.CONTROL).send_keys("v").key_up(Keys.CONTROL).perform()
        self._tick(0.8)

    def _write_theme_html(self, html: str) -> str:
        how = self.driver.execute_script(
            _FIND_THEME_CM_JS
            + """
            const html = arguments[0];
            const ta = document.querySelector('textarea[jsname="bqeLof"], textarea.Fdco1c');
            if (ta) {
              const setter = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, "value")?.set;
              if (setter) setter.call(ta, html);
              else ta.value = html;
              ta.dispatchEvent(new Event("input", {bubbles: true}));
              ta.dispatchEvent(new Event("change", {bubbles: true}));
            }
            const cm = findThemeCM();
            if (cm) {
              cm.setValue(html);
              try { cm.save(); } catch (e) {}
              try { cm.refresh(); } catch (e) {}
              return "cm";
            }
            return ta ? "textarea" : "";
            """,
            html,
        )
        self._tick(0.3)
        return str(how or "")

    def open_theme_html_editor(self, blog_id: str) -> None:
        self._focus_open_window()
        url = self._blogger_page("themes", blog_id)
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
        done = set()
        for blog in self.state.blogs:
            if blog.id == blog_id:
                done = set(blog.done)
                break

        self._report(2, total, "구글,네이버 디스크립션")
        if description:
            self.set_google_description(description)
            self._mark_done(blog_id, "description")
        self._report(3, total, "검색 설명")
        if self._try_setting_step("검색 설명 사용 설정", self.enable_search_description):
            if description and self._try_setting_step("검색 설명", lambda: self.set_search_description(description)):
                self._mark_done(blog_id, "search_desc")
        self._report(4, total, "파비콘")
        if favicon_path:
            self.set_favicon(favicon_path)
            self._mark_done(blog_id, "favicon")
        self._report(5, total, "시간대")
        if "timezone" in done:
            self.log("시간대는 이미 적용되어 건너뜁니다.")
        elif self._try_setting_step("시간대", self.set_timezone_seoul):
            self._mark_done(blog_id, "timezone")
        self._report(6, total, "robots.txt")
        if "robots" in done:
            self.log("robots.txt는 이미 적용되어 건너뜁니다.")
        elif self._try_setting_step("robots.txt", lambda: self.apply_robots_settings(address)):
            self._mark_done(blog_id, "robots")
        self._report(7, total, "로봇 헤더 태그")
        if "headers" in done:
            self.log("로봇 헤더 태그는 이미 적용되어 건너뜁니다.")
        elif self._try_setting_step("로봇 헤더 태그", self.apply_robot_header_settings):
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
        last_exc = None
        for attempt in range(3):
            try:
                self._close_open_dialogs()
                self._wait_setting_row_ready("sHhTg", "설명", timeout=8)
                self._click_setting_row("sHhTg", "설명")
                self._fill_visible_dialog(text, title_hint="설명")
                self.log("구글,네이버 디스크립션을 입력했습니다.")
                return
            except Exception as exc:
                last_exc = exc
                self.log(f"설명 설정 창을 다시 엽니다 ({attempt + 1}/3)")
                try:
                    self._close_open_dialogs()
                except Exception:
                    pass
                self._tick(0.4)
        raise last_exc

    def set_search_description(self, text: str) -> None:
        last_exc = None
        for attempt in range(3):
            try:
                self._close_open_dialogs()
                self._wait_setting_row_ready("mM3Kjc", "검색 설명", timeout=12)
                self._click_setting_row("mM3Kjc", "검색 설명")
                self._fill_visible_dialog(text, title_hint=("검색 설명", "Search description"))
                self.log("검색 설명을 입력했습니다.")
                return
            except Exception as exc:
                last_exc = exc
                self.log(f"검색 설명 창을 다시 엽니다 ({attempt + 1}/3)")
                try:
                    self._close_open_dialogs()
                except Exception:
                    pass
                self._tick(0.4)
        raise last_exc

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
        last_exc = None
        for attempt in range(3):
            try:
                self._close_open_dialogs()
                box = self._wait_setting_toggle(
                    ("검색 설명 사용 설정", "Enable search description", "Use search description"),
                    timeout=14,
                )
                self._set_toggle(
                    box,
                    True,
                    labels=("검색 설명 사용 설정", "Enable search description", "Use search description"),
                )
                self.log("검색 설명 사용 설정을 켰습니다.")
                return
            except Exception as exc:
                last_exc = exc
                self.log(f"검색 설명 사용 설정을 다시 찾습니다 ({attempt + 1}/3)")
                try:
                    self._close_open_dialogs()
                except Exception:
                    pass
                self._tick(0.4)
        raise last_exc

    def apply_robots_settings(self, address: str) -> None:
        self._enable_aria_checkbox("맞춤 robots.txt 사용 설정")
        self._wait_setting_unlocked("AyIhkc")
        self.set_custom_robots_txt(address)

    def apply_robot_header_settings(self) -> None:
        self._enable_aria_checkbox("맞춤 로봇 헤더 태그 사용 설정")
        for controller, label, tag in (
            ("ZVRmn", "홈페이지 태그", "all"),
            ("Y2HcZd", "자료실 및 검색 페이지 태그", "noindex"),
            ("tybrDe", "글 및 페이지 태그", "all"),
        ):
            self._wait_setting_row_ready(controller, label)
            self._set_robot_header_row(controller, label, tag)

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
        self._set_robot_header_row("ZVRmn", "홈페이지 태그", "all")

    def _set_robot_header_row(self, controller: str, label: str, wanted: str) -> None:
        self._close_open_dialogs()
        self._click_setting_row(controller, label)
        dialog = self._wait_dialog()
        self._set_robot_tag_checks(dialog, wanted)
        self._click_named_button(dialog, "저장", wait_enabled=True)
        self._wait_dialog_closed(dialog)
        self.log(f"{label} {wanted}을(를) 켜고 저장했습니다.")

    def _set_robot_tag_checks(self, dialog, wanted: str) -> None:
        names = (
            "all",
            "noindex",
            "nofollow",
            "none",
            "noarchive",
            "nosnippet",
            "noodp",
            "notranslate",
            "noimageindex",
            "unavailable_after",
        )
        wanted = (wanted or "all").strip()
        if wanted not in names:
            raise RuntimeError(f"알 수 없는 로봇 태그: {wanted}")
        for name in names:
            self._set_aria_checkbox(name, name == wanted, scope=dialog)

    def _set_aria_checkbox(self, aria_label: str, on: bool, scope=None) -> None:
        if scope is None:
            self._close_open_dialogs()
            box = self._wait_setting_toggle((aria_label,), timeout=14)
            self._set_toggle(box, on, labels=(aria_label,))
            return
        selector = f'[aria-label="{aria_label}"][role="checkbox"]'
        root = scope
        box = self._wait(10).until(
            lambda d: _displayed(root.find_elements(By.CSS_SELECTOR, selector))
        )
        self._set_toggle(box, on, selector=selector, root=root)

    def _enable_aria_checkbox(self, aria_label: str, scope=None) -> None:
        self._set_aria_checkbox(aria_label, True, scope=scope)
        self.log(f"{aria_label}을(를) 켰습니다.")

    def _setting_label_aliases(self, label: str) -> tuple[str, ...]:
        aliases = {
            "검색 설명": ("검색 설명", "Search description"),
            "검색 설명 사용 설정": ("검색 설명 사용 설정", "Enable search description", "Use search description"),
            "설명": ("설명", "Description"),
        }
        return aliases.get(label, (label,))

    def _scroll_settings_for(self, hint: str) -> None:
        try:
            self.driver.execute_script(
                """
                const hint = String(arguments[0] || "").replace(/\\s+/g, "").toLowerCase();
                const norm = (s) => String(s || "").replace(/\\s+/g, "").toLowerCase();
                const hit = [...document.querySelectorAll('[role="checkbox"], [role="switch"], .EDnCLe, [jscontroller]')]
                  .find((el) => {
                    const t = norm(el.getAttribute("aria-label") || el.textContent);
                    return hint && t.includes(hint.slice(0, Math.min(hint.length, 6)));
                  });
                let scroller = document.scrollingElement || document.documentElement;
                for (const el of document.querySelectorAll("div, [role='main']")) {
                  const st = getComputedStyle(el);
                  if ((st.overflowY === "auto" || st.overflowY === "scroll") && el.scrollHeight > el.clientHeight + 40) {
                    scroller = el;
                    break;
                  }
                }
                if (hit) {
                  hit.scrollIntoView({block: "center"});
                  return;
                }
                const bottom = scroller.scrollTop + scroller.clientHeight >= scroller.scrollHeight - 8;
                if (bottom) scroller.scrollTop = 0;
                else scroller.scrollBy(0, Math.max(280, (scroller.clientHeight || 400) * 0.65));
                """,
                hint,
            )
        except Exception:
            pass

    def _find_setting_toggle(self, labels) -> object | None:
        names = [str(item) for item in (labels or ()) if str(item).strip()]
        if not names:
            return None
        return self.driver.execute_script(
            """
            const labels = arguments[0].map((s) => String(s || "").replace(/\\s+/g, "").toLowerCase()).filter(Boolean);
            const norm = (s) => String(s || "").replace(/\\s+/g, "").toLowerCase();
            const nodes = [...document.querySelectorAll('[role="checkbox"], [role="switch"]')];
            return nodes.find((el) => {
              const aria = norm(el.getAttribute("aria-label"));
              return labels.some((label) => aria === label || aria.includes(label));
            }) || null;
            """,
            names,
        )

    def _wait_setting_toggle(self, labels, timeout: float = 14):
        hint = str((labels or ("설정",))[0])
        def found(_driver):
            self._scroll_settings_for(hint)
            return self._find_setting_toggle(labels)

        return self._wait(timeout).until(found)

    def _set_toggle(self, box, on: bool, selector: str = "", root=None, labels=None) -> None:
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", box)
        self._tick(0.15)
        current = (box.get_attribute("aria-checked") or "").lower() == "true"
        if current == on:
            return
        try:
            self._click_jsaction(box)
        except Exception:
            try:
                box.click()
            except Exception:
                self.driver.execute_script("arguments[0].click();", box)
        expect = "true" if on else "false"

        def checked(_driver):
            el = box
            if selector:
                scope = root if root is not None else self.driver
                el = _displayed(scope.find_elements(By.CSS_SELECTOR, selector)) or box
            elif labels:
                el = self._find_setting_toggle(labels) or box
            return (el.get_attribute("aria-checked") or "").lower() == expect

        self._wait(6).until(checked)

    def _wait_setting_unlocked(self, controller: str, timeout: float = 10) -> None:
        def unlocked(driver):
            self._scroll_settings_for(controller)
            els = driver.find_elements(By.CSS_SELECTOR, f'[jscontroller="{controller}"]')
            if not els:
                return False
            return (els[0].get_attribute("data-is-disable-dialog") or "").lower() != "true"

        self._wait(timeout).until(unlocked)
        self._tick()

    def _wait_setting_row_ready(self, controller: str, label: str, timeout: float = 10) -> None:
        def ready(_driver):
            self._scroll_settings_for(label)
            el = self._find_setting_row(controller, label)
            if el is None:
                return False
            return (el.get_attribute("data-is-disable-dialog") or "").lower() != "true"

        self._wait(timeout).until(ready)
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
            const labels = arguments[0].map((s) => String(s || "").replace(/\\s+/g, "").toLowerCase());
            const rows = [...document.querySelectorAll('.cI5zJb')];
            return rows.find((row) => {
              const first = row.querySelector('.EDnCLe');
              const text = String((first && first.textContent) || "").replace(/\\s+/g, "").toLowerCase();
              return text && labels.some((label) => text === label || text.includes(label));
            }) || null;
            """,
            list(self._setting_label_aliases(label)),
        )

    def _click_setting_row(self, controller: str, label: str) -> None:
        el = self._find_setting_row(controller, label)
        if el is None:
            raise RuntimeError(f"설정 항목을 찾지 못했습니다: {label}")
        self.driver.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
        self._tick(0.15)
        self._click_jsaction(el)

    def _is_page_chrome_dialog(self, dialog) -> bool:
        try:
            label = (dialog.get_attribute("aria-label") or "").strip().lower()
            if "navigational drawer" in label or "navigation drawer" in label:
                return True
            class_name = dialog.get_attribute("class") or ""
            if "UMrnmb" in class_name:
                return True
        except Exception:
            return False
        return False

    def _visible_dialog(self):
        for dialog in self.driver.find_elements(By.CSS_SELECTOR, '[role="dialog"]'):
            try:
                if not dialog.is_displayed() or self._is_page_chrome_dialog(dialog):
                    continue
                return dialog
            except Exception:
                continue
        return None

    def _wait_dialog(self, title_hint: str | None = None, timeout: float = 15):
        def found(driver):
            for dialog in driver.find_elements(By.CSS_SELECTOR, '[role="dialog"]'):
                try:
                    if not dialog.is_displayed() or self._is_page_chrome_dialog(dialog):
                        continue
                    if title_hint:
                        hints = title_hint if isinstance(title_hint, (list, tuple)) else (title_hint,)
                        text = dialog.text or ""
                        if not any(str(hint) in text for hint in hints if str(hint).strip()):
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
            cancel = None
            for button in dialog.find_elements(By.CSS_SELECTOR, '[role="button"]'):
                if "취소" not in (button.text or ""):
                    continue
                if button.is_displayed():
                    cancel = button
                    break
            if cancel is not None:
                self._click_jsaction(cancel)
                self._wait_dialog_closed(dialog)
                return
        except Exception:
            pass
        try:
            self.driver.find_element(By.TAG_NAME, "body").send_keys(Keys.ESCAPE)
        except Exception:
            pass
        self._tick(0.2)

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

    def reattach(self) -> bool:
        with self._lock:
            if self.driver is not None:
                try:
                    _ = self.driver.current_url
                except Exception:
                    self.driver = None
            if self.driver is None:
                if not self.chrome_running():
                    return False
                self.log("열려 있는 블로그스팟 Chrome에 다시 연결합니다.")
                options = Options()
                options.add_experimental_option("debuggerAddress", f"127.0.0.1:{BLOGGER_DEBUG_PORT}")
                service = _chrome_driver_service()
                self.driver = webdriver.Chrome(service=service, options=options)
                self.driver.quit = lambda *args, **kwargs: None
        self.detect()
        if self.state.logged_in:
            self.log("블로그스팟 로그인을 유지한 채로 연결했습니다.")
        return bool(self.state.logged_in)

    def close(self, kill_chrome: bool = False) -> None:
        with self._lock:
            driver = self.driver
            self.driver = None
            self.state = SessionState()
            proc = self._chrome_proc
            self._chrome_proc = None
            self._chrome_user_dir = None
        _release_driver(driver, kill_browser=kill_chrome)
        if kill_chrome and proc is not None:
            try:
                proc.terminate()
                proc.wait(timeout=3)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        if kill_chrome:
            self.log("브라우저를 종료했습니다. Chrome 프로필은 유지됩니다.")
        elif self.chrome_running():
            self.log("프로그램 연결만 끊습니다. Chrome 로그인은 그대로 둡니다.")


def _release_driver(driver, kill_browser: bool) -> None:
    if driver is None:
        return
    if kill_browser:
        try:
            driver.quit()
        except Exception:
            pass
        return
    try:
        driver.quit = lambda *args, **kwargs: None
    except Exception:
        pass
    service = getattr(driver, "service", None)
    proc = getattr(service, "process", None) if service is not None else None
    if service is not None:
        try:
            service.process = None
        except Exception:
            pass
    if proc is not None:
        try:
            proc.kill()
        except Exception:
            pass
