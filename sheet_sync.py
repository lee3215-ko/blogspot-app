"""블로그 기록을 지정한 구글 스프레드시트의 '블로그스팟 기록' 탭에 올린다."""
from __future__ import annotations

import csv
import ctypes
import io
import os
import re
import subprocess
import threading
import time
import urllib.request
from ctypes import wintypes

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager

from blogger_session import _find_chrome, _wait_debug_port
from paths import get_data_dir

RECORD_SHEET_ID = "1xQnL0kc1dJm9jeAL78O5D-IUBXPZE9_qwI3kIVH6Wm0"
RECORD_SHEET_GID = "627503332"
DEFAULT_SHEET_URL = (
    "https://docs.google.com/spreadsheets/d/"
    f"{RECORD_SHEET_ID}/edit?gid={RECORD_SHEET_GID}#gid={RECORD_SHEET_GID}"
)
SHEET_DEBUG_PORT = 9338

HEADERS = [
    "블로그제목",
    "색인상태",
    "현재상태",
    "핵심키워드",
    "주소",
    "한줄메모",
    "색인아이디",
    "검색결과",
    "노출키워드",
    "현재작업",
    "HTML코드",
    "수집횟수",
    "최근수집",
    "처음수집",
    "최근글수집",
    "최근확인",
    "첫색인일",
    "잘림시작",
    "구글이메일",
    "글주소",
    "전체흐름",
    "직전상태",
    "폴더",
    "블로그ID",
]

# 시트에서 사람이 고치는 칸. 프로그램 값이 비어 있을 때만 시트 값을 남긴다.
SHEET_WINS_IF_LOCAL_EMPTY = {
    "핵심키워드",
    "구글이메일",
    "현재상태",
    "검색결과",
    "현재작업",
    "노출키워드",
    "최근확인",
    "한줄메모",
    "첫색인일",
    "잘림시작",
    "전체흐름",
    "직전상태",
}

STATUS_OPTIONS = [
    "확인전",
    "생성만",
    "설정완료",
    "수집요청",
    "재수집요청",
    "미색인",
    "색인됨",
    "POST만색인",
    "재색인확인",
    "노출됨",
    "재노출확인",
    "별도키워드노출",
    "잘림의심",
    "잘림확신",
    "노출후이탈",
    "색인사라짐",
]

RECORD_FIELDS = (
    "keyword",
    "google_email",
    "sheet_status",
    "search_result",
    "work",
    "exposed_keyword",
    "sheet_note",
    "first_index_at",
    "trim_started_at",
    "status_flow",
    "prev_status",
    "last_check",
)

_ID_RE = re.compile(r"/spreadsheets/d/([a-zA-Z0-9-_]+)")


def spreadsheet_id(url: str) -> str:
    match = _ID_RE.search(url or "")
    if not match:
        raise ValueError("구글 스프레드시트 주소가 아닙니다. 시트 링크를 붙여 넣어 주세요.")
    return match.group(1)


def sheet_gid(url: str) -> str:
    match = re.search(r"[?#&]gid=(\d+)", url or "")
    if match:
        return match.group(1)
    if spreadsheet_id(url) == RECORD_SHEET_ID:
        return RECORD_SHEET_GID
    return "0"


def sheet_edit_url(sheet_id: str) -> str:
    return f"https://docs.google.com/spreadsheets/d/{sheet_id}/edit"


def sheet_tab_url(url: str) -> str:
    sheet_id = spreadsheet_id(url)
    gid = sheet_gid(url)
    return f"https://docs.google.com/spreadsheets/d/{sheet_id}/edit?gid={gid}#gid={gid}"


def _cell(value) -> str:
    return str(value or "").replace("\t", " ").replace("\r", " ").replace("\n", " / ").strip()


def index_status_label(indexed, checked_at: str, address: str) -> str:
    if not str(address or "").strip():
        return "주소 없음"
    if not str(checked_at or "").strip():
        return "확인 전"
    if indexed is True:
        return "색인됨"
    if indexed is False:
        return "미색인"
    return "확인 실패"


def program_row(record: dict) -> list[str]:
    values = {
        "블로그제목": record.get("title"),
        "색인상태": record.get("index_status"),
        "현재상태": record.get("sheet_status"),
        "핵심키워드": record.get("keyword"),
        "주소": record.get("address"),
        "한줄메모": record.get("sheet_note"),
        "색인아이디": record.get("naver_id"),
        "검색결과": record.get("search_result"),
        "노출키워드": record.get("exposed_keyword"),
        "현재작업": record.get("work"),
        "HTML코드": record.get("html_code"),
        "수집횟수": record.get("collect_count"),
        "최근수집": record.get("last_collect"),
        "처음수집": record.get("first_collect"),
        "최근글수집": record.get("last_post_collect"),
        "최근확인": record.get("last_check"),
        "첫색인일": record.get("first_index_at"),
        "잘림시작": record.get("trim_started_at"),
        "구글이메일": record.get("google_email"),
        "글주소": record.get("posts"),
        "전체흐름": record.get("status_flow"),
        "직전상태": record.get("prev_status"),
        "폴더": record.get("folder"),
        "블로그ID": record.get("id"),
    }
    return [_cell(values.get(name, "")) for name in HEADERS]


def to_tsv(rows: list[list[str]]) -> str:
    lines = []
    for row in rows:
        padded = list(row) + [""] * (len(HEADERS) - len(row))
        lines.append("\t".join(_cell(cell) for cell in padded[: len(HEADERS)]))
    return "\n".join(lines)


def parse_csv(text: str) -> list[list[str]]:
    raw = (text or "").lstrip("\ufeff").strip()
    if not raw or raw.startswith("<") or raw.startswith("ERROR"):
        return []
    return [row for row in csv.reader(io.StringIO(raw)) if any(str(cell).strip() for cell in row)]


def fetch_sheet_csv(url: str) -> list[list[str]]:
    """링크가 열린 시트의 지정 탭만 읽는다. 다른 탭은 열지 않는다."""
    export = (
        "https://docs.google.com/spreadsheets/d/"
        f"{spreadsheet_id(url)}/export?format=csv&gid={sheet_gid(url)}"
    )
    request = urllib.request.Request(export, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(request, timeout=30) as response:
        payload = response.read()
    return parse_csv(payload.decode("utf-8-sig", errors="replace"))


def _record_header(row: list[str]) -> bool:
    return bool(row) and "블로그ID" in row and "주소" in row


def merge_rows(program_rows: list[list[str]], sheet_rows: list[list[str]]) -> list[list[str]]:
    header = list(HEADERS)
    index = {name: pos for pos, name in enumerate(header)}
    sheet_header = sheet_rows[0] if sheet_rows else []
    sheet_index = {name: pos for pos, name in enumerate(sheet_header)}
    body = sheet_rows[1:] if _record_header(sheet_header) else sheet_rows
    by_id: dict[str, list[str]] = {}
    by_address: dict[str, list[str]] = {}
    used: set[int] = set()
    id_pos = sheet_index.get("블로그ID", -1)
    address_pos = sheet_index.get("주소", -1)
    for row_index, row in enumerate(body):
        blog_id = str(row[id_pos]).strip() if id_pos >= 0 and id_pos < len(row) else ""
        address = str(row[address_pos]).strip().rstrip("/").lower() if 0 <= address_pos < len(row) else ""
        if blog_id:
            by_id[blog_id] = row
        elif address:
            by_address[address] = row
        else:
            used.add(row_index)

    merged = [header]
    seen: set[str] = set()
    for program in program_rows:
        row = list(program) + [""] * (len(header) - len(program))
        row = row[: len(header)]
        blog_id = row[index["블로그ID"]]
        address = row[index["주소"]].strip().rstrip("/").lower()
        sheet = by_id.get(blog_id) if blog_id else None
        if sheet is None and address:
            sheet = by_address.get(address)
        if sheet:
            if blog_id and blog_id in by_id:
                seen.add(blog_id)
            for name in SHEET_WINS_IF_LOCAL_EMPTY:
                pos = index[name]
                if row[pos]:
                    continue
                src = sheet_index.get(name)
                if src is None or src >= len(sheet):
                    continue
                filled = _cell(sheet[src])
                if filled:
                    row[pos] = filled
        merged.append(row)

    if _record_header(sheet_header):
        for row in body:
            blog_id = str(row[id_pos]).strip() if 0 <= id_pos < len(row) else ""
            if blog_id and blog_id in seen:
                continue
            if blog_id and any(item[index["블로그ID"]] == blog_id for item in merged[1:]):
                continue
            kept = [""] * len(header)
            for name, pos in index.items():
                src = sheet_index.get(name)
                if src is not None and src < len(row):
                    kept[pos] = _cell(row[src])
            if any(kept):
                merged.append(kept)
    return merged


def sheet_user_values(sheet_rows: list[list[str]]) -> list[dict]:
    if not sheet_rows or not _record_header(sheet_rows[0]):
        raise ValueError("이 시트는 아직 블로그 기록 형식이 아닙니다. 먼저 올리기를 해 주세요.")
    header = sheet_rows[0]
    index = {name: pos for pos, name in enumerate(header)}
    found = []
    for row in sheet_rows[1:]:
        def cell(name: str, row=row) -> str:
            pos = index.get(name)
            if pos is None or pos >= len(row):
                return ""
            return _cell(row[pos])

        blog_id = cell("블로그ID")
        address = cell("주소")
        if not blog_id and not address:
            continue
        found.append(
            {
                "id": blog_id,
                "address": address,
                "keyword": cell("핵심키워드"),
                "google_email": cell("구글이메일"),
                "sheet_status": cell("현재상태"),
                "search_result": cell("검색결과"),
                "work": cell("현재작업"),
                "exposed_keyword": cell("노출키워드"),
                "last_check": cell("최근확인"),
                "sheet_note": cell("한줄메모"),
                "first_index_at": cell("첫색인일"),
                "trim_started_at": cell("잘림시작"),
                "status_flow": cell("전체흐름"),
                "prev_status": cell("직전상태"),
            }
        )
    return found


def set_clipboard_text(text: str) -> None:
    CF_UNICODETEXT = 13
    GMEM_MOVEABLE = 0x0002
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    user32.OpenClipboard.argtypes = [wintypes.HWND]
    user32.OpenClipboard.restype = wintypes.BOOL
    user32.EmptyClipboard.restype = wintypes.BOOL
    user32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
    user32.SetClipboardData.restype = wintypes.HANDLE
    user32.CloseClipboard.restype = wintypes.BOOL
    kernel32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
    kernel32.GlobalAlloc.restype = wintypes.HGLOBAL
    kernel32.GlobalLock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalLock.restype = ctypes.c_void_p
    kernel32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
    kernel32.GlobalUnlock.restype = wintypes.BOOL
    data = text.encode("utf-16-le") + b"\x00\x00"
    opened = False
    for _ in range(10):
        if user32.OpenClipboard(None):
            opened = True
            break
        time.sleep(0.05)
    if not opened:
        raise RuntimeError("클립보드를 열지 못했습니다.")
    try:
        if not user32.EmptyClipboard():
            raise RuntimeError("클립보드를 비우지 못했습니다.")
        handle = kernel32.GlobalAlloc(GMEM_MOVEABLE, len(data))
        if not handle:
            raise RuntimeError("클립보드 메모리를 만들지 못했습니다.")
        locked = kernel32.GlobalLock(handle)
        if not locked:
            raise RuntimeError("클립보드 메모리를 잠그지 못했습니다.")
        ctypes.memmove(locked, data, len(data))
        kernel32.GlobalUnlock(handle)
        if not user32.SetClipboardData(CF_UNICODETEXT, handle):
            raise RuntimeError("클립보드에 기록을 넣지 못했습니다.")
    finally:
        user32.CloseClipboard()


def _wait_new_handle(driver, before: set[str], timeout: float = 15):
    end = time.time() + timeout
    while time.time() < end:
        handles = list(driver.window_handles)
        fresh = [handle for handle in handles if handle not in before]
        if fresh:
            return fresh[-1]
        time.sleep(0.2)
    raise RuntimeError("크롬에서 새 탭을 찾지 못했습니다.")


def _open_tab(driver, url: str) -> tuple[str, str | None]:
    original = None
    try:
        original = driver.current_window_handle
    except Exception:
        original = None
    before = set(driver.window_handles)
    try:
        driver.execute_cdp_cmd("Target.createTarget", {"url": url})
    except Exception:
        driver.execute_script("window.open(arguments[0], '_blank');", url)
    handle = _wait_new_handle(driver, before)
    driver.switch_to.window(handle)
    return handle, original


def _restore_window(driver, original: str | None) -> None:
    if not original:
        return
    try:
        if original in driver.window_handles:
            driver.switch_to.window(original)
    except Exception:
        pass


def _wait_sheet_ready(driver, timeout: float = 25) -> None:
    from selenium.webdriver.common.by import By
    from selenium.webdriver.support.ui import WebDriverWait

    WebDriverWait(driver, timeout).until(lambda d: d.find_elements(By.ID, "t-name-box"))


def _read_csv(driver, sheet_id: str, gid: str = "") -> list[list[str]]:
    del driver
    url = sheet_edit_url(sheet_id)
    if gid:
        url = f"{url}?gid={gid}"
    elif sheet_id == RECORD_SHEET_ID:
        url = DEFAULT_SHEET_URL
    return fetch_sheet_csv(url)


def _select_a1(driver) -> None:
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys

    box = driver.find_element(By.ID, "t-name-box")
    box.click()
    box.send_keys(Keys.CONTROL, "a")
    box.send_keys("A1")
    box.send_keys(Keys.ENTER)
    time.sleep(0.25)


def _paste_rows(driver, rows: list[list[str]], gid: str = "") -> None:
    from selenium.webdriver.common.action_chains import ActionChains
    from selenium.webdriver.common.keys import Keys

    current = driver.current_url or ""
    if gid and f"gid={gid}" not in current:
        raise RuntimeError("기록 탭이 아니라서 다른 시트는 그대로 두었습니다.")
    set_clipboard_text(to_tsv(rows))
    driver.execute_script("window.focus();")
    _select_a1(driver)
    ActionChains(driver).key_down(Keys.CONTROL).send_keys("a").key_up(Keys.CONTROL).perform()
    time.sleep(0.15)
    ActionChains(driver).send_keys(Keys.DELETE).perform()
    time.sleep(0.2)
    _select_a1(driver)
    ActionChains(driver).key_down(Keys.CONTROL).send_keys("v").key_up(Keys.CONTROL).perform()
    time.sleep(0.8)


def _sheet_target_id(url_part: str) -> str:
    import json

    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{SHEET_DEBUG_PORT}/json", timeout=3) as resp:
            targets = json.load(resp)
    except Exception:
        return ""
    for target in targets:
        if target.get("type") != "page":
            continue
        if url_part and url_part in str(target.get("url") or ""):
            return str(target.get("id") or "")
    return ""


def _focus_window_title(part: str) -> None:
    user32 = ctypes.windll.user32
    found: list[int] = []

    @ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
    def callback(hwnd, _lparam):
        if not user32.IsWindowVisible(hwnd):
            return True
        buf = ctypes.create_unicode_buffer(512)
        user32.GetWindowTextW(hwnd, buf, 512)
        if part and part in buf.value:
            found.append(int(hwnd))
        return True

    user32.EnumWindows(callback, 0)
    if not found:
        return
    hwnd = found[0]
    user32.ShowWindow(hwnd, 9)
    user32.keybd_event(0x12, 0, 0, 0)
    user32.keybd_event(0x12, 0, 2, 0)
    user32.SetForegroundWindow(hwnd)


def _show_sheet_tab(driver, sheet_url: str) -> None:
    sheet_id = spreadsheet_id(sheet_url) if "/spreadsheets/d/" in sheet_url else ""
    target_id = _sheet_target_id(sheet_id)
    if target_id:
        try:
            driver.execute_cdp_cmd("Target.activateTarget", {"targetId": target_id})
        except Exception:
            pass
    time.sleep(0.4)
    _focus_window_title("블로그스팟 기록")
    if sheet_id:
        _focus_window_title(sheet_id[:8])


def _rename_sheet(driver, title: str) -> None:
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys

    for selector in (".docs-title-input", "input.docs-title-input"):
        fields = driver.find_elements(By.CSS_SELECTOR, selector)
        if not fields:
            continue
        field = fields[0]
        try:
            field.click()
            field.send_keys(Keys.CONTROL, "a")
            field.send_keys(title)
            field.send_keys(Keys.ENTER)
            return
        except Exception:
            continue


class _SheetChrome:
    """블로그스팟 로그인 크롬과 프로필이 다른 시트 전용 창."""

    def __init__(self) -> None:
        self._lock = threading.RLock()
        self.driver = None

    def port_open(self) -> bool:
        try:
            with urllib.request.urlopen(
                f"http://127.0.0.1:{SHEET_DEBUG_PORT}/json/version", timeout=0.3
            ) as resp:
                return resp.status == 200
        except Exception:
            return False

    def ensure(self, url: str):
        with self._lock:
            if self.driver is not None:
                try:
                    _ = self.driver.current_url
                except Exception:
                    self.driver = None
            fresh = False
            if self.driver is None:
                if not self.port_open():
                    profile = os.path.join(get_data_dir(), "chrome-sheet-session")
                    os.makedirs(profile, exist_ok=True)
                    subprocess.Popen(
                        [
                            _find_chrome(),
                            f"--remote-debugging-port={SHEET_DEBUG_PORT}",
                            f"--user-data-dir={profile}",
                            "--no-first-run",
                            "--no-default-browser-check",
                            "--disable-popup-blocking",
                            "--new-window",
                            "--window-size=1400,900",
                            url,
                        ]
                    )
                    _wait_debug_port(SHEET_DEBUG_PORT)
                    fresh = True
                options = Options()
                options.add_experimental_option("debuggerAddress", f"127.0.0.1:{SHEET_DEBUG_PORT}")
                driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)
                driver.quit = lambda: None
                self.driver = driver
            if not fresh:
                self._show(url)
            self._focus()
            return self.driver

    def _show(self, url: str) -> None:
        driver = self.driver
        if driver is None:
            return
        try:
            driver.get(url)
        except Exception:
            pass

    def _focus(self) -> None:
        return


_sheet_chrome = _SheetChrome()


def _wait_new_sheet_url(driver, timeout: float = 180) -> str:
    end = time.time() + timeout
    while time.time() < end:
        current = driver.current_url or ""
        if "accounts.google.com" in current:
            _sheet_chrome._focus()
        match = _ID_RE.search(current)
        if match and "/create" not in current:
            return current.split("?")[0]
        time.sleep(0.4)
    raise RuntimeError("새 크롬 창에서 구글 로그인이 끝나면 시트가 열립니다. 로그인 후 새 시트 만들기를 다시 눌러 주세요.")


def _run_on_sheet(url: str, work):
    driver = _sheet_chrome.ensure(url)
    with _sheet_chrome._lock:
        result = work(driver)
        _sheet_chrome._focus()
        return result


def create_spreadsheet(session=None) -> str:
    return DEFAULT_SHEET_URL


def open_spreadsheet(url: str, session=None) -> str:
    return sheet_tab_url(url)


def plan_sheet_update(
    program_rows: list[list[str]],
    sheet_rows: list[list[str]],
    drop_ids: set[str] | None = None,
    new_ids: set[str] | None = None,
) -> list[list[str]] | None:
    """시트에 이미 있는 줄만 고친다. new_ids만 새 줄로 넣고, drop_ids는 뺀다."""
    drop = {str(item).strip() for item in (drop_ids or set()) if str(item).strip()}
    fresh = {str(item).strip() for item in (new_ids or set()) if str(item).strip()}
    if not sheet_rows or not _record_header(sheet_rows[0]):
        raise ValueError("이 시트는 아직 블로그 기록 형식이 아닙니다. 먼저 올리기를 해 주세요.")
    header = sheet_rows[0]
    id_pos = header.index("블로그ID")
    sheet_ids = {
        str(row[id_pos]).strip()
        for row in sheet_rows[1:]
        if id_pos < len(row) and str(row[id_pos]).strip()
    }
    blog_col = HEADERS.index("블로그ID")
    selected: list[list[str]] = []
    for row in program_rows:
        padded = list(row) + [""] * (len(HEADERS) - len(row))
        blog_id = str(padded[blog_col]).strip()
        if not blog_id or blog_id in drop:
            continue
        if blog_id in sheet_ids or blog_id in fresh:
            selected.append(padded[: len(HEADERS)])
    merged = merge_rows(selected, sheet_rows)
    status_pos = header.index("현재상태") if "현재상태" in header else -1
    manual_status: dict[str, str] = {}
    program_statuses = {"생성만", "설정완료", "수집요청", "재수집요청"}
    if status_pos >= 0:
        for row in sheet_rows[1:]:
            if id_pos >= len(row):
                continue
            blog_id = str(row[id_pos]).strip()
            value = str(row[status_pos]).strip() if status_pos < len(row) else ""
            if blog_id and value and value not in program_statuses:
                manual_status[blog_id] = value
    status_col = HEADERS.index("현재상태")
    for row in merged[1:]:
        blog_id = str(row[blog_col]).strip()
        current = manual_status.get(blog_id)
        if current and row[status_col] in program_statuses.union({""}):
            row[status_col] = current
    if drop:
        merged = [merged[0]] + [
            row for row in merged[1:] if str(row[blog_col]).strip() not in drop
        ]
    current = merge_rows([], sheet_rows)
    if list(sheet_rows[0]) == list(HEADERS) and to_tsv(merged) == to_tsv(current):
        return None
    return merged


def push_updated_rows(
    url: str,
    program_rows: list[list[str]],
    drop_ids: set[str] | None = None,
    new_ids: set[str] | None = None,
    session=None,
) -> tuple[int, bool]:
    gid = sheet_gid(url)
    target = sheet_tab_url(url)
    existing = fetch_sheet_csv(target)
    merged = plan_sheet_update(program_rows, existing, drop_ids, new_ids)
    if merged is None:
        return 0, False

    def work(driver):
        _wait_sheet_ready(driver)
        if gid and f"gid={gid}" not in (driver.current_url or ""):
            driver.get(target)
            _wait_sheet_ready(driver)
        _paste_rows(driver, merged, gid)
        return len(merged) - 1, True

    return _run_on_sheet(target, work)


def push_rows(url: str, program_rows: list[list[str]], session=None) -> tuple[int, int]:
    gid = sheet_gid(url)
    target = sheet_tab_url(url)

    def work(driver):
        _wait_sheet_ready(driver)
        if gid and f"gid={gid}" not in (driver.current_url or ""):
            driver.get(target)
            _wait_sheet_ready(driver)
        existing = fetch_sheet_csv(target)
        merged = merge_rows(program_rows, existing)
        _paste_rows(driver, merged, gid)
        return len(program_rows), max(0, len(merged) - 1 - len(program_rows))

    return _run_on_sheet(target, work)


def pull_rows(url: str, session=None) -> list[dict]:
    return sheet_user_values(fetch_sheet_csv(url))


def _self_check() -> None:
    assert spreadsheet_id("https://docs.google.com/spreadsheets/d/abc_DEF-123/edit") == "abc_DEF-123"
    assert spreadsheet_id(DEFAULT_SHEET_URL) == RECORD_SHEET_ID
    assert sheet_gid(DEFAULT_SHEET_URL) == RECORD_SHEET_GID
    assert f"gid={RECORD_SHEET_GID}" in sheet_tab_url(DEFAULT_SHEET_URL)
    assert index_status_label(True, "2026-10-01", "https://a.blogspot.com/") == "색인됨"
    assert index_status_label(False, "2026-10-01", "https://a.blogspot.com/") == "미색인"
    assert index_status_label(None, "", "https://a.blogspot.com/") == "확인 전"
    assert index_status_label(None, "", "") == "주소 없음"
    assert "생성순서" not in HEADERS
    assert HEADERS[0] == "블로그제목"
    assert HEADERS[1] == "색인상태"
    assert HEADERS[-1] == "블로그ID"
    old_header = [
        "블로그ID", "생성순서", "핵심키워드", "구글이메일", "블로그제목", "주소", "현재상태",
    ]
    old_row = ["10", "1", "카드깡", "a@gmail.com", "예전제목", "https://a.blogspot.com/", "색인됨"]
    manual = ["99", "9", "수기", "", "수기블로그", "https://b.blogspot.com/", ""]
    program = [program_row({
        "id": "10",
        "order": "1",
        "title": "카드",
        "address": "https://a.blogspot.com/",
        "keyword": "",
        "index_status": "미색인",
    })]
    merged = merge_rows(program, [old_header, old_row, manual])
    assert merged[0] == HEADERS
    assert merged[1][HEADERS.index("핵심키워드")] == "카드깡"
    assert merged[1][HEADERS.index("블로그제목")] == "카드"
    assert merged[1][HEADERS.index("현재상태")] == "색인됨"
    assert merged[1][HEADERS.index("색인상태")] == "미색인"
    assert merged[2][HEADERS.index("블로그ID")] == "99"
    assert len(sheet_user_values(merged)) == 2
    live = [HEADERS, program_row({"id": "10", "order": "1", "title": "예전", "index_status": "확인 전"})]
    changed = plan_sheet_update(
        [program_row({"id": "10", "order": "1", "title": "카드", "index_status": "미색인"})],
        live,
    )
    assert changed is not None
    assert changed[1][HEADERS.index("색인상태")] == "미색인"
    kept = [list(row) for row in live]
    kept[1][HEADERS.index("현재상태")] = "재색인확인"
    guarded = plan_sheet_update(
        [program_row({
            "id": "10",
            "order": "1",
            "title": "카드",
            "sheet_status": "수집요청",
            "index_status": "미색인",
        })],
        kept,
    )
    assert guarded is not None
    assert guarded[1][HEADERS.index("현재상태")] == "재색인확인"
    assert guarded[1][HEADERS.index("색인상태")] == "미색인"
    assert plan_sheet_update(
        [program_row({"id": "77", "title": "없는블로그"})],
        live,
    ) is None
    added = plan_sheet_update(
        [program_row({"id": "77", "order": "2", "title": "새블로그"})],
        live,
        new_ids={"77"},
    )
    assert added is not None
    assert any(row[HEADERS.index("블로그ID")] == "77" for row in added[1:])
    removed = plan_sheet_update([], live, drop_ids={"10"})
    assert removed is not None and len(removed) == 1
    print("ok", len(merged))


if __name__ == "__main__":
    _self_check()
