"""구글스팟 HOME NEW 시트(2026-10-06 연동 준비판)의 규칙을 프로그램 안에서 그대로 재현한다.

시트의 Apps Script가 하던 일을 하나씩 옮겼다.
- 열 구조 A:AD (30열) + 변경 로그 AE:AK
- 상태 목록 / 계정 생성상태 목록 / 옛 상태 이름 정리
- 상태 확정(confirmCurrentState_): 직전·전전상태, 날짜 칸, 전체흐름, 변경 로그, 하루 중복 방지
- 요약 I:M 수식(검색결과·현재 작업·노출키워드·최근 확인·한줄 특이사항)과 Z/AA/AC 수식
- 본표 정렬(sortMasterRows_): 삭제됨 맨 아래 → 이메일 첫 등장 순서 → 프로그램 순서(없으면 키워드 우선순위) → 날짜 → 상태
- 묶음 경계(getBoundaryType_): 이메일이 바뀌면 굵은 선, 같은 이메일에서 키워드가 바뀌면 중간 선

이 모듈은 tk를 모른다. 순수 함수와 dict만 다루므로 `python home_records.py`로 자가 점검한다.
"""

from __future__ import annotations

import re
import unicodedata
from datetime import date, datetime

# ----- 열 구조 ---------------------------------------------------------------
HOME_HEADERS = [
    "핵심키워드",        # A
    "로그인 이메일",     # B
    "계정 생성상태",     # C
    "마지막확인",        # D
    "도메인주소",        # E
    "블로그테마 주소",   # F
    "블로그제목(H1)",    # G
    "현재상태",          # H
    "현재 검색결과",     # I  (수식)
    "현재 작업",         # J  (수식)
    "현재 노출키워드",   # K  (수식 =Q)
    "최근 확인",         # L  (수식)
    "한줄 특이사항",     # M  (수식)
    "직전상태",          # N
    "전전상태",          # O
    "오늘확인",          # P  (체크박스)
    "현재노출키워드",    # Q
    "메모",              # R
    "처음수집",          # S
    "첫색인확인",        # T
    "핵심노출",          # U
    "핵심마지막",        # V
    "잘림시작",          # W
    "재수집요청최근",    # X
    "재수집요청이력",    # Y
    "색인 소요일",       # Z  (수식)
    "노출 유지일",       # AA (수식)
    "전체흐름",          # AB
    "노출이탈",          # AC (수식)
    "생성일",            # AD
]

LOG_HEADERS = ["변경일시", "핵심키워드", "도메인", "이전상태", "변경상태/이벤트", "현재노출키워드", "메모"]

# 사람이 고치는 칸 → 프로그램 저장 키. 나머지는 프로그램이 채운다.
EDITABLE = {
    "핵심키워드": "keyword",
    "로그인 이메일": "google_email",
    "계정 생성상태": "account_status",
    "마지막확인": "account_check",
    "블로그테마 주소": "theme_url",
    "블로그제목(H1)": "h1",
    "현재상태": "sheet_status",
    "오늘확인": "today_checked",
    "현재노출키워드": "exposed_keyword",
    "메모": "sheet_note",
}

# 현재상태 옆 수식 칸. 표에서는 접었다 펼 수 있다.
STATUS_SUMMARY_COLS = ["현재 검색결과", "현재 작업", "현재 노출키워드", "최근 확인", "한줄 특이사항"]
# 메모 뒤 처음수집~전체흐름. 표에서는 접었다 펼 수 있다.
FLOW_COLS = [
    "처음수집", "첫색인확인", "핵심노출", "핵심마지막", "잘림시작",
    "재수집요청최근", "재수집요청이력", "색인 소요일", "노출 유지일", "전체흐름",
]
HIDDEN_TAB_COLS = ["로그인 이메일"]

COL_CHARS = {
    "핵심키워드": 11, "로그인 이메일": 20, "계정 생성상태": 11, "마지막확인": 7, "도메인주소": 26,
    "블로그테마 주소": 14, "블로그제목(H1)": 16, "현재상태": 11, "현재 검색결과": 10, "현재 작업": 12,
    "현재 노출키워드": 11, "최근 확인": 14, "한줄 특이사항": 18, "직전상태": 10, "전전상태": 10,
    "오늘확인": 9, "현재노출키워드": 11, "메모": 16, "처음수집": 7, "첫색인확인": 8, "핵심노출": 7,
    "핵심마지막": 8, "잘림시작": 7, "재수집요청최근": 10, "재수집요청이력": 14, "색인 소요일": 8,
    "노출 유지일": 8, "전체흐름": 30, "노출이탈": 8, "생성일": 7,
    "변경일시": 18, "도메인": 26, "이전상태": 10, "변경상태/이벤트": 24,
}

# ----- 상태 ----------------------------------------------------------------
STATUS_LIST = [
    "재수집요청", "색인됨", "미색인", "색인사라짐", "POST만색인",
    "노출됨", "별도키워드노출", "잘림", "수집요청", "생성만", "삭제됨",
]
ACCOUNT_STATUS_LIST = ["생성 가능", "생성 제한 의심", "미확인"]
# 정렬에서 쓰는 키워드 우선순위 (시트 KEYWORD_PRIORITY 그대로)
KEYWORD_PRIORITY = ["카드깡", "카드현금화", "신용카드한도대출", "신용카드현금화", "소액결제현금화"]
STATUS_ORDER = ["노출됨", "별도키워드노출", "색인됨", "수집요청", "재수집요청", "POST만색인", "미색인", "색인사라짐", "잘림", "생성만"]
STATUS_RANK = {name: index + 1 for index, name in enumerate(STATUS_ORDER)}
# 프로그램이 진행 상황으로 스스로 정하는 상태. 이 상태일 때만 프로그램이 덮어쓴다.
PROGRAM_STATUSES = {"생성만", "수집요청", "재수집요청"}
# 색인 확인 결과로 넣을 수 있는 상태 (시트 API 'check')
CHECK_STATUSES = {"색인됨", "미색인", "색인사라짐", "POST만색인", "노출됨", "별도키워드노출", "잘림"}

_LEGACY = {
    "재수집": "재수집요청", "재색인": "색인됨", "재색인확인": "색인됨", "재노출": "노출됨",
    "재노출확인": "노출됨", "잘림의심": "잘림", "잘림확신": "잘림", "확인전": "생성만",
    "설정완료": "생성만",  # 예전 프로그램 상태
}

# 상태별 색 (조건부서식). (배경, 글자, 굵게)
STATUS_COLORS = {
    "재수집요청": ("#D9EAD3", None), "색인됨": ("#CFE2F3", None), "POST만색인": ("#D9D2E9", None),
    "별도키워드노출": ("#FFF2CC", None), "미색인": ("#D9D9D9", None), "색인사라짐": ("#FCE5CD", None),
    "수집요청": ("#FCE5CD", None), "생성만": (None, None), "잘림": ("#F4CCCC", "#990000"),
    "노출됨": ("#FFEB3B", None), "삭제됨": ("#D9D9D9", "#666666"),
}
# 행 전체를 칠하는 상태 (A:H, P:AC)
ROW_HIGHLIGHT = {"노출됨": ("#FFEB3B", None), "잘림": ("#F4CCCC", "#990000"), "삭제됨": ("#D9D9D9", "#666666")}
ACCOUNT_COLORS = {"생성 가능": "#D9EAD3", "생성 제한 의심": "#F4CCCC", "미확인": "#D9D9D9"}

# ----- 저장 키 ---------------------------------------------------------------
STR_FIELDS = (
    "keyword", "google_email", "account_status", "account_check", "theme_url", "h1",
    "sheet_status", "confirmed_status", "prev_status", "prev2_status", "exposed_keyword", "sheet_note",
    "first_crawl", "first_index_at", "first_core", "last_core", "trim_started_at",
    "recrawl_last", "recrawl_hist", "status_flow", "created_date", "check_ts", "last_state_time",
    "last_check", "search_result", "work",
)
BOOL_FIELDS = ("today_checked", "clip_track")
DICT_FIELDS = ("daily_confirm",)
HOME_FIELDS = STR_FIELDS + BOOL_FIELDS + DICT_FIELDS

NO_EMAIL = "이메일 없음"


def load_fields(item: dict) -> dict:
    """저장 파일에서 HOME 칸만 안전한 타입으로 꺼낸다."""
    out: dict = {}
    for key in STR_FIELDS:
        out[key] = str(item.get(key) or "")
    for key in BOOL_FIELDS:
        out[key] = bool(item.get(key)) if isinstance(item.get(key), bool) else False
    for key in DICT_FIELDS:
        out[key] = dict(item.get(key)) if isinstance(item.get(key), dict) else {}
    return out


# ----- 날짜 ----------------------------------------------------------------
def parse_day(value) -> date | None:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        return datetime.fromisoformat(text).date()
    except ValueError:
        pass
    match = re.match(r"^(\d{4})[.\-/\s]+(\d{1,2})[.\-/\s]+(\d{1,2})", text)
    if match:
        try:
            return date(int(match.group(1)), int(match.group(2)), int(match.group(3)))
        except ValueError:
            return None
    match = re.match(r"^(\d{1,2})[/.\-](\d{1,2})$", text)
    if match:
        try:
            return date(date.today().year, int(match.group(1)), int(match.group(2)))
        except ValueError:
            return None
    return None


def parse_when(value) -> datetime | None:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        day = parse_day(text)
        return datetime(day.year, day.month, day.day) if day else None


def md(value) -> str:
    """시트의 M/d 표시."""
    day = parse_day(value)
    if day is None:
        return str(value or "").strip()
    return f"{day.month}/{day.day}"


def ymd(when: datetime | date) -> str:
    return when.date().isoformat() if isinstance(when, datetime) else when.isoformat()


def md_of(when: datetime | date) -> str:
    return f"{when.month}/{when.day}"


def fmt_check(value) -> str:
    """최근 확인(L) 표시: m/d hh:mm:ss."""
    when = parse_when(value)
    if when is None:
        return ""
    return f"{when.month}/{when.day} {when:%H:%M:%S}"


def _days_between(start, end) -> str:
    a, b = parse_day(start), parse_day(end)
    if a is None or b is None:
        return ""
    return f"{(b - a).days}일"


def _sort_date_number(value) -> int:
    day = parse_day(value)
    return int(day.strftime("%Y%m%d")) if day else 99999999


# ----- 문자열 정리 -------------------------------------------------------------
def normalize_status(value) -> str:
    text = str(value or "").strip()
    return _LEGACY.get(text, text)


def normalize_keyword(value) -> str:
    text = unicodedata.normalize("NFKC", str(value or ""))
    return re.sub(r"[\s\u200B-\u200D\uFEFF]+", "", text).lower()


def normalize_domain(url) -> str:
    return str(url or "").strip().lower().rstrip("/")


def match_domain(url) -> str:
    """홈 주소를 호스트 이름으로. www.는 떼고, 경로가 있으면 호스트만."""
    raw = str(url or "").strip().lower()
    raw = re.sub(r"^https?://", "", raw)
    host = raw.split("/")[0].split("?")[0]
    return host[4:] if host.startswith("www.") else host


def clean_flow(flow: str) -> str:
    parts = [part.strip() for part in str(flow or "").split("→") if part.strip()]
    cleaned: list[str] = []
    for part in parts:
        if not cleaned or cleaned[-1] != part:
            cleaned.append(part)
    return " → ".join(cleaned)


def migrate_flow_text(flow: str) -> str:
    text = str(flow or "")
    for old, new in (("잘림의심", "잘림"), ("잘림확신", "잘림"), ("재색인확인", "색인됨"), ("재노출확인", "노출됨"), ("확인전", "생성만"), ("설정완료", "생성만")):
        text = text.replace(old, new)
    return clean_flow(text)


# ----- 요약 수식 (I:M, Z, AA, AC) ---------------------------------------------
_RESULT_BY_STATUS = {
    "삭제됨": "삭제됨", "노출됨": "핵심노출", "별도키워드노출": "부키워드노출", "색인됨": "색인만",
    "POST만색인": "POST만색인", "미색인": "미색인", "색인사라짐": "색인사라짐", "잘림": "잘림",
    "생성만": "준비중", "수집요청": "확인전",
}
_RESULT_FROM_PREV = {
    "노출됨": "핵심노출", "별도키워드노출": "부키워드노출", "색인됨": "색인만", "POST만색인": "POST만색인",
    "미색인": "미색인", "색인사라짐": "색인사라짐", "잘림": "잘림",
}
_WORK_BY_STATUS = {
    "삭제됨": "기록보관", "생성만": "준비중", "수집요청": "최초수집요청", "재수집요청": "재수집요청",
    "노출됨": "유지관찰", "별도키워드노출": "핵심노출 대기", "색인됨": "핵심노출 대기", "POST만색인": "HOME 확인",
    "미색인": "재수집 검토", "색인사라짐": "재색인 검토", "잘림": "회복 어려움·관찰",
}
_NOTE_RECRAWL = {
    "미색인": "미색인 후 재수집", "색인사라짐": "색인 복구 시도", "잘림": "잘림 후 재수집·회복 미확인",
    "부키워드노출": "부키워드→핵심 노출 시도", "색인만": "핵심키워드 노출 시도", "POST만색인": "HOME 재색인 시도",
    "핵심노출": "노출 유지 중 재수집",
}
_NOTE_BY_RESULT = {
    "핵심노출": "핵심키워드 노출", "부키워드노출": "핵심키워드 노출 대기", "색인만": "색인 완료·핵심 노출 대기",
    "POST만색인": "HOME 색인 여부 확인", "색인사라짐": "HOME 색인 재확인", "미색인": "색인 확인 필요",
    "잘림": "잘림 상태", "준비중": "설정/수집 전",
}


def search_result(status: str, prev: str) -> str:
    status, prev = normalize_status(status), normalize_status(prev)
    if status == "재수집요청":
        return _RESULT_FROM_PREV.get(prev, "확인전") if prev else "확인전"
    return _RESULT_BY_STATUS.get(status, "확인전")


def work_label(status: str) -> str:
    return _WORK_BY_STATUS.get(normalize_status(status), "관찰중")


def note_label(status: str, result: str) -> str:
    status = normalize_status(status)
    if status == "삭제됨":
        return "삭제 확인·기록 보관"
    if status == "재수집요청":
        return _NOTE_RECRAWL.get(result, "재수집 결과 대기")
    if status == "수집요청":
        return "최초 색인 대기"
    return _NOTE_BY_RESULT.get(result, "확인 필요")


def exposure_drop(meta: dict) -> str:
    status = normalize_status(meta.get("sheet_status"))
    had = bool(meta.get("first_core") or meta.get("last_core")) or normalize_status(meta.get("prev_status")) == "노출됨" or normalize_status(meta.get("prev2_status")) == "노출됨"
    return "노출후이탈" if had and status != "노출됨" else ""


# ----- 상태 확정 --------------------------------------------------------------
def _set_if_blank(meta: dict, key: str, value: str) -> None:
    if not str(meta.get(key) or "").strip():
        meta[key] = value


def ensure_created(meta: dict, day: str) -> None:
    _set_if_blank(meta, "created_date", day)


def append_flow(meta: dict, text: str) -> bool:
    text = str(text or "").strip()
    if not text:
        return False
    old = clean_flow(meta.get("status_flow") or "")
    parts = [part.strip() for part in old.split("→") if part.strip()]
    if parts and parts[-1] == text:
        meta["status_flow"] = old
        return False
    meta["status_flow"] = f"{old} → {text}" if old else text
    return True


def append_recrawl_history(meta: dict, stamp: str) -> None:
    old = str(meta.get("recrawl_hist") or "").strip()
    parts = [part.strip() for part in re.split(r"[·,]", old) if part.strip()]
    if stamp not in parts:
        meta["recrawl_hist"] = f"{old} · {stamp}" if old else stamp


def apply_status_effects(meta: dict, state: str, when: datetime) -> None:
    today = ymd(when)
    if state == "생성만":
        ensure_created(meta, today)
        meta["exposed_keyword"] = ""
    elif state == "수집요청":
        ensure_created(meta, today)
        _set_if_blank(meta, "first_crawl", today)
        meta["exposed_keyword"] = ""
    elif state in ("미색인", "색인사라짐", "POST만색인"):
        meta["exposed_keyword"] = ""
    elif state == "재수집요청":
        meta["recrawl_last"] = today
        append_recrawl_history(meta, md_of(when))
    elif state == "색인됨":
        _set_if_blank(meta, "first_index_at", today)
        meta["exposed_keyword"] = ""
    elif state == "별도키워드노출":
        meta["clip_track"] = False
    elif state == "노출됨":
        meta["clip_track"] = False
        _set_if_blank(meta, "first_core", today)
        meta["last_core"] = today
        meta["exposed_keyword"] = str(meta.get("keyword") or "")
    elif state == "잘림":
        meta["clip_track"] = True
        _set_if_blank(meta, "trim_started_at", today)
        meta["exposed_keyword"] = ""


def has_index_history(meta: dict) -> bool:
    if str(meta.get("first_index_at") or "").strip():
        return True
    flow = str(meta.get("status_flow") or "").strip()
    if not flow:
        return False
    return any(
        part.strip().endswith((" 색인됨", " 노출됨", " 별도키워드노출"))
        for part in flow.split("→")
    )


def flow_event(meta: dict, state: str, when: datetime) -> str:
    stamp = md_of(when)
    core = str(meta.get("keyword") or "").strip()
    exposure = str(meta.get("exposed_keyword") or "").strip()
    if state == "미색인":
        return f"{stamp} 미색인 확인"
    if state == "별도키워드노출":
        return f"{stamp} {exposure} 별도키워드노출" if exposure else f"{stamp} 별도키워드노출"
    if state == "노출됨":
        return f"{stamp} {core or '핵심키워드'} 노출됨"
    return f"{stamp} {state}"


def log_event(meta: dict, state: str) -> str:
    exposure = str(meta.get("exposed_keyword") or "").strip()
    if state == "미색인":
        return "미색인 확인"
    if state == "별도키워드노출" and exposure:
        return f"별도키워드노출 · {exposure}"
    return state


def confirmed_today(meta: dict, state: str, when: datetime) -> bool:
    state = normalize_status(state)
    daily = meta.setdefault("daily_confirm", {})
    if not isinstance(daily, dict):
        daily = {}
        meta["daily_confirm"] = daily
    today = ymd(when)
    if daily.get(state) == today:
        return True
    stamp = md_of(when)
    found = False
    for raw in str(meta.get("status_flow") or "").split("→"):
        part = raw.strip()
        if not part.startswith(f"{stamp} "):
            continue
        if state == "미색인":
            found = part in (f"{stamp} 미색인 확인", f"{stamp} 미색인")
        elif state == "노출됨":
            found = part.endswith(" 노출됨") and not part.endswith(" 별도키워드노출")
        elif state == "별도키워드노출":
            found = part.endswith(" 별도키워드노출")
        else:
            found = part == f"{stamp} {state}"
        if found:
            break
    if found:
        daily[state] = today
    return found


def mark_confirmed_today(meta: dict, state: str, when: datetime) -> None:
    daily = meta.setdefault("daily_confirm", {})
    if not isinstance(daily, dict):
        daily = {}
        meta["daily_confirm"] = daily
    daily[normalize_status(state)] = ymd(when)


def make_event(meta: dict, *, blog_id: str, domain: str, old: str, event: str, when: datetime, source: str, note: str = "") -> dict:
    """변경 로그 한 줄 (AE:AK). source는 '프로그램' 또는 '수동'."""
    memo = " | ".join(part for part in (str(meta.get("sheet_note") or "").strip(), str(note or "").strip()) if part)
    return {
        "ts": when.isoformat(timespec="seconds"),
        "blog_id": blog_id,
        "email": str(meta.get("google_email") or "").strip(),
        "keyword": str(meta.get("keyword") or ""),
        "domain": domain,
        "old": old or "",
        "event": f"{event} · {source}",
        "exposure": str(meta.get("exposed_keyword") or ""),
        "memo": memo,
    }


def confirm_state(
    meta: dict,
    raw_state: str,
    when: datetime,
    *,
    blog_id: str = "",
    domain: str = "",
    source: str = "수동",
    note: str = "",
    events: list | None = None,
) -> dict:
    """시트의 confirmCurrentState_. 상태를 확정하고 날짜·흐름·로그를 남긴다.

    반환: {"ok": bool, "changed": bool, "reason": str}
    """
    state = normalize_status(raw_state)
    if state not in STATUS_LIST:
        return {"ok": False, "changed": False, "reason": "unknown_status"}
    if state == "별도키워드노출" and not str(meta.get("exposed_keyword") or "").strip():
        return {"ok": False, "changed": False, "reason": "exposure_required"}
    if state == "노출됨":
        meta["exposed_keyword"] = str(meta.get("keyword") or "")
    previous = normalize_status(meta.get("confirmed_status")) or state
    changed = previous != state
    if state in ("노출됨", "별도키워드노출") and not has_index_history(meta):
        _set_if_blank(meta, "first_index_at", ymd(when))
        if not confirmed_today(meta, "색인됨", when):
            append_flow(meta, f"{md_of(when)} 색인됨")
            if events is not None:
                events.append(make_event(meta, blog_id=blog_id, domain=domain, old=previous, event="색인됨 · 노출 확인으로 자동기록", when=when, source=source, note=note))
            mark_confirmed_today(meta, "색인됨", when)
    if changed:
        meta["prev2_status"] = str(meta.get("prev_status") or "")
        meta["prev_status"] = previous
    apply_status_effects(meta, state, when)
    if changed or not confirmed_today(meta, state, when):
        append_flow(meta, flow_event(meta, state, when))
        mark_confirmed_today(meta, state, when)
    if events is not None:
        events.append(make_event(meta, blog_id=blog_id, domain=domain, old=previous, event=log_event(meta, state), when=when, source=source, note=note))
    meta["confirmed_status"] = state
    meta["sheet_status"] = state
    meta["last_state_time"] = when.isoformat(timespec="seconds")
    meta["last_check"] = md_of(when)
    if state == "삭제됨":
        meta["exposed_keyword"] = ""
        meta["clip_track"] = False
    return {"ok": True, "changed": changed, "reason": ""}


def register_new(meta: dict, when: datetime, *, blog_id: str, domain: str, email: str, title: str, source: str = "프로그램", events: list | None = None) -> None:
    """시트의 registerNewBlogRecord_ + blog_created. 처음 본 블로그를 '생성만'으로 등록한다."""
    if email and not str(meta.get("google_email") or "").strip():
        meta["google_email"] = email
    if title and not str(meta.get("h1") or "").strip() and not str(meta.get("name") or "").strip():
        meta["h1"] = title
    status = normalize_status(meta.get("sheet_status")) or "생성만"
    if status not in STATUS_LIST:
        status = "생성만"
    meta["sheet_status"] = status
    ensure_created(meta, ymd(when))
    apply_status_effects(meta, status, when)
    append_flow(meta, f"{md_of(when)} {status}")
    if events is not None:
        events.append(make_event(meta, blog_id=blog_id, domain=domain, old="", event=f"신규등록 · {status}", when=when, source=source, note=""))
    meta["confirmed_status"] = status
    meta["last_state_time"] = when.isoformat(timespec="seconds")
    mark_confirmed_today(meta, status, when)


def pending_edit(meta: dict, new_status: str) -> str:
    """시트의 H열 직접 편집(onEdit). 확정은 오늘확인 체크 때 한다."""
    state = normalize_status(new_status)
    if state not in STATUS_LIST:
        return ""
    if not str(meta.get("confirmed_status") or "").strip():
        old = normalize_status(meta.get("sheet_status"))
        if old in STATUS_LIST:
            meta["confirmed_status"] = old
    meta["sheet_status"] = state
    return state


def index_check_state(meta: dict, indexed) -> str:
    """색인 확인 결과를 시트 상태로. 노출 상태는 색인됨으로 끌어내리지 않는다."""
    current = normalize_status(meta.get("confirmed_status") or meta.get("sheet_status"))
    if current == "삭제됨":
        return ""
    if indexed is True:
        if current in ("노출됨", "별도키워드노출", "잘림"):
            return ""
        return "색인됨"
    if indexed is False:
        if current in ("색인됨", "노출됨", "별도키워드노출", "POST만색인"):
            return "색인사라짐"
        return "미색인"
    return ""


def program_state(meta: dict, *, collected: bool, collect_count: int) -> str:
    """프로그램 진행으로 정해지는 상태. 시트에서 프로그램이 보내던 recrawl/blog_created에 해당."""
    if collected and collect_count < 1:
        collect_count = 1
    if collect_count > 1:
        return "재수집요청"
    if collected:
        return "수집요청"
    return "생성만"


def sync_account_by_email(metas: dict[str, dict], email: str, status: str, check: str) -> list[str]:
    """같은 로그인 이메일의 계정 생성상태/마지막확인을 맞춘다. 바뀐 blog_id 목록 반환."""
    email = str(email or "").strip().lower()
    changed: list[str] = []
    if not email:
        return changed
    for blog_id, meta in metas.items():
        if not isinstance(meta, dict):
            continue
        if str(meta.get("google_email") or "").strip().lower() != email:
            continue
        if meta.get("account_status") != status or meta.get("account_check") != check:
            meta["account_status"] = status
            meta["account_check"] = check
            changed.append(blog_id)
    return changed


def sync_all_accounts(metas: dict[str, dict]) -> list[str]:
    """시트의 syncAllAccountStatus_: 이메일별로 값이 있는 상태/날짜를 모아서 전부에 적용."""
    canonical: dict[str, dict] = {}
    for meta in metas.values():
        if not isinstance(meta, dict):
            continue
        email = str(meta.get("google_email") or "").strip().lower()
        if not email:
            continue
        item = canonical.setdefault(email, {"status": "", "date": ""})
        if str(meta.get("account_status") or "").strip():
            item["status"] = str(meta.get("account_status")).strip()
        if str(meta.get("account_check") or "").strip():
            item["date"] = str(meta.get("account_check")).strip()
    changed: list[str] = []
    for blog_id, meta in metas.items():
        if not isinstance(meta, dict):
            continue
        email = str(meta.get("google_email") or "").strip().lower()
        if not email:
            continue
        item = canonical.get(email) or {"status": "", "date": ""}
        if meta.get("account_status") != item["status"] or meta.get("account_check") != item["date"]:
            meta["account_status"] = item["status"]
            meta["account_check"] = item["date"]
            changed.append(blog_id)
    return changed


# ----- 표 한 줄 만들기 ---------------------------------------------------------
def pending(meta: dict) -> bool:
    """H를 바꿨지만 아직 오늘확인으로 확정하지 않은 상태."""
    confirmed = normalize_status(meta.get("confirmed_status"))
    current = normalize_status(meta.get("sheet_status"))
    return bool(current) and bool(confirmed) and current != confirmed


def today_cell(meta: dict) -> str:
    if meta.get("today_checked"):
        when = parse_when(meta.get("check_ts"))
        return f"☑ {when:%H:%M}" if when else "☑"
    return "☐ 확인필요" if pending(meta) else "☐"


def build_record(meta: dict, *, blog_id: str, address: str, title: str, last_event_ts: str = "") -> dict:
    """HOME_HEADERS 순서의 표시값 dict. 수식 칸도 여기서 계산한다."""
    status = normalize_status(meta.get("sheet_status"))
    prev = normalize_status(meta.get("prev_status"))
    result = search_result(status, prev) if address else ""
    first_crawl = str(meta.get("first_crawl") or meta.get("blog_collect_at") or meta.get("last_blog_crawl") or "")
    check = fmt_check(meta.get("check_ts")) or fmt_check(last_event_ts)
    return {
        "핵심키워드": str(meta.get("keyword") or ""),
        "로그인 이메일": str(meta.get("google_email") or ""),
        "계정 생성상태": str(meta.get("account_status") or ""),
        "마지막확인": md(meta.get("account_check")),
        "도메인주소": address,
        "블로그테마 주소": str(meta.get("theme_url") or ""),
        "블로그제목(H1)": str(meta.get("h1") or title or ""),
        "현재상태": status,
        "현재 검색결과": result,
        "현재 작업": work_label(status) if address else "",
        "현재 노출키워드": str(meta.get("exposed_keyword") or "") if address else "",
        "최근 확인": check if address else "",
        "한줄 특이사항": note_label(status, result) if address else "",
        "직전상태": prev,
        "전전상태": normalize_status(meta.get("prev2_status")),
        "오늘확인": today_cell(meta),
        "현재노출키워드": str(meta.get("exposed_keyword") or ""),
        "메모": str(meta.get("sheet_note") or ""),
        "처음수집": md(first_crawl),
        "첫색인확인": md(meta.get("first_index_at")),
        "핵심노출": md(meta.get("first_core")),
        "핵심마지막": md(meta.get("last_core")),
        "잘림시작": md(meta.get("trim_started_at")),
        "재수집요청최근": md(meta.get("recrawl_last")),
        "재수집요청이력": str(meta.get("recrawl_hist") or ""),
        "색인 소요일": _days_between(first_crawl, meta.get("first_index_at")),
        "노출 유지일": _days_between(meta.get("first_core"), meta.get("last_core")),
        "전체흐름": clean_flow(meta.get("status_flow") or ""),
        "노출이탈": exposure_drop(meta),
        "생성일": md(meta.get("created_date")),
        "_id": blog_id,
        "_first_crawl": first_crawl,
        "_first_index": str(meta.get("first_index_at") or ""),
    }


def record_values(record: dict) -> list[str]:
    return [str(record.get(name, "") or "") for name in HOME_HEADERS]


def log_values(event: dict) -> list[str]:
    when = parse_when(event.get("ts"))
    stamp = when.strftime("%Y-%m-%d %H:%M:%S") if when else str(event.get("ts") or "")
    return [stamp, str(event.get("keyword") or ""), str(event.get("domain") or ""), str(event.get("old") or ""), str(event.get("event") or ""), str(event.get("exposure") or ""), str(event.get("memo") or "")]


def row_colors(status: str) -> tuple[str | None, str | None]:
    """행 전체 색. 없으면 (None, None)."""
    return ROW_HIGHLIGHT.get(normalize_status(status), (None, None))


# ----- 정렬 / 경계 -------------------------------------------------------------
def _pad(value, width: int) -> str:
    try:
        number = int(value)
    except (TypeError, ValueError):
        number = 0
    return str(number).zfill(width)


def email_ranks(records: list[dict], saved_order: list[str] | None = None) -> list[str]:
    """이메일 등장 순서. 저장된 순서를 앞에 두고, 새 이메일은 뒤에 붙인다."""
    order: list[str] = []
    for email in list(saved_order or []):
        email = str(email or "").strip().lower()
        if email and email not in order:
            order.append(email)
    for record in records:
        email = str(record.get("로그인 이메일") or "").strip().lower()
        if email and email not in order:
            order.append(email)
    return order


def sort_records(records: list[dict], saved_email_order: list[str] | None = None, program_orders: dict[str, list[str]] | None = None) -> list[dict]:
    """시트의 sortMasterRows_ 그대로."""
    program_orders = program_orders or {}
    order = email_ranks(records, saved_email_order)
    email_rank = {email: index + 1 for index, email in enumerate(order)}
    priority = [normalize_keyword(item) for item in KEYWORD_PRIORITY]
    unknown: dict[str, int] = {}
    for record in records:
        keyword = normalize_keyword(record.get("핵심키워드"))
        if keyword and keyword not in priority and keyword not in unknown:
            unknown[keyword] = len(unknown) + 1
    programs: dict[str, dict[str, int]] = {}
    for email, domains in program_orders.items():
        programs[str(email).strip().lower()] = {match_domain(domain): index + 1 for index, domain in enumerate(domains or [])}
    keyed = []
    for index, record in enumerate(records):
        email = str(record.get("로그인 이메일") or "").strip().lower()
        keyword = normalize_keyword(record.get("핵심키워드"))
        known = priority.index(keyword) if keyword in priority else -1
        keyword_rank = known + 1 if known >= 0 else len(priority) + unknown.get(keyword, 999)
        first_crawl = _sort_date_number(record.get("_first_crawl"))
        first_index = _sort_date_number(record.get("_first_index"))
        status = normalize_status(record.get("현재상태"))
        program = programs.get(email) or {}
        rank = program.get(match_domain(record.get("도메인주소"))) if program else None
        dead = "1" if status == "삭제됨" else "0"
        key = "|".join([
            dead,
            _pad(email_rank.get(email, 9999), 4),
            _pad(rank or 999999, 6) if program else _pad(keyword_rank, 6),
            _pad(index + 1, 8) if program else _pad(first_crawl, 8),
            _pad(first_index, 8),
            _pad(STATUS_RANK.get(status, 99), 3),
            _pad(index + 1, 6),
        ])
        keyed.append((key, index, record))
    keyed.sort(key=lambda item: (item[0], item[1]))
    return [record for _key, _index, record in keyed]


def boundary_type(current: dict | None, following: dict | None) -> str:
    """current 줄 아래에 그을 선. 'email' = 굵은 선, 'keyword' = 중간 선, '' = 없음."""
    if current is None or following is None:
        return "email" if current is not None else ""
    if str(current.get("로그인 이메일") or "").strip().lower() != str(following.get("로그인 이메일") or "").strip().lower():
        return "email"
    if normalize_keyword(current.get("핵심키워드")) != normalize_keyword(following.get("핵심키워드")):
        return "keyword"
    return ""


def expire_today_checks(metas: dict[str, dict], now: datetime, hours: int = 10) -> list[str]:
    """오늘확인 체크를 10시간 뒤 자동 해제 (HOME_오늘확인10시간정리)."""
    changed: list[str] = []
    limit = hours * 3600
    for blog_id, meta in metas.items():
        if not isinstance(meta, dict) or not meta.get("today_checked"):
            continue
        when = parse_when(meta.get("check_ts"))
        if when is None or (now - when).total_seconds() >= limit:
            meta["today_checked"] = False
            meta["check_ts"] = ""
            changed.append(blog_id)
    return changed


# ----- 자가 점검 -------------------------------------------------------------
def _self_check() -> None:
    when = datetime(2026, 10, 6, 10, 30, 0)
    events: list = []
    meta = load_fields({})
    meta["keyword"] = "키워드A"
    meta["google_email"] = "a@x.com"
    register_new(meta, when, blog_id="1", domain="https://a.blogspot.com/", email="a@x.com", title="제목", events=events)
    assert meta["sheet_status"] == "생성만" and meta["created_date"] == "2026-10-06"
    assert meta["status_flow"] == "10/6 생성만" and events[-1]["event"] == "신규등록 · 생성만 · 프로그램"

    # 수집요청 → 처음수집 날짜, 흐름
    out = confirm_state(meta, "수집요청", when, blog_id="1", domain="a.blogspot.com", source="프로그램", events=events)
    assert out["ok"] and out["changed"] and meta["first_crawl"] == "2026-10-06"
    assert meta["prev_status"] == "생성만" and meta["status_flow"].endswith("10/6 수집요청")
    # 같은 날 같은 상태 반복: 흐름은 한 번만, 로그는 매번
    before = len(events)
    confirm_state(meta, "수집요청", when, blog_id="1", domain="a.blogspot.com", source="프로그램", events=events)
    assert meta["status_flow"].count("수집요청") == 1 and len(events) == before + 1

    # 노출됨: 색인 이력이 없으면 색인됨 자동 기록, Q=키워드, U/V
    later = datetime(2026, 10, 8, 9, 0, 0)
    confirm_state(meta, "노출됨", later, blog_id="1", domain="a.blogspot.com", events=events)
    assert meta["first_index_at"] == "2026-10-08" and meta["exposed_keyword"] == "키워드A"
    assert "10/8 색인됨" in meta["status_flow"] and meta["status_flow"].endswith("10/8 키워드A 노출됨")
    assert meta["first_core"] == "2026-10-08" and meta["last_core"] == "2026-10-08"
    record = build_record(meta, blog_id="1", address="https://a.blogspot.com/", title="제목")
    assert record["현재 검색결과"] == "핵심노출" and record["현재 작업"] == "유지관찰" and record["한줄 특이사항"] == "핵심키워드 노출"
    assert record["색인 소요일"] == "2일" and record["노출 유지일"] == "0일" and record["노출이탈"] == ""

    # 별도키워드노출은 노출키워드가 없으면 거부
    bad = confirm_state(load_fields({}), "별도키워드노출", when)
    assert not bad["ok"] and bad["reason"] == "exposure_required"

    # 재수집요청: X/Y, 검색결과는 직전상태 기준, 노출이탈
    confirm_state(meta, "재수집요청", datetime(2026, 10, 9, 8, 0), blog_id="1", domain="a.blogspot.com", events=events)
    record = build_record(meta, blog_id="1", address="https://a.blogspot.com/", title="제목")
    assert record["재수집요청최근"] == "10/9" and record["재수집요청이력"] == "10/9"
    assert record["현재 검색결과"] == "핵심노출" and record["한줄 특이사항"] == "노출 유지 중 재수집" and record["노출이탈"] == "노출후이탈"

    # 옛 상태 이름 정리
    assert normalize_status("잘림의심") == "잘림" and normalize_status("확인전") == "생성만" and normalize_status("설정완료") == "생성만"
    assert migrate_flow_text("10/1 확인전 → 10/2 잘림확신") == "10/1 생성만 → 10/2 잘림"

    # H 직접 편집은 확정 전 상태
    pm = load_fields({})
    pm["sheet_status"] = "색인됨"
    pending_edit(pm, "미색인")
    assert pm["confirmed_status"] == "색인됨" and pm["sheet_status"] == "미색인" and pending(pm)
    assert today_cell(pm) == "☐ 확인필요"

    # 색인 확인 결과 → 상태
    assert index_check_state({"confirmed_status": "수집요청"}, True) == "색인됨"
    assert index_check_state({"confirmed_status": "노출됨"}, True) == ""
    assert index_check_state({"confirmed_status": "색인됨"}, False) == "색인사라짐"
    assert index_check_state({"confirmed_status": "수집요청"}, False) == "미색인"
    assert index_check_state({"confirmed_status": "삭제됨"}, False) == ""

    # 정렬: 삭제됨 맨 아래, 이메일 첫 등장 순서, 프로그램 순서 우선, 없으면 키워드 우선순위
    rows = [
        {"핵심키워드": "zzz", "로그인 이메일": "b@x.com", "도메인주소": "https://b1.blogspot.com/", "현재상태": "생성만", "_first_crawl": "", "_first_index": ""},
        {"핵심키워드": KEYWORD_PRIORITY[1], "로그인 이메일": "a@x.com", "도메인주소": "https://a2.blogspot.com/", "현재상태": "색인됨", "_first_crawl": "2026-10-02", "_first_index": ""},
        {"핵심키워드": KEYWORD_PRIORITY[0], "로그인 이메일": "a@x.com", "도메인주소": "https://a1.blogspot.com/", "현재상태": "삭제됨", "_first_crawl": "2026-10-01", "_first_index": ""},
        {"핵심키워드": KEYWORD_PRIORITY[0], "로그인 이메일": "a@x.com", "도메인주소": "https://a3.blogspot.com/", "현재상태": "노출됨", "_first_crawl": "2026-10-03", "_first_index": ""},
    ]
    ordered = sort_records(rows, saved_email_order=["a@x.com"])
    assert [r["도메인주소"] for r in ordered] == ["https://a3.blogspot.com/", "https://a2.blogspot.com/", "https://b1.blogspot.com/", "https://a1.blogspot.com/"]
    ordered = sort_records(rows, saved_email_order=["a@x.com"], program_orders={"a@x.com": ["a2.blogspot.com", "a3.blogspot.com"]})
    assert [r["도메인주소"] for r in ordered][:2] == ["https://a2.blogspot.com/", "https://a3.blogspot.com/"]
    assert boundary_type(ordered[0], ordered[1]) == "keyword" and boundary_type(ordered[1], ordered[2]) == "email"

    # 계정상태 동기화
    metas = {"1": {"google_email": "A@x.com", "account_status": "생성 가능", "account_check": "2026-10-06"}, "2": {"google_email": "a@x.com"}, "3": {"google_email": "b@x.com"}}
    assert "2" in sync_all_accounts(metas) and metas["2"]["account_status"] == "생성 가능" and metas["2"]["account_check"] == "2026-10-06"

    # 10시간 자동 해제
    checks = {"1": {"today_checked": True, "check_ts": "2026-10-06T00:00:00"}, "2": {"today_checked": True, "check_ts": "2026-10-06T09:00:00"}}
    assert expire_today_checks(checks, datetime(2026, 10, 6, 10, 30)) == ["1"] and checks["2"]["today_checked"]

    assert len(record_values(record)) == len(HOME_HEADERS) and len(log_values(events[-1])) == len(LOG_HEADERS)
    assert HOME_HEADERS.index("핵심키워드") + 1 == HOME_HEADERS.index("로그인 이메일")
    assert HOME_HEADERS.index("로그인 이메일") + 1 == HOME_HEADERS.index("계정 생성상태")
    assert all(name in HOME_HEADERS for name in (*STATUS_SUMMARY_COLS, *FLOW_COLS, *HIDDEN_TAB_COLS))
    print("ok", len(events))


if __name__ == "__main__":
    _self_check()
