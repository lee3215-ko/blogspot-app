"""블로그스팟 글 작성 프로그램."""
from __future__ import annotations

import html
import json
import os
import random
import re
import shutil
import threading
import time
import tkinter as tk
import webbrowser
from datetime import datetime, timedelta
from tkinter import filedialog, font as tkfont, messagebox, ttk

from blogger_session import (
    SETTING_ITEMS,
    BlogInfo,
    BloggerSession,
    RunControl,
    SessionState,
    StopRequested,
    _exc_text,
    is_post_permalink,
    normalize_post_url,
    insert_meta_under_head,
    normalize_posts,
    posts_for_address,
)
import home_records as hr
from naver_advisor_session import NaverAdvisorSession, OwnershipPending
from naver_index_check import DEFAULT_DELAY_SEC, check_naver_index
from paths import APP_VERSION, data_path, get_app_dir, is_frozen
from sheet_sync import (
    DEFAULT_SHEET_URL,
    HEADERS,
    RECORD_FIELDS,
    STATUS_OPTIONS,
    index_status_label,
    program_row,
    pull_rows,
    push_rows,
    push_updated_rows,
    sheet_tab_url,
    spreadsheet_id,
)
from ui_theme import (
    COLORS,
    FONTS,
    HoverPopup,
    button,
    card,
    flat_button,
    frame,
    install_ctk_resize_guard,
    install_wheel_dispatch,
    label,
    light_scroll,
    pill,
    scrollable,
    set_pill_tone,
    set_resize_frozen,
    text_entry,
    tk_pill,
)

try:
    import customtkinter as ctk
except ImportError:
    ctk = None

IMAGE_EXTS = {".ico", ".jpg", ".jpeg", ".gif", ".png", ".bmp", ".tif", ".tiff", ".webp"}
# 기록 표에서 구글 이메일별로 줄 배경을 나누는 색. 이메일 탭도 같은 색을 쓴다.
RECORD_EMAIL_PALETTE = ("#eef2ff", "#ecfdf5", "#fff7ed", "#f0f9ff", "#fdf4ff", "#fef2f2", "#f7fee7", "#ecfeff")
RECORD_NO_EMAIL = hr.NO_EMAIL
HOME_STATE_FILE = "home_records.json"
SETTINGS_DONE_KEYS = {"description", "search_desc", "timezone", "robots", "headers"}
SETTINGS_FILE = "settings.json"
PROGRESS_FILE = "blog_progress.json"
BLOG_META_FILE = "blog_meta.json"
LOG_FILE = "app.log"
_LOG_MAX = 1_500_000
SETUP_KEYS = tuple(key for key, _name in SETTING_ITEMS if key not in {"collect", "collect_post"})
SETTINGS_APPLY_KEYS = ("description", "search_desc", "timezone", "robots", "headers")
FIRST_COLLECT_KEYS = ("naver_verify", "theme_head", "crawl_fast", "naver_robots", "sitemap", "collect", "collect_post")
SETTING_NAME = {key: name for key, name in SETTING_ITEMS}
RECORD_VIEW_COLS = (
    ("blog", "블로그", 160),
    ("created", "생성일", 72),
    ("keyword", "키워드", 90),
    ("settings", "설정적용", 210),
    ("collect", "최초수집", 230),
    ("index", "색인확인", 150),
    ("shown", "노출", 130),
    ("recrawl", "재수집", 90),
    ("note", "메모", 240),
)
BLOG_FILTERS = (
    ("all", "전체"),
    ("blog_pending", "블로그 미수집"),
    ("post_pending", "글 미수집"),
    ("setup_pending", "설정 미완료"),
)
_SCHEME_RE = re.compile(r"^https?://", re.I)
_BLOG_ROW_BATCH = 20
_BLOG_LOG_MAX = 400
_BLOG_POST_ADD_RE = re.compile(r"^글 (\d+)개 추가$")


def _search_compact(text: str) -> str:
    value = (text or "").strip().casefold()
    if not value:
        return ""
    value = _SCHEME_RE.sub("", value)
    value = value.split("?")[0].split("#")[0].strip().strip("/")
    if value.startswith("www."):
        value = value[4:]
    return value


def _parse_activity_log(raw) -> list[dict]:
    items: list[dict] = []
    if not isinstance(raw, list):
        return items
    for entry in raw:
        if isinstance(entry, dict):
            text = str(entry.get("text") or "").strip()
            if not text:
                continue
            items.append({"ts": str(entry.get("ts") or ""), "text": text})
        elif isinstance(entry, str) and entry.strip():
            items.append({"ts": "", "text": entry.strip()})
    return items


def _query_matches(hay: str, query: str) -> bool:
    raw = (query or "").strip().casefold()
    if not raw:
        return True
    hay = hay or ""
    if raw in hay:
        return True
    compact = _search_compact(raw)
    if compact and compact in hay:
        return True
    host = compact.split("/")[0] if compact else ""
    return bool(host) and host in hay


class BloggerApp:
    def __init__(self, root):
        self.root = root
        self.root.title(f"블로그스팟 글 작성  {APP_VERSION}")
        self.root.geometry("1280x900")
        self.root.minsize(1100, 760)
        try:
            self.root.configure(bg=COLORS["bg"])
        except Exception:
            try:
                self.root.configure(fg_color=COLORS["bg"])
            except Exception:
                pass

        self.session = BloggerSession(self.log)
        self.naver = NaverAdvisorSession(self.log)
        self._login_busy = False
        self._naver_login_busy = False
        self._post_busy = False
        self._settings_busy = False
        self._naver_busy = False
        self._create_busy = False
        self._catalog_running = False
        self._watch_id = None
        self._watch_detect_running = False
        self._after_jobs: dict[str, str] = {}
        self.blog_var = tk.StringVar(value="")
        self.favicon_var = tk.StringVar(value="")
        self.manuscript_var = tk.StringVar(value="")
        self.post_image_var = tk.StringVar(value="")
        self.blog_folder_var = tk.StringVar(value=os.path.join(get_app_dir(), "블로그"))
        self.write_count_var = tk.StringVar(value="1")
        self._blog_buttons: list = []
        self._blog_check_vars: dict[str, tk.BooleanVar] = {}
        self._blog_row_frames: dict[str, object] = {}
        self._blog_filter_btns: dict[str, object] = {}
        self._shown_blog_keys: list[tuple] = []
        self._shown_session_keys: list[tuple] = []
        self._dashboard_fp = None
        self._refreshing = False
        self._blog_filter = "all"
        self.blog_query = tk.StringVar(value="")
        self._run_control = RunControl()
        self._paused = False
        self._progress_map: dict[str, list[str]] = {}
        self._blog_meta: dict[str, dict] = {}
        self._shown_account = ""
        self.post_query = tk.StringVar(value="")
        self._dock_buttons: list = []
        self._hover = HoverPopup(self.root)
        self._code_watch_started = False
        self._code_reload_pending = False
        self._reloading = False
        self._text_cache: dict[str, str] = {}
        self._html_codes: list[dict] = [{"name": "A코드", "html": ""}]
        self._html_code_index = 0
        self.memo_var = tk.StringVar(value="")
        self.sheet_url_var = tk.StringVar(value=DEFAULT_SHEET_URL)
        self._sheet_busy = False
        self._sheet_sync_ids: set[str] = set()
        self._sheet_sync_new: set[str] = set()
        self._sheet_sync_drop: set[str] = set()
        self._sheet_sync_reason = ""
        self._sheet_sync_again = False
        self._records_rendering = False
        self._record_fp: tuple | None = None
        self._record_editor: dict | None = None
        self._record_sort: tuple[str, bool] | None = None
        self._record_click_col = 0
        self._record_mode = "main"
        self._home_state: dict = {"email_order": [], "program_order": {}, "program_order_time": {}, "events": []}
        self._memo_parts = ["", "", "", ""]
        self._index_labels: list = []
        self._blog_index_btns: list = []
        self._blog_row_sigs: dict[str, tuple] = {}
        self._post_check_vars: dict[str, tk.BooleanVar] = {}
        self._blog_pending_rows: list[BlogInfo] = []
        self._blog_log_win = None
        self._blog_log_blog_id = ""

        self._build()
        self._load_local_settings()
        self._bind_copy_shortcuts()
        self._refresh_dashboard()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(80, self._fit_window)
        self.root.after(400, self._restore_naver_if_open)
        self.root.after(500, self._restore_blogger_if_open)
        self.root.after(900, self._start_code_watch)

    def _ensure_write_folders(self) -> None:
        if not hasattr(self, "manuscript_var"):
            self.manuscript_var = tk.StringVar(value="")
        if not hasattr(self, "post_image_var"):
            self.post_image_var = tk.StringVar(value="")
        if not hasattr(self, "write_count_var"):
            self.write_count_var = tk.StringVar(value="1")
        if not hasattr(self, "blog_folder_var"):
            self.blog_folder_var = tk.StringVar(value=os.path.join(get_app_dir(), "블로그"))
        if self.manuscript_var.get().strip() or self.post_image_var.get().strip():
            return
        path = data_path(SETTINGS_FILE)
        if not os.path.isfile(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                data = json.load(handle)
        except Exception:
            return
        if not self.manuscript_var.get().strip():
            self.manuscript_var.set(str(data.get("manuscript_folder") or ""))
        if not self.post_image_var.get().strip():
            self.post_image_var.set(str(data.get("post_image_folder") or ""))
        if hasattr(self, "write_count_var") and not str(self.write_count_var.get() or "").strip():
            saved_count = str(data.get("write_count") or "").strip()
            self.write_count_var.set(saved_count if saved_count.isdigit() else "1")

    # ----- 타이머 / 이벤트 뼈대 -------------------------------------------------
    # 디바운스용 after는 전부 이름을 붙여 여기로 모은다. 화면을 다시 만들 때 한 번에 취소할 수 있고,
    # 같은 이름을 다시 걸면 이전 것이 자동으로 취소되므로 중복 실행이 생기지 않는다.

    def _after_once(self, key: str, ms: int, fn) -> None:
        jobs = self.__dict__.setdefault("_after_jobs", {})
        old = jobs.pop(key, None)
        if old is not None:
            try:
                self.root.after_cancel(old)
            except Exception:
                pass

        def run():
            jobs.pop(key, None)
            fn()

        try:
            jobs[key] = self.root.after(max(0, int(ms)), run)
        except Exception:
            pass

    def _cancel_after(self, key: str) -> None:
        jobs = self.__dict__.setdefault("_after_jobs", {})
        old = jobs.pop(key, None)
        if old is not None:
            try:
                self.root.after_cancel(old)
            except Exception:
                pass

    def _cancel_all_afters(self) -> None:
        jobs = self.__dict__.setdefault("_after_jobs", {})
        for key in list(jobs):
            self._cancel_after(key)

    def _trace_var(self, var, fn) -> None:
        """우리가 건 추적만 기록해 둔다. CTkEntry가 textvariable에 거는 내부 추적은 건드리지 않는다."""
        ids = self.__dict__.setdefault("_var_trace_ids", [])
        try:
            ids.append((var, var.trace_add("write", fn)))
        except Exception:
            pass

    def _bind_var_traces(self) -> None:
        """StringVar는 화면을 다시 만들어도 살아 있으므로, 우리 추적은 지우고 다시 건다."""
        self._clear_input_traces()
        self._trace_var(self.memo_var, lambda *_: self._schedule_memo_refresh())
        self._trace_var(self.write_count_var, lambda *_: self._schedule_write_count())
        self._trace_var(self.blog_query, self._on_blog_query_changed)
        self._trace_var(self.post_query, self._on_post_query_changed)

    def _build(self):
        self._install_centered_dialogs()
        self._ensure_write_folders()
        install_ctk_resize_guard()
        install_wheel_dispatch(self.root, on_wheel=self._hover.hide)
        self._bind_var_traces()
        shell = frame(self.root, COLORS["bg"])
        shell.pack(fill=tk.BOTH, expand=True, padx=20, pady=16)
        self._outer = shell

        header = frame(shell, COLORS["bg"])
        header.pack(fill=tk.X, pady=(0, 10))
        title_wrap = frame(header, COLORS["bg"])
        title_wrap.pack(side=tk.LEFT, fill=tk.X, expand=True)
        title_row = frame(title_wrap, COLORS["bg"])
        title_row.pack(fill=tk.X)
        label(title_row, "블로그스팟", "title").pack(side=tk.LEFT, padx=(0, 14))
        label(title_row, "계정 메모", "small", COLORS["text_muted"]).pack(side=tk.LEFT, padx=(0, 6))
        self.memo_entry = text_entry(title_row, textvariable=self.memo_var)
        self.memo_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        self.memo_copy_row = frame(title_row, COLORS["bg"])
        self.memo_copy_row.pack(side=tk.LEFT)
        self._memo_copy_btns = []
        for index, title in enumerate(("이메일", "아이디", "비번", "이름")):
            btn = button(
                self.memo_copy_row,
                title,
                variant="ghost",
                width=78,
                height=32,
                command=lambda pick=index: self._copy_memo_index(pick),
            )
            btn.pack(side=tk.LEFT, padx=(0, 4))
            self._memo_copy_btns.append(btn)
        self.status_label = label(title_wrap, "로그인 전", "body_bold", COLORS["text"])
        self.status_label.pack(anchor="w", pady=(2, 0))
        self.account_label = label(title_wrap, "계정: -", "body", COLORS["text_muted"])
        self.account_label.pack(anchor="w")

        login_wrap = frame(header, COLORS["bg"])
        login_wrap.pack(side=tk.RIGHT, padx=(12, 0))
        self.naver_status_label = label(
            login_wrap, "서치어드바이저: 로그인 전", "small", COLORS["text_muted"]
        )
        self.naver_status_label.pack(anchor="e", pady=(0, 4))
        self.naver_count_label = label(login_wrap, "", "small", COLORS["text_muted"])
        self.naver_count_label.pack(anchor="e", pady=(0, 6))
        login_btns = frame(login_wrap, COLORS["bg"])
        login_btns.pack(anchor="e")
        self.naver_login_btn = button(
            login_btns,
            "서치어드바이저 로그인",
            variant="ghost",
            width=180,
            command=self.on_naver_login,
        )
        self.naver_login_btn.pack(side=tk.RIGHT)
        self.login_btn = button(
            login_btns,
            "블로그스팟 로그인",
            variant="primary",
            width=170,
            command=self.on_login,
        )
        self.login_btn.pack(side=tk.RIGHT, padx=(0, 8))

        dock = card(shell)
        dock.pack(side=tk.BOTTOM, fill=tk.X, pady=(8, 0))
        dock_inner = frame(dock, COLORS["card"])
        dock_inner.pack(fill=tk.X, padx=12, pady=10)
        label(dock_inner, "작업", "subheading", COLORS["text"]).pack(anchor="w")
        self.action_host = frame(dock_inner, COLORS["card"])
        self.action_host.pack(fill=tk.X, pady=(6, 0))
        self.action_host.configure(height=96)
        try:
            self.action_host.pack_propagate(False)
        except Exception:
            pass
        self._dock_buttons = [
            button(self.action_host, "설정 적용", variant="warning", width=130, height=40, command=self.on_apply_settings),
            button(self.action_host, "최초코드", variant="primary", width=110, height=40, command=self.on_naver_html_insert),
            button(self.action_host, "글작성", variant="success", width=100, height=40, command=self.on_write_post),
            button(self.action_host, "최초 수집", variant="success", width=120, height=40, command=self.on_naver_first_setup),
            button(self.action_host, "블로그 생성", variant="primary", width=130, height=40, command=self.on_create_blogs),
            button(self.action_host, "일시정지", variant="ghost", width=100, height=40, command=self.on_toggle_pause),
            button(self.action_host, "정지", variant="danger", width=80, height=40, command=self.on_stop_settings),
        ]
        (
            self.settings_btn,
            self.naver_html_btn,
            self.post_btn,
            self.naver_first_btn,
            self.create_blogs_btn,
            self.pause_btn,
            self.stop_btn,
        ) = self._dock_buttons
        self.action_host.bind("<Configure>", lambda _e: self._after_once("dock_layout", 40, self._layout_dock))
        self.root.after(60, self._layout_dock)
        self._set_run_controls(False)
        self.progress_label = label(dock_inner, "대기 중", "body", COLORS["text_muted"])
        self.progress_label.pack(anchor="w", pady=(8, 4))
        self.progress_bar = ttk.Progressbar(dock_inner, maximum=100, mode="determinate")
        self.progress_bar.pack(fill=tk.X)

        self.tab_bar = frame(shell, COLORS["bg"])
        self.tab_bar.pack(fill=tk.X, pady=(0, 8))
        self.tab_bar.configure(height=44)
        try:
            self.tab_bar.pack_propagate(False)
        except Exception:
            pass
        self._main_tab = "블로그"
        self._main_tab_buttons = {}
        for name, width in (
            ("블로그", 110),
            ("만들기", 110),
            ("HTML 편집", 130),
            ("색인 확인", 120),
            ("로그", 90),
        ):
            btn = button(
                self.tab_bar,
                name,
                variant="ghost",
                width=width,
                height=36,
                command=lambda n=name: self._show_main_tab(n),
            )
            self._main_tab_buttons[name] = btn
        self.tab_bar.bind("<Configure>", lambda _e: self._after_once("tab_layout", 40, self._layout_tabs))
        self.root.after(70, self._layout_tabs)

        self.tab_body = frame(shell, COLORS["bg"])
        self.tab_body.pack(fill=tk.BOTH, expand=True)
        try:
            self.tab_body.pack_propagate(False)
        except Exception:
            pass
        self._resize_filler = frame(shell, COLORS["bg"])
        self._ui_ready = False
        self._resize_frozen = False
        self._root_size = (0, 0)
        self._main_pages = {}
        self._build_write_page()

        body = frame(self.tab_body, COLORS["bg"])
        self._main_pages["블로그"] = body
        body.grid_columnconfigure(0, weight=2, minsize=420)
        body.grid_columnconfigure(1, weight=3, minsize=460)
        body.grid_rowconfigure(0, weight=1)

        blog_card = card(body)
        blog_card.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        blog_inner = frame(blog_card, COLORS["card"])
        blog_inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
        self.blog_heading = label(blog_inner, "블로그", "heading", COLORS["text"])
        head_row = frame(blog_inner, COLORS["card"])
        head_row.pack(fill=tk.X)
        self.blog_heading.pack(in_=head_row, side=tk.LEFT)
        self.blog_summary = frame(head_row, COLORS["card"])
        self.blog_summary.pack(side=tk.LEFT, padx=(10, 0))
        self.blog_log_btn = button(
            head_row, "블로그 로그", variant="ghost", width=96, height=28, command=self.on_blog_log,
        )
        self.blog_log_btn.pack(side=tk.RIGHT)
        self.blog_search = text_entry(blog_inner, textvariable=self.blog_query)
        self.blog_search.pack(fill=tk.X, pady=(8, 0))

        filter_wrap = frame(blog_inner, COLORS["card"])
        filter_wrap.pack(fill=tk.X, pady=(8, 0))
        filter_sizes = {
            "all": 58,
            "blog_pending": 102,
            "post_pending": 84,
            "setup_pending": 92,
        }
        for key, title in BLOG_FILTERS:
            btn = button(
                filter_wrap,
                title,
                variant="ghost",
                width=filter_sizes.get(key, 80),
                height=28,
                command=lambda k=key: self._set_blog_filter(k),
            )
            btn.pack(side=tk.LEFT, padx=(0, 4), pady=(0, 4))
            self._blog_filter_btns[key] = btn
        self._paint_filter_btns()
        tool_wrap = frame(blog_inner, COLORS["card"])
        tool_wrap.pack(fill=tk.X, pady=(0, 6))
        self.sel_count_label = label(tool_wrap, "0개 선택", "small", COLORS["accent"])
        self.sel_count_label.pack(side=tk.LEFT, padx=(0, 8))
        self.select_all_btn = button(
            tool_wrap, "전체 선택", variant="ghost", width=76, height=28,
            command=lambda: self._set_visible_checks(True),
        )
        self.select_all_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.select_none_btn = button(
            tool_wrap, "선택 해제", variant="ghost", width=76, height=28,
            command=lambda: self._set_visible_checks(False),
        )
        self.select_none_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.blog_recrawl_btn = button(
            tool_wrap,
            "블로그 재수집",
            variant="primary",
            width=100,
            height=28,
            command=self.on_naver_blog_recrawl,
        )
        self.blog_recrawl_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.blog_delete_btn = button(
            tool_wrap,
            "블로그 삭제",
            variant="danger",
            width=92,
            height=28,
            command=self.on_delete_blogs,
        )
        self.blog_delete_btn.pack(side=tk.LEFT, padx=(0, 4))

        self.blog_list = scrollable(blog_inner, height=420, bg=COLORS["card"])
        self.blog_list.pack(fill=tk.BOTH, expand=True)
        self._blog_list_inner = tk.Frame(self.blog_list.inner, bg=COLORS["card"])
        self._blog_list_inner.pack(fill=tk.X)

        right_card = card(body)
        right_card.grid(row=0, column=1, sticky="nsew")
        right = frame(right_card, COLORS["card"])
        right.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
        self.posts_heading = label(right, "글", "heading", COLORS["text"])
        self.posts_heading.pack(anchor="w")
        self.posts_meta = label(
            right,
            "블로그를 누르면 글을 봅니다. 더블클릭하면 로그인된 크롬의 새 탭에서 글 목록이 열립니다.",
            "small",
            COLORS["text_muted"],
            wraplength=640,
            justify="left",
        )
        self.posts_meta.pack(anchor="w", pady=(4, 0))
        self.post_search = text_entry(right, textvariable=self.post_query)
        self.post_search.pack(fill=tk.X, pady=(8, 0))
        post_tools = frame(right, COLORS["card"])
        post_tools.pack(fill=tk.X, pady=(8, 0))
        self.post_sel_count_label = label(post_tools, "0개 선택", "small", COLORS["accent"])
        self.post_sel_count_label.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 4))
        self.post_select_all_btn = button(
            post_tools, "전체 선택", variant="ghost", width=76, height=28,
            command=lambda: self._set_visible_post_checks(True),
        )
        self.post_select_all_btn.pack(side=tk.LEFT, padx=(0, 4), pady=(0, 4))
        self.post_select_none_btn = button(
            post_tools, "선택 해제", variant="ghost", width=76, height=28,
            command=lambda: self._set_visible_post_checks(False),
        )
        self.post_select_none_btn.pack(side=tk.LEFT, padx=(0, 4), pady=(0, 4))
        self.post_recrawl_btn = button(
            post_tools, "선택 글 재수집", variant="primary", width=120, height=28,
            command=self.on_recrawl_selected_posts,
        )
        self.post_recrawl_btn.pack(side=tk.LEFT, padx=(0, 4), pady=(0, 4))

        self.posts_list = scrollable(right, height=420, bg=COLORS["card"])
        self.posts_list.pack(fill=tk.BOTH, expand=True, pady=(8, 0))
        self.blog_detail_wrap = tk.Frame(self.posts_list.inner, bg=COLORS["card"])
        self.blog_detail_wrap.pack(fill=tk.X)

        setup_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["만들기"] = setup_page
        setup_card = card(setup_page)
        setup_card.pack(fill=tk.BOTH, expand=True)
        setup_scroll = scrollable(setup_card, 420, COLORS["card"])
        setup_scroll.pack(fill=tk.BOTH, expand=True)
        setup_inner = setup_scroll.inner
        label(setup_inner, "블로그 생성", "heading", COLORS["text"]).pack(anchor="w", padx=16, pady=(16, 0))
        label(
            setup_inner,
            "블로그를 고르지 않습니다. 제목을 한 줄에 하나씩 적으면 위에서부터 새 블로그를 만듭니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", padx=16, pady=(4, 8))
        self.create_titles = tk.Text(
            setup_inner, height=8, font=FONTS["body"], wrap=tk.WORD,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"],
        )
        self.create_titles.pack(fill=tk.X, padx=16)
        self.create_side_btn = button(
            setup_inner, "이 제목으로 생성", variant="primary", width=180, height=40, command=self.on_create_blogs,
        )
        self.create_side_btn.pack(anchor="w", padx=16, pady=(10, 0))

        label(setup_inner, "디스크립션", "heading", COLORS["text"]).pack(anchor="w", padx=16, pady=(18, 0))
        label(
            setup_inner,
            "블로그마다 따로 적지 않습니다. 문장을 한 줄에 하나씩 모아 두면, 설정 적용 때 그중에서 넣습니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", padx=16, pady=(4, 8))
        self.desc_text = tk.Text(
            setup_inner, height=8, font=FONTS["body"], wrap=tk.WORD,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"],
        )
        self.desc_text.pack(fill=tk.X, padx=16)
        if hasattr(self, "_bind_text_cache"):
            self._bind_text_cache(self.create_titles, "create")
            self._bind_text_cache(self.desc_text, "desc")

        label(setup_inner, "블로그 폴더", "subheading", COLORS["text"]).pack(anchor="w", padx=16, pady=(18, 0))
        label(
            setup_inner,
            "블로그가 만들어지면 주소 이름으로 이 폴더 안에 폴더를 만듭니다. 경로 복사는 블로그 목록 옆에 있습니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", padx=16, pady=(4, 8))
        folder_row = frame(setup_inner, COLORS["card"])
        folder_row.pack(fill=tk.X, padx=16, pady=(0, 4))
        self.blog_folder_entry = text_entry(folder_row, textvariable=self.blog_folder_var)
        self.blog_folder_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        button(
            folder_row, "폴더 선택", variant="primary", width=120, height=40, command=self.on_pick_blog_folder,
        ).pack(side=tk.LEFT, padx=(8, 0))

        label(setup_inner, "파비콘", "heading", COLORS["text"]).pack(anchor="w", padx=16, pady=(18, 0))
        label(
            setup_inner,
            "블로그를 고른 뒤 지정하는 항목이 아닙니다. 폴더만 정해 두면 설정 적용 때 그 폴더의 이미지를 넣습니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", padx=16, pady=(4, 8))
        fav_row = frame(setup_inner, COLORS["card"])
        fav_row.pack(fill=tk.X, padx=16, pady=(0, 16))
        self.favicon_entry = text_entry(fav_row, textvariable=self.favicon_var)
        self.favicon_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.folder_btn = button(fav_row, "폴더 선택", variant="primary", width=120, height=40, command=self.on_pick_folder)
        self.folder_btn.pack(side=tk.LEFT, padx=(8, 0))

        html_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["HTML 편집"] = html_page
        html_card = card(html_page)
        html_card.pack(fill=tk.BOTH, expand=True)
        html_inner = frame(html_card, COLORS["card"])
        html_inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=16)
        label(html_inner, "HTML 편집", "heading", COLORS["text"]).pack(anchor="w")
        label(
            html_inner,
            "코드를 여러 개 저장할 수 있습니다. 탭을 더블클릭하면 이름을 바꿀 수 있고, 바꾼 이름은 블로그 기록에도 반영됩니다. 선택한 코드만 네이버 최초 HTML 코드 넣기에 사용합니다.",
            "body",
            COLORS["text_muted"],
            wraplength=720,
            justify="left",
        ).pack(anchor="w", pady=(4, 8))
        code_bar = frame(html_inner, COLORS["card"])
        code_bar.pack(fill=tk.X, pady=(0, 8))
        self.html_del_btn = button(
            code_bar, "코드 삭제", variant="danger", width=100, height=36, command=self.on_delete_html_code,
        )
        self.html_del_btn.pack(side=tk.RIGHT)
        self.html_add_btn = button(
            code_bar, "코드 추가", variant="primary", width=100, height=36, command=self.on_add_html_code,
        )
        self.html_add_btn.pack(side=tk.RIGHT, padx=(0, 6))
        self.html_code_list = scrollable(code_bar, 44, COLORS["card"], orientation="horizontal")
        self.html_code_list.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        if not isinstance(getattr(self, "_html_codes", None), list) or not self._html_codes:
            self._html_codes = [{"name": "A코드", "html": ""}]
            self._html_code_index = 0
        self._render_html_code_buttons()
        self.theme_html = tk.Text(
            html_inner, font=FONTS["log"], wrap=tk.WORD,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"],
        )
        self.theme_html.pack(fill=tk.BOTH, expand=True)
        self._load_html_editor()

        log_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["로그"] = log_page
        log_card = card(log_page)
        log_card.pack(fill=tk.BOTH, expand=True)
        log_inner = frame(log_card, COLORS["card"])
        log_inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        label(log_inner, "로그", "heading", COLORS["text"]).pack(anchor="w", pady=(0, 8))
        self.log_box = tk.Text(
            log_inner, font=FONTS["log"],
            bg=COLORS["log_bg"], fg=COLORS["log_fg"], wrap=tk.WORD,
            relief="flat", highlightthickness=0,
        )
        self.log_box.pack(fill=tk.BOTH, expand=True)
        self.log_box.configure(state=tk.DISABLED)
        self._close_record_ui()
        self._build_index_page()
        self._show_main_tab("블로그")
        self._fit_window()
        self._bind_copy_shortcuts()
        try:
            self.root.unbind("<Configure>")
        except Exception:
            pass
        self.root.bind("<Configure>", self._on_root_configured)
        self._after_once("resize_guard", 400, self._enable_resize_guard)

    def _enable_resize_guard(self) -> None:
        try:
            self._root_size = (int(self.root.winfo_width()), int(self.root.winfo_height()))
        except Exception:
            self._root_size = (0, 0)
        self._ui_ready = True

    def _on_root_configured(self, event) -> None:
        if getattr(event, "widget", None) is not self.root:
            return
        hover = getattr(self, "_hover", None)
        if hover is not None:
            hover.hide()
        if not getattr(self, "_ui_ready", False) or getattr(self, "_reloading", False):
            return
        try:
            width = int(event.width)
            height = int(event.height)
        except Exception:
            return
        prev_w, prev_h = getattr(self, "_root_size", (0, 0))
        self._root_size = (width, height)
        if time.monotonic() < float(getattr(self, "_resize_ignore_until", 0) or 0):
            return
        if prev_w <= 1 or prev_h <= 1:
            return
        if width == prev_w and height == prev_h:
            return
        self._freeze_for_resize()
        self._after_once("resize_thaw", 120, self._thaw_after_resize)

    def _freeze_for_resize(self) -> None:
        if getattr(self, "_resize_frozen", False):
            return
        body = getattr(self, "tab_body", None)
        filler = getattr(self, "_resize_filler", None)
        if not self._widget_alive(body) or not self._widget_alive(filler):
            return
        self._resize_frozen = True
        set_resize_frozen(True)
        try:
            body.pack_forget()
        except Exception:
            pass
        try:
            filler.pack(fill=tk.BOTH, expand=True)
        except Exception:
            pass

    def _thaw_after_resize(self) -> None:
        if not getattr(self, "_resize_frozen", False):
            return
        filler = getattr(self, "_resize_filler", None)
        body = getattr(self, "tab_body", None)
        try:
            if self._widget_alive(filler):
                filler.pack_forget()
        except Exception:
            pass
        try:
            if self._widget_alive(body):
                body.pack(fill=tk.BOTH, expand=True)
        except Exception:
            pass
        self._resize_frozen = False
        set_resize_frozen(False)
        self._resize_ignore_until = time.monotonic() + 0.25
        page = (getattr(self, "_main_pages", {}) or {}).get(getattr(self, "_main_tab", ""))
        if self._widget_alive(page):
            self._map_only_tab(page)
        self._layout_dock()
        self._layout_tabs()
        try:
            self.root.after_idle(self._commit_visible_scrolls)
        except Exception:
            self._commit_visible_scrolls()

    def _commit_visible_scrolls(self, widget=None) -> None:
        node = widget
        if node is None:
            node = getattr(self, "tab_body", None)
        if not self._widget_alive(node):
            return
        if hasattr(node, "_commit_span") and hasattr(node, "inner"):
            try:
                node._commit_span()
            except Exception:
                pass
            return
        try:
            children = list(node.winfo_children())
        except Exception:
            return
        for child in children:
            self._commit_visible_scrolls(child)

    def _install_drag_hook(self) -> None:
        self._remove_drag_hook()

    def _remove_drag_hook(self) -> None:
        self._drag_hooked = False
        self._drag_proc = None
        self._drag_old_proc = None
        self._drag_hwnd = None

    def _layout_dock(self, _event=None) -> None:
        if getattr(self, "_resize_frozen", False):
            return
        host = getattr(self, "action_host", None)
        if host is None or getattr(self, "_dock_layouting", False):
            return
        self._dock_layouting = True
        try:
            self._layout_dock_body(host)
        finally:
            self._dock_layouting = False

    def _layout_dock_body(self, host) -> None:
        width = host.winfo_width()
        if width < 80:
            return
        if abs(width - int(getattr(self, "_dock_width", 0) or 0)) < 12:
            return
        self._dock_width = width
        x = 0
        y = 0
        row_h = 0
        for btn in self._dock_buttons:
            try:
                req_w = int(btn.cget("width"))
            except Exception:
                req_w = 140
            req_h = 40
            if x and x + req_w > width:
                x = 0
                y += row_h + 8
                row_h = 0
            btn.place(x=x, y=y)
            x += req_w + 8
            row_h = max(row_h, req_h)
        total = max(48, y + row_h + 2)
        if abs(host.winfo_height() - total) > 2:
            host.configure(height=total)

    def _layout_tabs(self, _event=None) -> None:
        if getattr(self, "_resize_frozen", False):
            return
        host = getattr(self, "tab_bar", None)
        if host is None or getattr(self, "_tab_layouting", False):
            return
        self._tab_layouting = True
        try:
            self._layout_tabs_body(host)
        finally:
            self._tab_layouting = False

    def _layout_tabs_body(self, host) -> None:
        width = host.winfo_width()
        if width < 80:
            return
        if abs(width - int(getattr(self, "_tab_width", 0) or 0)) < 12:
            return
        self._tab_width = width
        x = 0
        y = 0
        row_h = 0
        for btn in self._main_tab_buttons.values():
            try:
                req_w = int(btn.cget("width"))
            except Exception:
                req_w = 120
            req_h = 36
            if x and x + req_w > width:
                x = 0
                y += row_h + 6
                row_h = 0
            btn.place(x=x, y=y)
            x += req_w + 8
            row_h = max(row_h, req_h)
        total = max(40, y + row_h + 2)
        if abs(host.winfo_height() - total) > 2:
            host.configure(height=total)

    def _build_write_page(self) -> None:
        old = self._main_pages.get("글쓰기")
        if self._widget_alive(old):
            try:
                old.destroy()
            except Exception:
                pass
        write_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["글쓰기"] = write_page
        write_card = card(write_page)
        write_card.pack(fill=tk.BOTH, expand=True)
        write_inner = frame(write_card, COLORS["card"])
        write_inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=16)
        label(write_inner, "글쓰기", "heading", COLORS["text"]).pack(anchor="w")
        self.write_count_label = label(
            write_inner,
            "작성할 글 0개",
            "subheading",
            COLORS["accent"],
            wraplength=720,
            anchor="w",
            justify="left",
        )
        self.write_count_label.pack(anchor="w", fill=tk.X, pady=(6, 0))
        count_row = frame(write_inner, COLORS["card"])
        count_row.pack(fill=tk.X, pady=(8, 0))
        label(count_row, "작성할 글 개수", "subheading", COLORS["text"]).pack(side=tk.LEFT)
        self.write_count_entry = text_entry(count_row, textvariable=self.write_count_var, width=8)
        self.write_count_entry.pack(side=tk.LEFT, padx=(8, 0))
        label(
            write_inner,
            "체크한 블로그가 있으면 그 블로그에, 없으면 목록에서 누른 블로그에 글을 씁니다. 위에 적은 개수만큼만 쓰고, 블로그가 여러 개면 고른 순서대로 돌아가며 넣습니다. 제목은 txt 파일 이름입니다. 발행되면 원고 폴더 안의 성공 폴더로 옮깁니다.",
            "body",
            COLORS["text_muted"],
            wraplength=720,
            anchor="w",
            justify="left",
        ).pack(anchor="w", fill=tk.X, pady=(4, 12))
        label(write_inner, "원고 폴더", "subheading", COLORS["text"]).pack(anchor="w")
        manuscript_row = frame(write_inner, COLORS["card"])
        manuscript_row.pack(fill=tk.X, pady=(4, 12))
        self.manuscript_entry = text_entry(manuscript_row, textvariable=self.manuscript_var)
        self.manuscript_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.manuscript_folder_btn = button(
            manuscript_row, "폴더 선택", variant="primary", width=120, height=40, command=self.on_pick_manuscript_folder,
        )
        self.manuscript_folder_btn.pack(side=tk.LEFT, padx=(8, 0))
        label(write_inner, "이미지 폴더", "subheading", COLORS["text"]).pack(anchor="w")
        image_row = frame(write_inner, COLORS["card"])
        image_row.pack(fill=tk.X, pady=(4, 0))
        self.post_image_entry = text_entry(image_row, textvariable=self.post_image_var)
        self.post_image_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.post_image_folder_btn = button(
            image_row, "폴더 선택", variant="primary", width=120, height=40, command=self.on_pick_post_image_folder,
        )
        self.post_image_folder_btn.pack(side=tk.LEFT, padx=(8, 0))
        label(
            write_inner,
            "이미지는 이 폴더에서 글을 쓸 때마다 하나를 골라 본문 앞에 넣습니다. 폴더를 비워 두면 원고만 넣습니다. 글 작성 버튼은 아래 작업 줄에 있습니다.",
            "body",
            COLORS["text_muted"],
            wraplength=720,
            anchor="w",
            justify="left",
        ).pack(anchor="w", fill=tk.X, pady=(12, 0))
        self._refresh_write_count()

    def _build_index_page(self) -> None:
        page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["색인 확인"] = page
        card_wrap = card(page)
        card_wrap.pack(fill=tk.BOTH, expand=True)
        inner = frame(card_wrap, COLORS["card"])
        inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
        label(inner, "색인 확인", "heading", COLORS["text"]).pack(anchor="w")
        label(
            inner,
            "등록된 블로그를 네이버 site: 검색으로 확인합니다. 로그인은 필요 없습니다. 블로그를 삭제하면 이 목록에서도 빠집니다.",
            "body",
            COLORS["text_muted"],
            wraplength=980,
            justify="left",
        ).pack(anchor="w", pady=(4, 8))
        self.index_summary = label(inner, "블로그 0개", "small", COLORS["text_muted"])
        self.index_summary.pack(anchor="w")
        if not isinstance(getattr(self, "index_query", None), tk.StringVar):
            self.index_query = tk.StringVar(value="")
        self.index_search = text_entry(inner, textvariable=self.index_query)
        self.index_search.pack(fill=tk.X, pady=(8, 0))
        self._trace_var(self.index_query, self._on_index_query_changed)
        actions = frame(inner, COLORS["card"])
        actions.pack(fill=tk.X, pady=(8, 0))
        self.index_check_btn = button(
            actions, "색인 확인", variant="primary", width=110, height=36, command=lambda: self.on_index_check(False),
        )
        self.index_check_btn.pack(side=tk.LEFT, padx=(0, 6))
        self.index_recheck_btn = button(
            actions, "다시 확인", variant="ghost", width=100, height=36, command=lambda: self.on_index_check(True),
        )
        self.index_recheck_btn.pack(side=tk.LEFT, padx=(0, 6))
        self.index_stop_btn = button(
            actions, "중지", variant="danger", width=70, height=36, command=self.on_index_stop,
        )
        self.index_stop_btn.pack(side=tk.LEFT)
        self.index_stop_btn.configure(state="disabled")
        self.index_progress = label(inner, "대기 중", "small", COLORS["text_muted"])
        self.index_progress.pack(anchor="w", pady=(8, 0))
        self.index_list = light_scroll(inner, height=420, bg=COLORS["card"])
        self.index_list.pack(fill=tk.BOTH, expand=True, pady=(8, 0))
        host = getattr(self.index_list, "inner", self.index_list)
        self._index_list_inner = tk.Frame(host, bg=COLORS["card"])
        self._index_list_inner.pack(fill=tk.X)
        self._index_row_frames = {}
        self._index_fp = None
        self._index_vis_query = None
        self._listed_index_blogs = []

    def _set_index_progress(self, text: str) -> None:
        label_widget = getattr(self, "index_progress", None)
        if self._widget_alive(label_widget):
            label_widget.configure(text=text)

    def _set_index_buttons(self, running: bool) -> None:
        for widget, enabled in (
            (getattr(self, "index_check_btn", None), not running),
            (getattr(self, "index_recheck_btn", None), not running),
            (getattr(self, "index_stop_btn", None), running),
        ):
            if self._widget_alive(widget):
                widget.configure(state="normal" if enabled else "disabled")
        for widget in list(getattr(self, "_blog_index_btns", []) or []):
            if self._widget_alive(widget):
                try:
                    widget.configure(state="disabled" if running else "normal")
                except Exception:
                    pass

    def _index_fingerprint(self, blogs: list[BlogInfo]) -> tuple:
        rows = []
        for blog in blogs:
            meta = self._blog_meta.get(blog.id) or {}
            rows.append(
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    meta.get("naver_indexed", None),
                    str(meta.get("naver_index_checked_at") or ""),
                    str(meta.get("naver_index_message") or ""),
                    str(meta.get("naver_index_sample") or ""),
                )
            )
        return tuple(rows)

    def _index_status_view(self, blog: BlogInfo) -> tuple[str, str, str]:
        address = (blog.address or "").strip()
        meta = self._blog_meta.get(blog.id) or {}
        checked = str(meta.get("naver_index_checked_at") or "").strip()
        if not address:
            return "주소 없음", "off", ""
        if not checked:
            return "확인 전", "off", ""
        when = self._fmt_when(checked)
        count = int(meta.get("naver_index_count") or 0)
        extra = when
        if count:
            extra = f"{count}건" + (f" · {when}" if when else "")
        indexed = meta.get("naver_indexed")
        if indexed is True:
            return "색인됨", "ok", extra
        if indexed is False:
            return "미색인", "wait", extra
        return "확인 실패", "wait", extra

    def _refresh_index_tab(self, force: bool = False) -> None:
        host = getattr(self, "_index_list_inner", None)
        if not self._widget_alive(host):
            return
        if not force and getattr(self, "_main_tab", "") != "색인 확인":
            return
        blogs = self._dashboard_blogs()
        fp = self._index_fingerprint(blogs)
        if fp == getattr(self, "_index_fp", None):
            self._index_dirty = False
            return
        self._index_fp = fp
        self._index_dirty = False
        self._render_index_rows(blogs)

    def _on_index_query_changed(self, *_args) -> None:
        self._after_once("index_query", 120, self._apply_index_visibility)

    def _index_search_text(self, blog: BlogInfo) -> str:
        return self._blog_search_text(blog)

    def _index_row_matches(self, blog: BlogInfo, query: str) -> bool:
        text = getattr(blog, "_index_search_text", "") or self._index_search_text(blog)
        return _query_matches(text, query)

    def _apply_index_visibility(self) -> None:
        rows = getattr(self, "_index_row_frames", None) or {}
        listed = getattr(self, "_listed_index_blogs", None) or []
        if not rows or not listed:
            return
        query = (self.index_query.get() or "").strip() if hasattr(self, "index_query") else ""
        if not query and query == getattr(self, "_index_vis_query", None):
            self._update_index_summary(listed)
            return
        visible: list[tuple] = []
        for blog in listed:
            blog._index_search_text = self._index_search_text(blog)
            row = rows.get(blog.id)
            if row is None or not self._widget_alive(row):
                continue
            row.pack_forget()
            if self._index_row_matches(blog, query):
                visible.append(row)
        for row in visible:
            row.pack(fill=tk.X, pady=4, padx=2)
        shown = len(visible)
        self._index_vis_query = query
        self._update_index_summary(listed, shown=shown)

    def _update_index_summary(self, blogs: list[BlogInfo], shown: int | None = None) -> None:
        summary = getattr(self, "index_summary", None)
        if not self._widget_alive(summary):
            return
        indexed = missing = failed = waiting = 0
        for blog in blogs:
            meta = self._blog_meta.get(blog.id) or {}
            if not str(meta.get("naver_index_checked_at") or "").strip():
                waiting += 1
            elif meta.get("naver_indexed") is True:
                indexed += 1
            elif meta.get("naver_indexed") is False:
                missing += 1
            else:
                failed += 1
        text = f"블로그 {len(blogs)}개 · 색인됨 {indexed} · 미색인 {missing} · 확인 전 {waiting}"
        if failed:
            text += f" · 실패 {failed}"
        query = (self.index_query.get() or "").strip() if hasattr(self, "index_query") else ""
        if query:
            visible = len(blogs) if shown is None else shown
            text += f" · 검색 {visible}개"
        summary.configure(text=text)

    def _paint_index_status(self, row, blog: BlogInfo) -> None:
        status, tone, extra = self._index_status_view(blog)
        pill_widget = getattr(row, "_status_pill", None)
        if self._widget_alive(pill_widget):
            set_pill_tone(pill_widget, text=status, tone=tone)
        extra_widget = getattr(row, "_extra_label", None)
        if self._widget_alive(extra_widget):
            extra_widget.configure(text=extra)
        sample = str((self._blog_meta.get(blog.id) or {}).get("naver_index_sample") or "").strip()
        opener = getattr(row, "_sample_label", None)
        bottom = getattr(row, "_bottom", None)
        if sample and not self._widget_alive(opener) and self._widget_alive(bottom):
            opener = tk.Label(bottom, text="결과 열기", font=FONTS["small"], fg=COLORS["accent"], bg=bottom.cget("bg"), cursor="hand2")
            opener.pack(side=tk.RIGHT)
            opener.bind("<Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            opener.bind("<Double-Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            self._mark_check_hit(opener)
            try:
                opener.configure(cursor="hand2")
            except Exception:
                pass
            row._sample_label = opener
            row._sample_url = sample
        elif self._widget_alive(opener) and sample and getattr(row, "_sample_url", "") != sample:
            opener.bind("<Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            opener.bind("<Double-Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            row._sample_url = sample

    def _paint_blog_index_chip(self, row, blog: BlogInfo) -> None:
        status, tone, extra = self._index_status_view(blog)
        pill_widget = getattr(row, "_index_status_pill", None)
        if self._widget_alive(pill_widget):
            set_pill_tone(pill_widget, text=status, tone=tone)
        extra_widget = getattr(row, "_index_extra_label", None)
        if self._widget_alive(extra_widget):
            extra_widget.configure(text=extra)
            try:
                if extra:
                    extra_widget.pack(side=tk.LEFT, padx=(4, 0))
                else:
                    extra_widget.pack_forget()
            except Exception:
                pass

    def _sync_index_row(self, blog_id: str) -> None:
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        row = (getattr(self, "_index_row_frames", {}) or {}).get(blog_id)
        if blog is not None and self._widget_alive(row):
            self._paint_index_status(row, blog)
            blog._index_search_text = self._index_search_text(blog)
            listed = getattr(self, "_listed_index_blogs", None) or []
            self._apply_index_visibility()
            self._update_index_summary(listed)
            self._index_fp = self._index_fingerprint(self._dashboard_blogs())
        else:
            self._index_fp = None
            if getattr(self, "_main_tab", "") == "색인 확인":
                self._refresh_index_tab(force=True)
        blog_row = (getattr(self, "_blog_row_frames", {}) or {}).get(blog_id)
        if blog is not None and self._widget_alive(blog_row):
            self._paint_blog_index_chip(blog_row, blog)
        # 색인 확인 결과를 기록 상태로 확정 (시트 API 'check'와 같다)
        try:
            self._record_index_result(blog_id)
        except Exception as exc:
            self.log(f"기록 반영 오류: {_exc_text(exc)}")
        self._refresh_record_tree_item(blog_id)

    def _render_index_rows(self, blogs: list[BlogInfo]) -> None:
        host = getattr(self, "_index_list_inner", None)
        if not self._widget_alive(host):
            return
        for child in list(host.winfo_children()):
            child.destroy()
        self._index_row_frames = {}
        self._stale_index_rows = set()
        self._listed_index_blogs = list(blogs)
        self._update_index_summary(blogs)
        if not blogs:
            label(host, "로그인된 계정의 블로그가 없습니다.", "body", COLORS["text_muted"]).pack(anchor="w", pady=8)
            return
        for blog in blogs:
            blog._index_search_text = self._index_search_text(blog)
            self._render_index_row(host, blog)
        self._index_vis_query = None
        self._apply_index_visibility()

    def _render_index_row(self, parent, blog: BlogInfo) -> None:
        bg, border, width = self._row_look(blog.id)
        row = tk.Frame(parent, bg=bg, highlightbackground=border, highlightthickness=width)
        row.pack(fill=tk.X, pady=4, padx=2)
        self._index_row_frames[blog.id] = row
        top = tk.Frame(row, bg=bg)
        top.pack(fill=tk.X, padx=8, pady=(8, 0))
        bottom = tk.Frame(row, bg=bg)
        bottom.pack(fill=tk.X, padx=8, pady=(2, 8))
        row._paint_parts = [row, top, bottom]
        row._bottom = bottom
        self._bind_row_focus(row, blog.id)
        self._bind_row_focus(top, blog.id)
        self._bind_row_focus(bottom, blog.id)
        check_var = self._ensure_check(blog.id)
        check = tk.Checkbutton(
            top, text="", variable=check_var, bg=bg, activebackground=bg,
            command=lambda bid=blog.id: self._on_blog_checked(bid),
        )
        check.pack(side=tk.LEFT)
        self._mark_check_hit(check)
        title = blog.name or blog.address or blog.id
        name = tk.Label(top, text=title, font=FONTS["body_bold"], fg=COLORS["text"], bg=bg)
        name.pack(side=tk.LEFT, padx=(6, 8))
        self._bind_row_focus(name, blog.id)
        status, tone, extra = self._index_status_view(blog)
        status_pill = tk_pill(top, status, tone)
        status_pill.pack(side=tk.LEFT, padx=(0, 6))
        self._bind_row_focus(status_pill, blog.id)
        extra_label = tk.Label(top, text=extra, font=FONTS["small"], fg=COLORS["text_muted"], bg=bg)
        extra_label.pack(side=tk.LEFT)
        self._bind_row_focus(extra_label, blog.id)
        row._status_pill = status_pill
        row._extra_label = extra_label
        address = (blog.address or "").strip() or "주소 없음"
        address_label = tk.Label(bottom, text=address, font=FONTS["small"], fg=COLORS["text_muted"], bg=bg)
        address_label.pack(side=tk.LEFT)
        self._bind_row_focus(address_label, blog.id)
        sample = str((self._blog_meta.get(blog.id) or {}).get("naver_index_sample") or "").strip()
        if sample:
            opener = tk.Label(bottom, text="결과 열기", font=FONTS["small"], fg=COLORS["accent"], bg=bg, cursor="hand2")
            opener.pack(side=tk.RIGHT)
            opener.bind("<Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            opener.bind("<Double-Button-1>", lambda event, url=sample: self._open_index_sample(event, url))
            self._mark_check_hit(opener)
            try:
                opener.configure(cursor="hand2")
            except Exception:
                pass
            row._sample_label = opener
            row._sample_url = sample

    def _open_index_sample(self, _event, url: str):
        if url:
            webbrowser.open(url)
        return "break"

    def on_index_stop(self) -> None:
        stop = getattr(self, "_index_stop", None)
        if stop is not None:
            stop.set()
        self._set_index_progress("색인 확인을 중지하는 중...")

    def on_index_check(self, recheck: bool = False) -> None:
        if getattr(self, "_index_busy", False):
            return
        blogs = self._dashboard_blogs()
        selected = [blog for blog in blogs if self._ensure_check(blog.id).get()]
        query = (self.index_query.get() or "").strip().casefold() if hasattr(self, "index_query") else ""
        if selected:
            targets = selected
        else:
            targets = [blog for blog in blogs if self._index_row_matches(blog, query)]
        ready: list[BlogInfo] = []
        skipped = 0
        for blog in targets:
            if not (blog.address or "").strip():
                continue
            meta = self._blog_meta.get(blog.id) or {}
            if not recheck and meta.get("naver_indexed") is True:
                skipped += 1
                continue
            ready.append(blog)
        if not ready:
            if skipped:
                self._set_index_progress(f"이미 색인된 {skipped}개는 건너뛰었습니다. 다시 확인하면 다시 검색합니다.")
            else:
                self._set_index_progress("확인할 주소가 있는 블로그가 없습니다.")
            return
        scope = "선택한" if selected else ("검색된" if query else "등록된")
        self._start_index_check(ready, skipped, f"{scope} 블로그 {len(ready)}개 확인을 시작합니다.")

    def on_blog_row_index_check(self, blog_id: str) -> None:
        if getattr(self, "_index_busy", False):
            return
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        if blog is None or not (blog.address or "").strip():
            self.log("색인 확인할 주소가 없습니다.")
            return
        self._select_blog(blog_id)
        name = blog.name or blog.address or blog.id
        self._start_index_check([blog], 0, f"{name} 색인 확인을 시작합니다.")

    def _start_index_check(self, ready: list[BlogInfo], skipped: int, progress: str) -> None:
        self._index_busy = True
        self._index_stop = threading.Event()
        self._set_index_buttons(True)
        self._set_index_progress(progress)
        threading.Thread(
            target=self._index_check_worker,
            args=(ready, skipped),
            daemon=True,
        ).start()

    def _index_check_worker(self, blogs: list[BlogInfo], skipped: int) -> None:
        indexed = 0
        not_indexed = 0
        failed = 0
        total = len(blogs)
        stopped = False
        try:
            for index, blog in enumerate(blogs, 1):
                if self._index_stop.is_set():
                    stopped = True
                    break
                if not any(item.id == blog.id for item in self.session.state.blogs):
                    continue
                address = (blog.address or "").strip()
                name = blog.name or address or blog.id
                self.root.after(
                    0,
                    lambda i=index, t=total, label=name: self._set_index_progress(f"색인 확인 {i}/{t}: {label}"),
                )
                self.log(f"색인 확인 {index}/{total}: {name}")
                status = check_naver_index(address)
                if not any(item.id == blog.id for item in self.session.state.blogs):
                    continue
                cur = self._blog_meta.setdefault(blog.id, {})
                cur["naver_indexed"] = status.get("indexed")
                cur["naver_index_message"] = status.get("message") or ""
                cur["naver_index_sample"] = status.get("sample_url") or ""
                cur["naver_index_count"] = status.get("result_count") or 0
                cur["naver_index_query"] = status.get("query") or ""
                cur["naver_index_checked_at"] = datetime.now().isoformat(timespec="seconds")
                if status.get("indexed") is True:
                    indexed += 1
                    self.log(f"색인됨: {name}")
                    self._append_blog_log(blog.id, "색인확인 → 색인됨")
                elif status.get("indexed") is False:
                    not_indexed += 1
                    self.log(f"미색인: {name}")
                    self._append_blog_log(blog.id, "색인확인 → 미색인")
                else:
                    failed += 1
                    self.log(f"색인 확인 실패: {name} · {status.get('message') or ''}")
                    self._append_blog_log(blog.id, "색인확인 → 확인 실패")
                self._schedule_meta_save()
                self.root.after(0, lambda bid=blog.id: self._sync_index_row(bid))
                if index < total and not self._index_stop.is_set():
                    time.sleep(DEFAULT_DELAY_SEC)
            if stopped:
                self.root.after(0, lambda: self._set_index_progress("색인 확인을 중지했습니다."))
                self.log("색인 확인을 중지했습니다.")
            else:
                skip = f" · 이미 색인 {skipped}건 건너뜀" if skipped else ""
                fail = f" · 실패 {failed}" if failed else ""
                text = f"완료: {indexed + not_indexed + failed}건 확인 · 색인 {indexed} · 미색인 {not_indexed}{fail}{skip}"
                self.root.after(0, lambda message=text: self._set_index_progress(message))
                self.log(text)
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"색인 확인 오류: {detail}")
            self.root.after(0, lambda message=detail: self._set_index_progress(f"색인 확인 오류: {message}"))
        finally:
            self._index_busy = False
            self.root.after(0, lambda: self._set_index_buttons(False))
            self._queue_sheet_sync([blog.id for blog in blogs], "색인 확인")

    def _close_record_ui(self) -> None:
        win = getattr(self, "_record_view_win", None)
        if self._widget_alive(win):
            try:
                win.destroy()
            except Exception:
                pass
        self._record_view_win = None
        self._record_view_tree = None
        page = (getattr(self, "_main_pages", None) or {}).pop("기록", None)
        if self._widget_alive(page):
            try:
                page.destroy()
            except Exception:
                pass
        buttons = getattr(self, "_main_tab_buttons", None) or {}
        btn = buttons.pop("기록", None)
        if self._widget_alive(btn):
            try:
                btn.destroy()
            except Exception:
                pass
        if getattr(self, "_main_tab", "") == "기록":
            self._main_tab = "블로그"

    def _build_records_page(self) -> None:
        self._close_record_ui()
        return
        # 기록 탭은 더 이상 만들지 않는다.
        page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["기록"] = page
        card_wrap = card(page)
        card_wrap.pack(fill=tk.BOTH, expand=True)
        inner = tk.Frame(card_wrap, bg=COLORS["card"])
        inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=10)

        # 제목 줄: 왼쪽 제목, 오른쪽 개수
        title_row = tk.Frame(inner, bg=COLORS["card"])
        title_row.pack(fill=tk.X)
        tk.Label(title_row, text="기록", font=FONTS["heading"], fg=COLORS["text"], bg=COLORS["card"]).pack(side=tk.LEFT)
        self._record_count_label = tk.Label(title_row, text="", font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["card"])
        self._record_count_label.pack(side=tk.RIGHT)

        # 이메일 탭: 구글 이메일별로 묶어서 본다. 줄이 넘치면 다음 줄로 접힌다.
        self._record_tab_host = tk.Frame(inner, bg=COLORS["card"])
        self._record_tab_host.pack(fill=tk.X, pady=(6, 2))
        self._record_tab_host.bind("<Configure>", lambda _e: self._after_once("record_tabs_reflow", 30, self._reflow_record_tabs))
        self._record_tab_btns: dict[str, tk.Label] = {}
        self._record_tab_sig: tuple = ()
        if not hasattr(self, "_record_email_filter"):
            self._record_email_filter = ""

        # 찾기 줄
        tools = tk.Frame(inner, bg=COLORS["card"])
        tools.pack(fill=tk.X, pady=(2, 6))
        tk.Label(tools, text="찾기", font=FONTS["small_bold"], fg=COLORS["text_muted"], bg=COLORS["card"]).pack(side=tk.LEFT)
        if not hasattr(self, "record_query"):
            self.record_query = tk.StringVar(value="")
        self._trace_var(self.record_query, self._on_record_query_changed)
        search = tk.Entry(
            tools, textvariable=self.record_query, font=FONTS["body"], width=28,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"], highlightcolor=COLORS["accent"],
        )
        search.pack(side=tk.LEFT, padx=(6, 6), ipady=3)
        flat_button(tools, "지우기", variant="ghost", command=lambda: self.record_query.set("")).pack(side=tk.LEFT)
        self._record_log_btn = flat_button(tools, "변경 로그", variant="ghost", command=self._toggle_record_log)
        self._record_log_btn.pack(side=tk.RIGHT)
        flat_button(tools, "계정상태 동기화", variant="ghost", command=self.on_home_sync_accounts).pack(side=tk.RIGHT, padx=(0, 6))
        flat_button(tools, "본표 정렬", variant="ghost", command=self.on_home_sort).pack(side=tk.RIGHT, padx=(0, 6))
        tk.Label(
            tools, text="상태: " + " · ".join(hr.STATUS_LIST), font=FONTS["caption"],
            fg=COLORS["text_light"], bg=COLORS["card"],
        ).pack(side=tk.RIGHT, padx=(0, 10))

        fold_row = tk.Frame(inner, bg=COLORS["card"])
        fold_row.pack(fill=tk.X, pady=(0, 4))
        self._record_fold_host = fold_row
        self._record_status_fold_btn = flat_button(fold_row, "현재상태 요약 ▸", variant="ghost", command=lambda: self._toggle_record_fold("status"))
        self._record_status_fold_btn.pack(side=tk.LEFT)
        self._record_flow_fold_btn = flat_button(fold_row, "처음수집~전체흐름 ▸", variant="ghost", command=lambda: self._toggle_record_fold("flow"))
        self._record_flow_fold_btn.pack(side=tk.LEFT, padx=(6, 0))

        wrap = tk.Frame(inner, bg=COLORS["card"])
        wrap.pack(fill=tk.BOTH, expand=True)
        wrap.grid_rowconfigure(0, weight=1)
        wrap.grid_columnconfigure(0, weight=1)
        style = ttk.Style(wrap)
        try:
            style.configure(
                "Record.Treeview",
                font=FONTS["body"],
                rowheight=28,
                background=COLORS["card"],
                fieldbackground=COLORS["card"],
                foreground=COLORS["text"],
                borderwidth=0,
            )
            style.configure("Record.Treeview.Heading", font=FONTS["small_bold"], padding=(6, 4))
            style.map("Record.Treeview", background=[("selected", "#c7d2fe")], foreground=[("selected", COLORS["text"])])
        except Exception:
            pass
        tree = ttk.Treeview(
            wrap,
            columns=list(hr.HOME_HEADERS),
            show="headings",
            selectmode="browse",
            style="Record.Treeview",
        )
        self._record_tree = tree
        self._record_mode = "main"
        self._apply_record_columns(hr.HOME_HEADERS)
        ybar = tk.Scrollbar(wrap, orient="vertical", command=tree.yview)
        xbar = tk.Scrollbar(wrap, orient="horizontal", command=tree.xview)

        def on_yscroll(first, last):
            ybar.set(first, last)
            self._reposition_record_editor()

        def on_xscroll(first, last):
            xbar.set(first, last)
            self._reposition_record_editor()

        tree.configure(yscrollcommand=on_yscroll, xscrollcommand=on_xscroll)
        tree.grid(row=0, column=0, sticky="nsew")
        ybar.grid(row=0, column=1, sticky="ns")
        xbar.grid(row=1, column=0, sticky="ew")
        for index, color in enumerate(RECORD_EMAIL_PALETTE):
            tree.tag_configure(f"email{index}", background=color)
        # 시트 조건부서식: 노출됨·잘림·삭제됨은 행 전체를 칠한다
        for state, (bg, fg) in hr.ROW_HIGHLIGHT.items():
            options = {"background": bg}
            if fg:
                options["foreground"] = fg
            tree.tag_configure(f"st_{state}", **options)
        # 묶음 경계: 이메일이 바뀌면 굵은 줄, 같은 이메일에서 키워드가 바뀌면 중간 줄
        tree.tag_configure("grp_email", background="#1f2937", foreground="#ffffff", font=FONTS["small_bold"])
        tree.tag_configure("grp_keyword", background="#e5e7eb", foreground="#374151", font=FONTS["small_bold"])
        tree.tag_configure("log_row", background=COLORS["card"])
        tree.bind("<<TreeviewSelect>>", self._on_record_tree_select)
        tree.bind("<Button-1>", self._on_record_tree_click)
        tree.bind("<Button-3>", self._on_record_tree_menu)
        tree.bind("<Double-1>", self._on_record_tree_double)
        tree.bind("<Return>", self._on_record_tree_enter)
        tree.bind("<F2>", self._on_record_tree_enter)
        tree.bind("<space>", self._on_record_tree_space)
        tree.bind("<Configure>", lambda _e: self._reposition_record_editor())

        self._record_menu = tk.Menu(tree, tearoff=0, font=FONTS["small"])
        for item in (
            ("확인 결과 기록 · 오늘확인", lambda: self._menu_record_action("check")),
            ("재수집요청 기록", lambda: self._menu_record_action("recrawl")),
            ("삭제됨 기록", lambda: self._menu_record_action("deleted")),
            ("완전 삭제 · 삭제됨 행만", lambda: self._menu_record_action("purge")),
            None,
            ("계정상태 동기화", self.on_home_sync_accounts),
        ):
            if item is None:
                self._record_menu.add_separator()
            else:
                self._record_menu.add_command(label=item[0], command=item[1])

        self._record_detail_label = tk.Label(
            inner,
            text="탭으로 이메일을 고릅니다. 핵심키워드 옆에 계정 생성상태가 바로 붙습니다. 현재상태 요약·처음수집~전체흐름은 접고 펼 수 있습니다. 현재상태를 고른 뒤 오늘확인을 체크해야 확정됩니다. Space=오늘확인 · 우클릭=재수집요청/삭제됨 · 본표 정렬=시트 순서로 되돌리기",
            font=FONTS["small"],
            fg=COLORS["text_muted"],
            bg=COLORS["card"],
            anchor="w",
            justify="left",
            wraplength=980,
        )
        self._record_detail_label.pack(fill=tk.X, pady=(6, 0))
        self.records_list = wrap
        self._record_list_inner = wrap
        self._record_editor = None
        self._record_all_iids = []
        self._record_sort = None
        self._log_email: dict[str, str] = {}
        self._after_once("home_tick", 60_000, self._home_tick)

    def _record_headers(self) -> list[str]:
        return list(hr.LOG_HEADERS) if getattr(self, "_record_mode", "main") == "log" else list(hr.HOME_HEADERS)

    def _record_col_index_at(self, tree, x) -> int:
        col = tree.identify_column(x)
        if not col or col == "#0":
            return -1
        try:
            n = int(str(col).replace("#", "")) - 1
        except ValueError:
            return -1
        shown = self._record_display_headers()
        headers = self._record_headers()
        if 0 <= n < len(shown) and shown[n] in headers:
            return headers.index(shown[n])
        if 0 <= n < len(headers):
            return n
        return -1

    def _record_fold_state(self) -> dict:
        home = self.__dict__.setdefault("_home_state", {})
        state = home.get("record_folds")
        if not isinstance(state, dict):
            state = getattr(self, "_record_folds", None)
            if not isinstance(state, dict):
                state = {"status": False, "flow": False}
            home["record_folds"] = state
        state.setdefault("status", False)
        state.setdefault("flow", False)
        self._record_folds = state
        return state

    def _record_display_headers(self) -> list[str]:
        headers = self._record_headers()
        if getattr(self, "_record_mode", "main") != "main":
            return headers
        folds = self._record_fold_state()
        hidden = set(getattr(hr, "HIDDEN_TAB_COLS", ("로그인 이메일",)))
        if not folds.get("status"):
            hidden.update(getattr(hr, "STATUS_SUMMARY_COLS", (
                "현재 검색결과", "현재 작업", "현재 노출키워드", "최근 확인", "한줄 특이사항",
            )))
        if not folds.get("flow"):
            hidden.update(getattr(hr, "FLOW_COLS", (
                "처음수집", "첫색인확인", "핵심노출", "핵심마지막", "잘림시작",
                "재수집요청최근", "재수집요청이력", "색인 소요일", "노출 유지일", "전체흐름",
            )))
        return [name for name in headers if name not in hidden]

    def _toggle_record_fold(self, key: str) -> None:
        if getattr(self, "_record_mode", "main") != "main":
            return
        folds = self._record_fold_state()
        folds[key] = not bool(folds.get(key))
        self._record_shown_cols = None
        self._close_record_edit(True)
        self._schedule_home_save()
        self._apply_record_column_folds()

    def _paint_record_fold_btns(self) -> None:
        folds = self._record_fold_state()
        log_mode = getattr(self, "_record_mode", "main") == "log"
        host = getattr(self, "_record_fold_host", None)
        wrap = getattr(self, "records_list", None)
        if self._widget_alive(host):
            if log_mode:
                host.pack_forget()
            elif wrap is not None and str(host.winfo_manager() or "") != "pack":
                host.pack(fill=tk.X, pady=(0, 4), before=wrap)
        status_btn = getattr(self, "_record_status_fold_btn", None)
        flow_btn = getattr(self, "_record_flow_fold_btn", None)
        if self._widget_alive(status_btn):
            mark = "▾" if folds.get("status") else "▸"
            status_btn.configure(text=f"현재상태 요약 {mark}")
        if self._widget_alive(flow_btn):
            mark = "▾" if folds.get("flow") else "▸"
            flow_btn.configure(text=f"처음수집~전체흐름 {mark}")

    def _apply_record_column_folds(self) -> None:
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        shown = self._record_display_headers()
        prev = getattr(self, "_record_shown_cols", None)
        if prev == tuple(shown):
            self._paint_record_fold_btns()
            return
        self._record_shown_cols = tuple(shown)
        try:
            tree.configure(displaycolumns=shown)
        except Exception:
            pass
        for name in shown:
            try:
                tree.column(name, width=self._record_col_px(name), minwidth=48, stretch=False, anchor="w")
            except Exception:
                pass
        self._paint_record_fold_btns()

    def _apply_record_columns(self, headers: list[str]) -> None:
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        tree.configure(columns=list(headers))
        heading_text = {"계정 생성상태": "계정생성"}
        for name in headers:
            tree.heading(name, text=heading_text.get(name, name), anchor="w", command=lambda n=name: self._sort_record_tree(n))
        self._record_shown_cols = None
        self._apply_record_column_folds()

    def _toggle_record_log(self) -> None:
        """표를 본표(A:AD) ↔ 변경 로그(AE:AK)로 바꾼다."""
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        self._close_record_edit(True)
        self._record_mode = "log" if getattr(self, "_record_mode", "main") == "main" else "main"
        self._record_sort = None
        try:
            tree.delete(*tree.get_children(""))
        except Exception:
            pass
        for iid in list(getattr(self, "_record_all_iids", None) or []):
            try:
                if tree.exists(iid):
                    tree.delete(iid)
            except Exception:
                pass
        self._record_all_iids = []
        self._record_fp = None
        self._apply_record_columns(self._record_headers())
        btn = getattr(self, "_record_log_btn", None)
        if self._widget_alive(btn):
            btn.configure(text="본표로" if self._record_mode == "log" else "변경 로그")
        self._render_record_rows(force=True)

    def _home_tick(self) -> None:
        """시트의 1시간 트리거(오늘확인 10시간 정리)를 1분마다 가볍게 확인한다."""
        try:
            changed = hr.expire_today_checks(self._blog_meta, datetime.now())
            if changed:
                self._schedule_meta_save()
                for blog_id in changed:
                    self._refresh_record_tree_item(blog_id)
        except Exception:
            pass
        self._after_once("home_tick", 60_000, self._home_tick)

    def _sheet_day(self, raw: str = "") -> str:
        value = (raw or "").strip()
        if not value:
            return ""
        try:
            dt = datetime.fromisoformat(value)
        except ValueError:
            return value
        return f"{dt.month}/{dt.day}"

    def _schedule_meta_save(self) -> None:
        self._after_once("meta_save", 400, self._save_blog_meta)

    def _blog_log_stamp(self, raw: str = "") -> str:
        dt = self._event_when(raw) if raw else datetime.now()
        if dt is None:
            dt = datetime.now()
        return f"{dt.month}월 {dt.day}일 {dt.hour:02d}:{dt.minute:02d}"

    def _blog_log_when(self, raw: str = "") -> datetime | None:
        return self._event_when(raw)

    def _blog_log_day_label(self, dt: datetime | None) -> str:
        if dt is None:
            return "날짜 없음"
        today = datetime.now().date()
        day = dt.date()
        if day == today:
            return f"오늘 {dt.month}월 {dt.day}일"
        if day == today - timedelta(days=1):
            return f"어제 {dt.month}월 {dt.day}일"
        if dt.year == today.year:
            return f"{dt.month}월 {dt.day}일"
        return f"{dt.year}년 {dt.month}월 {dt.day}일"

    def _group_blog_logs(self, items: list[dict]) -> list[dict]:
        groups: dict[str, dict] = {}
        for item in items:
            dt = self._blog_log_when(item.get("ts"))
            key = dt.strftime("%Y-%m-%d") if dt is not None else "unknown"
            bucket = groups.get(key)
            if bucket is None:
                bucket = {"key": key, "dt": dt, "items": []}
                groups[key] = bucket
            elif dt is not None and (bucket.get("dt") is None or dt > bucket["dt"]):
                bucket["dt"] = dt
            bucket["items"].append({"ts": item.get("ts") or "", "text": item.get("text") or "", "dt": dt})
        ordered = sorted(
            groups.values(),
            key=lambda row: row.get("dt") or datetime.min,
            reverse=True,
        )
        for row in ordered:
            row["items"].sort(key=lambda item: item.get("dt") or datetime.min, reverse=True)
            row["summary"] = self._blog_log_day_summary(row["items"])
        return ordered

    def _blog_log_day_summary(self, entries: list[dict]) -> str:
        posts = 0
        counts: list[tuple[str, int]] = []
        index_last = ""
        chrono = sorted(entries, key=lambda item: item.get("dt") or datetime.min)
        for item in chrono:
            text = str(item.get("text") or "").strip()
            if not text:
                continue
            added = _BLOG_POST_ADD_RE.match(text)
            if added:
                posts += int(added.group(1))
                continue
            if text.startswith("색인확인"):
                index_last = text
                continue
            if counts and counts[-1][0] == text:
                counts[-1] = (text, counts[-1][1] + 1)
            else:
                counts.append((text, 1))
        parts: list[str] = []
        if posts:
            parts.append(f"글 {posts}개 추가")
        for text, count in counts:
            parts.append(text if count == 1 else f"{text} {count}회")
        if index_last:
            parts.append(index_last)
        return " · ".join(parts)

    def _blog_log_fg(self, text: str) -> str:
        if "미색인" in text or "실패" in text:
            return COLORS["danger"]
        if "색인됨" in text or "추가" in text:
            return COLORS["success"]
        if "변경" in text or "재신청" in text:
            return COLORS["warning"]
        return COLORS["text"]

    def _append_blog_log(self, blog_id: str, text: str) -> None:
        blog_id = str(blog_id or "").strip()
        label = " ".join(str(text or "").split())
        if not blog_id or not label:
            return
        now = datetime.now()
        cur = self._blog_meta.setdefault(blog_id, {})
        items = cur.get("activity_log")
        if not isinstance(items, list):
            items = []
            cur["activity_log"] = items
        last = items[-1] if items else None
        added = _BLOG_POST_ADD_RE.match(label)
        last_added = _BLOG_POST_ADD_RE.match(str(last.get("text") or "")) if last else None
        last_dt = self._event_when(last.get("ts")) if last else None
        if added and last_added and last_dt is not None and (now - last_dt).total_seconds() < 6 * 3600:
            count = int(last_added.group(1)) + int(added.group(1))
            last["text"] = f"글 {count}개 추가"
            last["ts"] = now.isoformat(timespec="seconds")
        elif last and str(last.get("text") or "") == label and last_dt is not None and (now - last_dt).total_seconds() < 90:
            return
        else:
            items.append({"ts": now.isoformat(timespec="seconds"), "text": label})
            if len(items) > _BLOG_LOG_MAX:
                del items[:-_BLOG_LOG_MAX]
        try:
            self._save_blog_meta()
        except Exception:
            self._schedule_meta_save()
        try:
            self.root.after(0, lambda bid=blog_id: self._refresh_blog_log_win(bid))
        except Exception:
            pass

    def _log_settings_apply(self, blog_id: str, ok: bool) -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        if not ok:
            self._append_blog_log(blog_id, "설정적용 실패")
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        had = bool(str(cur.get("settings_applied_at") or "").strip())
        cur["settings_applied_at"] = datetime.now().isoformat(timespec="minutes")
        self._append_blog_log(blog_id, "설정적용 재신청" if had else "설정적용")

    def on_blog_log(self) -> None:
        blog_id = str(self.blog_var.get() or "").strip()
        if not blog_id:
            messagebox.showwarning("블로그 로그", "로그를 볼 블로그를 목록에서 먼저 눌러 주세요.")
            return
        self._open_blog_log_win(blog_id)

    # ----- HOME 기록: 저장 / 확정 ---------------------------------------------------
    # 시트 Apps Script의 onEdit·confirmCurrentState_·API를 프로그램 안에서 그대로 수행한다.
    # 규칙 자체는 home_records.py에 있고, 여기서는 화면·저장·동기화만 잇는다.

    def _home_events(self) -> list:
        state = self.__dict__.setdefault("_home_state", {})
        events = state.get("events")
        if not isinstance(events, list):
            events = []
            state["events"] = events
        return events

    def _load_home_state(self) -> None:
        path = data_path(HOME_STATE_FILE)
        prev_gone = [str(item).strip() for item in ((self.__dict__.get("_home_state") or {}).get("gone_ids") or []) if str(item).strip()]
        prev_folds = (self.__dict__.get("_home_state") or {}).get("record_folds")
        state = {"email_order": [], "program_order": {}, "program_order_time": {}, "events": [], "gone_ids": [], "record_folds": {"status": False, "flow": False}}
        loaded_folds = False
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as handle:
                    raw = json.load(handle) or {}
                if isinstance(raw.get("email_order"), list):
                    state["email_order"] = [str(item) for item in raw["email_order"] if str(item or "").strip()]
                if isinstance(raw.get("program_order"), dict):
                    state["program_order"] = {str(k): [str(d) for d in v] for k, v in raw["program_order"].items() if isinstance(v, list)}
                if isinstance(raw.get("program_order_time"), dict):
                    state["program_order_time"] = {str(k): str(v) for k, v in raw["program_order_time"].items()}
                if isinstance(raw.get("events"), list):
                    state["events"] = [item for item in raw["events"] if isinstance(item, dict)]
                if isinstance(raw.get("gone_ids"), list):
                    state["gone_ids"] = [str(item) for item in raw["gone_ids"] if str(item or "").strip()]
                if isinstance(raw.get("record_folds"), dict):
                    state["record_folds"] = {
                        "status": bool(raw["record_folds"].get("status")),
                        "flow": bool(raw["record_folds"].get("flow")),
                    }
                    loaded_folds = True
            except Exception:
                pass
        if not loaded_folds and isinstance(prev_folds, dict):
            state["record_folds"] = {
                "status": bool(prev_folds.get("status")),
                "flow": bool(prev_folds.get("flow")),
            }
        for blog_id in prev_gone:
            if blog_id not in state["gone_ids"]:
                state["gone_ids"].append(blog_id)
        self._home_state = state
        self._record_folds = state.get("record_folds")
        self._apply_gone_ids()

    def _save_home_state(self) -> None:
        try:
            with open(data_path(HOME_STATE_FILE), "w", encoding="utf-8") as handle:
                json.dump(self.__dict__.get("_home_state") or {}, handle, ensure_ascii=False, indent=1)
        except Exception as exc:
            self.log(f"기록 상태 저장 오류: {_exc_text(exc)}")

    def _schedule_home_save(self) -> None:
        self._after_once("home_save", 500, self._save_home_state)

    def _apply_gone_ids(self) -> None:
        gone = {str(item).strip() for item in ((self.__dict__.get("_home_state") or {}).get("gone_ids") or []) if str(item).strip()}
        session = getattr(self, "session", None)
        if session is None:
            return
        current = getattr(session, "_gone_ids", None)
        if current is None:
            session._gone_ids = set()
            current = session._gone_ids
        current.update(gone)
        if current:
            home = self.__dict__.setdefault("_home_state", {})
            saved = home.setdefault("gone_ids", [])
            extra = [item for item in sorted(current) if item not in saved]
            if extra:
                saved.extend(extra)
                if len(saved) > 400:
                    home["gone_ids"] = saved[-400:]
                self._schedule_home_save()
        if session.state.blogs:
            session.state.blogs = [blog for blog in session.state.blogs if blog.id not in current]

    def _remember_gone_id(self, blog_id: str) -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        session = getattr(self, "session", None)
        if session is not None:
            gone = getattr(session, "_gone_ids", None)
            if gone is None:
                session._gone_ids = set()
                gone = session._gone_ids
            gone.add(blog_id)
        home = self.__dict__.setdefault("_home_state", {})
        saved = home.setdefault("gone_ids", [])
        if blog_id not in saved:
            saved.append(blog_id)
            if len(saved) > 400:
                home["gone_ids"] = saved[-400:]
        self._save_home_state()

    def _record_domain(self, blog_id: str) -> str:
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        meta = self._blog_meta.get(blog_id) or {}
        return str((blog.address if blog else "") or meta.get("address") or "").strip()

    def _remember_email_order(self, email: str) -> None:
        email = str(email or "").strip().lower()
        if not email:
            return
        order = self._home_state.setdefault("email_order", [])
        if email not in order:
            order.append(email)
            self._schedule_home_save()

    def _after_record_change(self, blog_ids, regroup: bool = False) -> None:
        """저장·시트 동기화·화면 갱신을 한 번에."""
        ids = [blog_id for blog_id in blog_ids if blog_id]
        self._schedule_meta_save()
        self._schedule_home_save()
        for blog_id in ids:
            self._refresh_record_tree_item(blog_id)
        if regroup:
            self._record_fp = None
            self._after_once("record_rerender", 40, lambda: self._render_record_rows(force=getattr(self, "_main_tab", "") == "기록"))
        self._schedule_record_view_refresh()

    def _confirm_record(self, blog_id: str, state: str, *, source: str = "수동", note: str = "", when: datetime | None = None, quiet: bool = False, check_today: bool = False) -> bool:
        """상태 확정. 시트의 confirmCurrentState_ + 변경 로그."""
        if not blog_id:
            return False
        cur = self._blog_meta.setdefault(blog_id, {})
        stamp = when or datetime.now()
        result = hr.confirm_state(
            cur, state, stamp,
            blog_id=blog_id, domain=self._record_domain(blog_id), source=source, note=note, events=self._home_events(),
        )
        if not result["ok"]:
            if not quiet:
                if result["reason"] == "exposure_required":
                    messagebox.showwarning("기록", "별도키워드노출은 현재노출키워드를 먼저 적어 주세요.")
                else:
                    messagebox.showwarning("기록", f"알 수 없는 상태입니다: {state}")
            return False
        if check_today:
            cur["today_checked"] = True
            cur["check_ts"] = stamp.isoformat(timespec="seconds")
        self._remember_email_order(cur.get("google_email"))
        regroup = result["changed"] and hr.normalize_status(state) == "삭제됨"
        self._after_record_change([blog_id], regroup=regroup)
        return True

    def _set_record_field(self, blog_id: str, key: str, value) -> None:
        """사람이 칸을 고쳤을 때 (시트 onEdit)."""
        if not blog_id or key not in hr.HOME_FIELDS:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        if key == "today_checked":
            self._toggle_today_check(blog_id)
            return
        text = str(value or "").strip()
        if key == "sheet_status":
            old = hr.normalize_status(cur.get("sheet_status"))
            state = hr.pending_edit(cur, text)
            if not state or state == old:
                self._refresh_record_tree_item(blog_id)
                return
            self._after_record_change([blog_id])
            return
        if key == "account_status":
            if text and text not in hr.ACCOUNT_STATUS_LIST:
                return
            if str(cur.get("account_status") or "") == text:
                return
            cur["account_status"] = text
            check = hr.ymd(datetime.now()) if text else str(cur.get("account_check") or "")
            cur["account_check"] = check
            changed = hr.sync_account_by_email(self._blog_meta, cur.get("google_email"), text, check)
            self._after_record_change(set(changed) | {blog_id})
            return
        if key == "account_check":
            day = hr.parse_day(text) if text else None
            if text and day is None:
                messagebox.showwarning("기록", "날짜는 10/6 또는 2026-10-06 형식으로 적어 주세요.")
                self._refresh_record_tree_item(blog_id)
                return
            check = day.isoformat() if day else ""
            if str(cur.get("account_check") or "") == check:
                return
            cur["account_check"] = check
            changed = hr.sync_account_by_email(self._blog_meta, cur.get("google_email"), str(cur.get("account_status") or ""), check)
            self._after_record_change(set(changed) | {blog_id})
            return
        old = str(cur.get(key) or "").strip()
        if old == text:
            return
        cur[key] = text
        if key == "google_email":
            self._remember_email_order(text)
            changed = hr.sync_all_accounts(self._blog_meta)
            self._after_record_change(set(changed) | {blog_id}, regroup=True)
            return
        if key == "keyword":
            self._after_record_change([blog_id], regroup=True)
            return
        self._after_record_change([blog_id])

    def _toggle_today_check(self, blog_id: str) -> None:
        """P 오늘확인. 체크하면 현재상태를 확정하고 로그를 남긴다. 해제하면 체크시각만 지운다."""
        cur = self._blog_meta.setdefault(blog_id, {})
        if cur.get("today_checked"):
            cur["today_checked"] = False
            cur["check_ts"] = ""
            self._after_record_change([blog_id])
            return
        state = hr.normalize_status(cur.get("sheet_status")) or "생성만"
        now = datetime.now()
        if not self._confirm_record(blog_id, state, source="수동", when=now):
            return
        cur["today_checked"] = True
        cur["check_ts"] = now.isoformat(timespec="seconds")
        self._after_record_change([blog_id])

    def _menu_record_action(self, action: str) -> None:
        """우클릭 메뉴: 시트의 선택 행 메뉴와 같은 동작."""
        blog_id = str(getattr(self, "_record_menu_target", "") or "")
        if not blog_id or blog_id.startswith("__"):
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        current = hr.normalize_status(cur.get("confirmed_status") or cur.get("sheet_status"))
        domain = self._record_domain(blog_id) or blog_id
        if action == "check":
            if cur.get("today_checked"):
                cur["today_checked"] = False
            self._toggle_today_check(blog_id)
            return
        if action == "recrawl":
            if current == "삭제됨":
                messagebox.showwarning("기록", "삭제된 블로그에는 재수집을 기록할 수 없습니다.")
                return
            self._confirm_record(blog_id, "재수집요청", source="수동", check_today=True)
            return
        if action == "deleted":
            if not messagebox.askyesno("삭제 확인 기록", f"{domain}\n실제로 삭제된 블로그를 삭제됨으로 기록할까요?\n로그아웃·목록 누락만으로는 삭제됨을 기록하지 마세요."):
                return
            self._confirm_record(blog_id, "삭제됨", source="수동")
            return
        if action == "purge":
            if current != "삭제됨":
                messagebox.showwarning("기록", "삭제됨으로 기록된 행만 완전 삭제할 수 있습니다.")
                return
            if not messagebox.askyesno("기록 행 완전 삭제", f"{domain}\n이 기록 행을 완전히 삭제할까요?\n변경 로그는 보존됩니다. Blogger의 실제 블로그에는 작업하지 않습니다."):
                return
            self._blog_meta.pop(blog_id, None)
            self._schedule_meta_save()
            self._record_fp = None
            self._render_record_rows(force=True)
            self.log(f"기록 행을 삭제했습니다: {domain}")

    def on_home_sync_accounts(self) -> None:
        changed = hr.sync_all_accounts(self._blog_meta)
        if changed:
            self._after_record_change(changed)
        self.log("같은 로그인 이메일의 계정 생성상태/마지막확인을 맞췄습니다.")

    def on_home_sort(self) -> None:
        """시트의 '본표 정렬 · 프로그램순서 우선'과 같다. 열 제목 정렬을 풀고 시트 순서로 되돌린다."""
        self._record_sort = None
        self._record_fp = None
        self._render_record_rows(force=True)
        self.log("기록을 시트와 같은 순서로 정렬했습니다.")

    def _record_index_result(self, blog_id: str) -> None:
        """색인 확인 결과를 시트 API 'check'처럼 상태로 반영한다."""
        cur = self._blog_meta.get(blog_id) or {}
        indexed = cur.get("naver_indexed")
        if not isinstance(indexed, bool):
            return
        state = hr.index_check_state(cur, indexed)
        count = int(cur.get("naver_index_count") or 0)
        note = f"검색엔진: naver · 결과 {count}건" if count else "검색엔진: naver"
        if state:
            self._confirm_record(blog_id, state, source="프로그램", note=note, quiet=True, check_today=True)
            return
        current = hr.normalize_status(cur.get("confirmed_status") or cur.get("sheet_status"))
        if current and current != "삭제됨":
            self._home_events().append(hr.make_event(
                cur, blog_id=blog_id, domain=self._record_domain(blog_id), old=current,
                event=f"{current} 유지 · 색인 확인", when=datetime.now(), source="프로그램", note=note,
            ))
            self._schedule_home_save()
            self._refresh_record_tree_item(blog_id)

    def _logged_google_email(self) -> str:
        account = str(getattr(getattr(self.session, "state", None), "account", "") or "").strip()
        if account:
            return account
        return str(getattr(self, "_shown_account", "") or "").strip()

    def _clean_status_flow(self, flow: str) -> str:
        parts = [part.strip() for part in (flow or "").split("→") if part.strip()]
        cleaned: list[str] = []
        for part in parts:
            if not cleaned or cleaned[-1] != part:
                cleaned.append(part)
        return " → ".join(cleaned)

    def _program_sheet_status(self, blog: BlogInfo) -> str:
        meta = self._blog_meta.get(blog.id) or {}
        done = set(getattr(blog, "done", set()) or set())
        done.update(self._progress_map.get(blog.id) or [])
        count = self._count_value(meta.get("blog_crawl_count"))
        collected = "collect" in done or bool(str(meta.get("last_blog_crawl") or "").strip())
        return hr.program_state(meta, collected=collected, collect_count=count)

    def _migrate_home_meta(self, cur: dict) -> bool:
        """옛 저장값(설정완료·확인전·잘림의심 등)을 시트의 새 상태 이름으로."""
        changed = False
        for key in ("sheet_status", "confirmed_status", "prev_status", "prev2_status"):
            old = str(cur.get(key) or "").strip()
            new = hr.normalize_status(old)
            if new != old:
                cur[key] = new
                changed = True
        flow = str(cur.get("status_flow") or "")
        migrated = hr.migrate_flow_text(flow)
        if migrated != flow:
            cur["status_flow"] = migrated
            changed = True
        if not str(cur.get("confirmed_status") or "").strip() and str(cur.get("sheet_status") or "").strip():
            cur["confirmed_status"] = hr.normalize_status(cur.get("sheet_status"))
            changed = True
        return changed

    def _fill_program_records(self, blogs: list[BlogInfo] | None = None) -> bool:
        return False
        """프로그램이 아는 사실을 기록에 반영한다 (시트 API의 blog_created / recrawl에 해당)."""
        email = self._logged_google_email()
        targets = list(blogs) if blogs is not None else self._dashboard_blogs()
        gone = self._gone_id_set()
        changed = False
        now = datetime.now()
        events = self._home_events()
        for blog in targets:
            if blog.id in gone:
                continue
            cur = self._blog_meta.setdefault(blog.id, {})
            if self._migrate_home_meta(cur):
                changed = True
            if email and not str(cur.get("google_email") or "").strip():
                cur["google_email"] = email
                self._remember_email_order(email)
                changed = True
            address = str(blog.address or cur.get("address") or "").strip()
            title = str(blog.name or cur.get("name") or "")
            if title and not str(cur.get("h1") or "").strip():
                cur["h1"] = title
                changed = True
            if not str(cur.get("confirmed_status") or "").strip():
                # 처음 보는 블로그 → 신규등록 · 생성만
                hr.register_new(cur, now, blog_id=blog.id, domain=address, email=email, title=title, events=events)
                changed = True
            status = hr.normalize_status(cur.get("confirmed_status"))
            if status in hr.PROGRAM_STATUSES:
                derived = self._program_sheet_status(blog)
                if derived and derived != status:
                    out = hr.confirm_state(cur, derived, now, blog_id=blog.id, domain=address, source="프로그램", events=events)
                    if out["ok"]:
                        cur["today_checked"] = True
                        cur["check_ts"] = now.isoformat(timespec="seconds")
                    changed = changed or out["ok"]
        if changed:
            self._schedule_meta_save()
            self._schedule_home_save()
        return changed

    def _sheet_record_dicts(self, only_ids: set[str] | None = None, blogs=None) -> list[dict]:
        source = list(blogs) if blogs is not None else self._dashboard_blogs()
        targets = source if only_ids is None else [blog for blog in source if blog.id in only_ids]
        live_ids = {item.id for item in self._dashboard_blogs()}
        self._fill_program_records([blog for blog in targets if blog.id in live_ids])
        records = []
        for blog in source:
            if only_ids is not None and blog.id not in only_ids:
                continue
            meta = self._blog_meta.get(blog.id) or {}
            urls = [str(post.get("url") or "").strip() for post in (blog.posts or []) if str(post.get("url") or "").strip()]
            if not urls:
                urls = [str(item.get("url") or "").strip() for item in normalize_posts(meta.get("posts") or []) if str(item.get("url") or "").strip()]
            done = set(getattr(blog, "done", set()) or set())
            done.update(self._progress_map.get(blog.id) or [])
            collect_count = self._count_value(meta.get("blog_crawl_count"))
            if collect_count < 1 and ("collect" in done or str(meta.get("last_blog_crawl") or "").strip()):
                collect_count = 1
            email = str(meta.get("google_email") or "").strip()
            if not email and blog.id in live_ids:
                email = self._logged_google_email()
            records.append(
                {
                    "id": blog.id,
                    "keyword": meta.get("keyword") or "",
                    "google_email": email,
                    "title": blog.name or meta.get("name") or "",
                    "address": blog.address or meta.get("address") or "",
                    "posts": " · ".join(urls),
                    "html_code": meta.get("html_code") or "",
                    "naver_id": meta.get("naver_id") or "",
                    "index_status": index_status_label(
                        meta.get("naver_indexed") if isinstance(meta.get("naver_indexed"), bool) else None,
                        str(meta.get("naver_index_checked_at") or ""),
                        blog.address or meta.get("address") or "",
                    ),
                    "sheet_status": meta.get("sheet_status") or "",
                    "search_result": meta.get("search_result") or "",
                    "work": meta.get("work") or "",
                    "exposed_keyword": meta.get("exposed_keyword") or "",
                    "last_check": meta.get("last_check") or "",
                    "sheet_note": meta.get("sheet_note") or "",
                    "first_collect": self._sheet_day(str(meta.get("blog_collect_at") or meta.get("last_blog_crawl") or "")),
                    "last_collect": self._sheet_day(str(meta.get("last_blog_crawl") or "")),
                    "collect_count": str(collect_count or ""),
                    "first_index_at": meta.get("first_index_at") or "",
                    "trim_started_at": meta.get("trim_started_at") or "",
                    "status_flow": meta.get("status_flow") or "",
                    "prev_status": meta.get("prev_status") or "",
                    "folder": meta.get("folder") or "",
                    "last_post_collect": self._sheet_day(str(meta.get("last_post_crawl") or "")),
                }
            )
        return records

    def _offline_blog(self, blog_id: str, meta: dict) -> BlogInfo:
        blog = BlogInfo(
            id=blog_id,
            name=str(meta.get("name") or meta.get("address") or blog_id[-6:]),
            address=str(meta.get("address") or ""),
            posts=normalize_posts(meta.get("posts") or []),
            done=set(self._progress_map.get(blog_id) or []),
        )
        return blog

    def _gone_id_set(self) -> set[str]:
        gone = set()
        session = getattr(self, "session", None)
        if session is not None:
            gone.update(str(item).strip() for item in (getattr(session, "_gone_ids", None) or set()) if str(item).strip())
        home = (self.__dict__.get("_home_state") or {}).get("gone_ids") or []
        gone.update(str(item).strip() for item in home if str(item).strip())
        return gone

    def _record_blogs(self) -> list[BlogInfo]:
        live = {blog.id: blog for blog in self._dashboard_blogs()}
        gone = self._gone_id_set()
        logged = str(self._logged_google_email() or "").strip().lower()
        account_live = bool(getattr(self.session.state, "logged_in", False) and live)
        found: list[BlogInfo] = []
        seen: set[str] = set()
        for blog_id, meta in (self._blog_meta or {}).items():
            if not isinstance(meta, dict):
                continue
            if blog_id in gone:
                continue
            if blog_id in live:
                found.append(live[blog_id])
                seen.add(blog_id)
                continue
            if account_live:
                email = str(meta.get("google_email") or "").strip().lower()
                if email and logged and email == logged:
                    continue
            if not (
                meta.get("address")
                or meta.get("name")
                or meta.get("status_flow")
                or meta.get("sheet_status")
                or meta.get("google_email")
                or meta.get("keyword")
            ):
                continue
            found.append(self._offline_blog(blog_id, meta))
            seen.add(blog_id)
        for blog in live.values():
            if blog.id not in seen and blog.id not in gone:
                found.append(blog)
        return found

    # ----- 기록 표: 편집 ---------------------------------------------------------
    # 표(Treeview) 위에 입력칸 하나만 띄워서 수정한다. 줄마다 입력칸을 만들지 않으므로 기록이 수백 개여도 가볍다.

    def _record_editable_indexes(self) -> list[int]:
        if getattr(self, "_record_mode", "main") == "log":
            return []
        shown = set(self._record_display_headers())
        return [index for index, name in enumerate(hr.HOME_HEADERS) if hr.EDITABLE.get(name) and name in shown]

    def _record_tree_visible(self) -> list[str]:
        """보이는 실제 기록 줄(묶음 머리글·로그 줄 제외)."""
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return []
        try:
            return [iid for iid in tree.get_children("") if not str(iid).startswith("__")]
        except Exception:
            return []

    def _close_record_edit(self, apply: bool = True) -> None:
        editor = getattr(self, "_record_editor", None)
        self._record_editor = None
        if editor is None:
            return
        widget = editor.get("widget")
        blog_id = str(editor.get("blog_id") or "")
        key = str(editor.get("key") or "")
        value = ""
        if apply and widget is not None:
            try:
                value = widget.get()
            except Exception:
                value = ""
        try:
            if widget is not None:
                widget.destroy()
        except Exception:
            pass
        if apply and blog_id and key in hr.HOME_FIELDS:
            self._set_record_field(blog_id, key, value)
            self._refresh_record_tree_item(blog_id)
            self._show_record_detail(blog_id, int(editor.get("index") or 0))
        tree = getattr(self, "_record_tree", None)
        if apply and self._widget_alive(tree):
            try:
                tree.focus_set()
            except Exception:
                pass

    def _reposition_record_editor(self) -> None:
        editor = getattr(self, "_record_editor", None)
        tree = getattr(self, "_record_tree", None)
        if editor is None or not self._widget_alive(tree):
            return
        widget = editor.get("widget")
        if not self._widget_alive(widget):
            self._record_editor = None
            return
        try:
            name = self._record_headers()[int(editor["index"])]
            bbox = tree.bbox(editor["blog_id"], name)
        except Exception:
            bbox = None
        if not bbox:
            try:
                widget.place_forget()
            except Exception:
                pass
            return
        x, y, width, height = bbox
        try:
            widget.place(x=x, y=y, width=max(width, 80), height=max(height, 24))
        except Exception:
            pass

    def _edit_record_cell(self, iid: str, index: int) -> None:
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree) or not iid:
            return
        headers = self._record_headers()
        if index < 0 or index >= len(headers) or str(iid).startswith("__"):
            return
        name = headers[index]
        key = hr.EDITABLE.get(name) if getattr(self, "_record_mode", "main") == "main" else ""
        self._record_click_col = index
        self._close_record_edit(True)
        if not key:
            self._show_record_detail(iid, index)
            return
        if key == "today_checked":
            self._toggle_today_check(iid)
            self._show_record_detail(iid, index)
            return
        try:
            if not tree.exists(iid):
                return
            tree.see(iid)
            tree.update_idletasks()
            bbox = tree.bbox(iid, name)
        except Exception:
            bbox = None
        if not bbox:
            return
        x, y, width, height = bbox
        values = tree.item(iid, "values")
        current = values[index] if index < len(values) else ""
        if key in ("sheet_status", "account_status"):
            options = list(hr.STATUS_LIST) if key == "sheet_status" else ["", *hr.ACCOUNT_STATUS_LIST]
            shown = current
            if shown not in options:
                options.append(shown)
            widget = ttk.Combobox(tree, values=options, state="readonly", font=FONTS["body"])
            widget.set(shown)
        else:
            widget = tk.Entry(
                tree, font=FONTS["body"], bg="#fffbeb", fg=COLORS["text"], relief="flat",
                highlightthickness=2, highlightbackground=COLORS["accent"], highlightcolor=COLORS["accent"],
            )
            widget.insert(0, current)
            widget.select_range(0, tk.END)
            widget.icursor(tk.END)
        widget.place(x=x, y=y, width=max(width, 80), height=max(height, 24))
        widget.focus_set()
        self._record_editor = {"widget": widget, "blog_id": iid, "key": key, "index": index}
        widget.bind("<Return>", lambda _e: (self._close_record_edit(True), "break")[1])
        widget.bind("<KP_Enter>", lambda _e: (self._close_record_edit(True), "break")[1])
        widget.bind("<Escape>", lambda _e: (self._close_record_edit(False), "break")[1])
        widget.bind("<Tab>", lambda _e: self._record_edit_step(cols=1))
        widget.bind("<Shift-Tab>", lambda _e: self._record_edit_step(cols=-1))
        widget.bind("<ISO_Left_Tab>", lambda _e: self._record_edit_step(cols=-1))
        widget.bind("<Down>", lambda _e: self._record_edit_step(rows=1))
        widget.bind("<Up>", lambda _e: self._record_edit_step(rows=-1))
        if key in ("sheet_status", "account_status"):
            widget.bind("<<ComboboxSelected>>", lambda _e: self._close_record_edit(True))
            widget.bind("<FocusOut>", lambda _e, w=widget: self._after_once("record_combo_blur", 150, lambda: self._combo_blur_check(w)))
        else:
            widget.bind("<FocusOut>", lambda _e: self._close_record_edit(True))
        self._show_record_detail(iid, index)

    def _combo_blur_check(self, widget) -> None:
        """콤보박스는 펼침 목록이 따로 뜨므로, 포커스가 정말 다른 곳으로 갔을 때만 닫는다."""
        editor = getattr(self, "_record_editor", None)
        if editor is None or editor.get("widget") is not widget:
            return
        try:
            focus = self.root.focus_get()
        except Exception:
            return  # 펼침 목록(파이썬이 모르는 Tk 창)이 포커스를 가진 상태
        if focus is widget:
            return
        self._close_record_edit(True)

    def _record_edit_step(self, rows: int = 0, cols: int = 0):
        """편집 중 Tab/Shift-Tab은 옆 칸으로, ↑↓는 같은 열의 윗줄·아랫줄로 옮긴다."""
        editor = getattr(self, "_record_editor", None)
        if editor is None:
            return "break"
        iid = str(editor.get("blog_id") or "")
        index = int(editor.get("index") or 0)
        self._close_record_edit(True)
        editable = self._record_editable_indexes()
        if cols and editable:
            if index in editable:
                pos = editable.index(index)
            else:
                pos = min(range(len(editable)), key=lambda i: abs(editable[i] - index))
            index = editable[(pos + cols) % len(editable)]
        if rows:
            visible = self._record_tree_visible()
            if iid in visible:
                pos = visible.index(iid) + rows
                if 0 <= pos < len(visible):
                    iid = visible[pos]
        if iid:
            self._select_blog(iid)
            self.root.after_idle(lambda: self._edit_record_cell(iid, index))
        return "break"

    def _show_record_detail(self, iid: str, index: int) -> None:
        tree = getattr(self, "_record_tree", None)
        label_widget = getattr(self, "_record_detail_label", None)
        if not self._widget_alive(tree) or not self._widget_alive(label_widget):
            return
        try:
            values = tree.item(iid, "values") if iid and tree.exists(iid) else ()
        except Exception:
            values = ()
        headers = self._record_headers()
        if not values or index < 0 or index >= len(headers) or str(iid).startswith("__grp"):
            return
        name = headers[index]
        value = str(values[index] if index < len(values) else "").strip()
        title_name = "도메인" if getattr(self, "_record_mode", "main") == "log" else "블로그제목(H1)"
        title_col = headers.index(title_name) if title_name in headers else -1
        title = str(values[title_col] if 0 <= title_col < len(values) else "").strip()
        key = hr.EDITABLE.get(name) if getattr(self, "_record_mode", "main") == "main" else ""
        if key == "today_checked":
            tail = "더블클릭 또는 Space로 체크 · 체크하면 현재상태를 확정하고 기록합니다"
        elif key == "sheet_status":
            tail = "선택 후 오늘확인을 체크해야 확정됩니다"
        elif key:
            tail = "수정 가능 · 더블클릭 또는 Enter"
        else:
            tail = "프로그램이 채우는 칸"
        text = f"[{title or iid}]  {name}: {value or '(비어 있음)'}    ({tail})"
        try:
            label_widget.configure(text=text, fg=COLORS["text"] if value else COLORS["text_muted"])
        except Exception:
            pass

    def _on_record_tree_click(self, event) -> None:
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        if tree.identify_region(event.x, event.y) in ("heading", "separator"):
            return
        row = tree.identify_row(event.y)
        index = self._record_col_index_at(tree, event.x)
        if index >= 0:
            self._record_click_col = index
        if row and str(row).startswith("__grp"):
            return "break"
        if row and index >= 0:
            self.root.after_idle(lambda: self._show_record_detail(row, index))

    def _on_record_tree_menu(self, event):
        tree = getattr(self, "_record_tree", None)
        menu = getattr(self, "_record_menu", None)
        if not self._widget_alive(tree) or menu is None or getattr(self, "_record_mode", "main") != "main":
            return
        row = tree.identify_row(event.y)
        if not row or str(row).startswith("__"):
            return
        self._close_record_edit(True)
        self._record_menu_target = row
        self._select_blog(row)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                menu.grab_release()
            except Exception:
                pass
        return "break"

    def _on_record_tree_space(self, _event=None):
        """선택한 줄의 오늘확인을 토글한다."""
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree) or getattr(self, "_record_mode", "main") != "main":
            return
        selected = tree.selection()
        if not selected or str(selected[0]).startswith("__"):
            return "break"
        self._close_record_edit(True)
        self._toggle_today_check(selected[0])
        if "오늘확인" in hr.HOME_HEADERS:
            self._show_record_detail(selected[0], hr.HOME_HEADERS.index("오늘확인"))
        return "break"

    def _on_record_tree_enter(self, _event=None):
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        selected = tree.selection()
        if not selected or str(selected[0]).startswith("__"):
            return "break"
        index = int(getattr(self, "_record_click_col", 0) or 0)
        editable = self._record_editable_indexes()
        if editable and index not in editable:
            index = min(editable, key=lambda i: abs(i - index))
        self._edit_record_cell(selected[0], index)
        return "break"

    # ----- 기록 표: 찾기 / 정렬 ----------------------------------------------------

    def _on_record_query_changed(self, *_args) -> None:
        self._after_once("record_query", 120, self._arrange_record_rows)

    def _sort_record_tree(self, name: str) -> None:
        current = getattr(self, "_record_sort", None)
        if current is None or current[0] != name:
            self._record_sort = (name, False)
        elif current[1] is False:
            self._record_sort = (name, True)
        else:
            self._record_sort = None
        self._arrange_record_rows()

    def _record_sort_key(self, value: str):
        text = str(value or "").strip()
        if not text:
            return (2, 0, "")
        try:
            return (0, float(text.replace(",", "")), "")
        except ValueError:
            return (1, 0, text.lower())

    def _arrange_record_rows(self) -> None:
        """찾기와 정렬을 한 번에 반영한다. 줄을 다시 만들지 않고 붙였다 떼기만 한다."""
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        headers = self._record_headers()
        log_mode = getattr(self, "_record_mode", "main") == "log"
        # 이전 묶음 머리글은 모두 지우고 다시 만든다 (실제 기록 줄은 그대로 둔다)
        for iid in list(tree.get_children("")):
            if str(iid).startswith("__grp"):
                try:
                    tree.delete(iid)
                except Exception:
                    pass
        all_iids = [iid for iid in (getattr(self, "_record_all_iids", None) or []) if tree.exists(iid)]
        order = list(all_iids)
        sort = getattr(self, "_record_sort", None)
        heading_text = {"계정 생성상태": "계정생성"}
        for name in (self._record_display_headers() if not log_mode else headers):
            label = heading_text.get(name, name)
            if sort and sort[0] == name:
                label = f"{label} {'▼' if sort[1] else '▲'}"
            try:
                if str(tree.heading(name, "text") or "") != label:
                    tree.heading(name, text=label)
            except Exception:
                pass
        sorted_by_col = bool(sort and sort[0] in headers)
        if sorted_by_col:
            col = headers.index(sort[0])

            def key_of(iid):
                values = tree.item(iid, "values")
                return self._record_sort_key(values[col] if col < len(values) else "")

            order.sort(key=key_of, reverse=bool(sort[1]))
        query = ""
        if hasattr(self, "record_query"):
            query = str(self.record_query.get() or "").strip().lower()
        # 이메일 탭: 처음 나온 순서대로, 개수와 함께
        counts: dict[str, int] = {}
        for iid in all_iids:
            email = self._record_row_email(iid)
            counts[email] = counts.get(email, 0) + 1
        self._rebuild_record_tabs(counts)
        email_filter = str(getattr(self, "_record_email_filter", "") or "")
        shown = 0
        for iid in order:
            values = tree.item(iid, "values")
            if email_filter and self._record_row_email(iid) != email_filter:
                try:
                    tree.detach(iid)
                except Exception:
                    pass
                continue
            if query and query not in " ".join(str(v) for v in values).lower():
                try:
                    tree.detach(iid)
                except Exception:
                    pass
                continue
            try:
                if tree.parent(iid) != "" or tree.index(iid) != shown:
                    tree.move(iid, "", shown)
            except Exception:
                pass
            shown += 1
        count_label = getattr(self, "_record_count_label", None)
        if self._widget_alive(count_label):
            unit = "로그" if log_mode else "기록"
            text = f"{unit} {len(all_iids)}개 · 이메일 {len(counts)}개"
            if email_filter or query:
                text += f" · 보이는 {shown}개"
            count_label.configure(text=text)
        self._paint_record_rows()

    # ----- 기록 표: 이메일 탭 ------------------------------------------------------

    def _record_row_email(self, iid: str) -> str:
        tree = getattr(self, "_record_tree", None)
        if getattr(self, "_record_mode", "main") == "log":
            return str((getattr(self, "_log_email", None) or {}).get(iid) or "").strip() or RECORD_NO_EMAIL
        headers = self._record_headers()
        col = headers.index("로그인 이메일") if "로그인 이메일" in headers else -1
        if col < 0 or not self._widget_alive(tree):
            return RECORD_NO_EMAIL
        try:
            values = tree.item(iid, "values")
        except Exception:
            return RECORD_NO_EMAIL
        return str(values[col] if col < len(values) else "").strip() or RECORD_NO_EMAIL

    def _rebuild_record_tabs(self, counts: dict[str, int]) -> None:
        host = getattr(self, "_record_tab_host", None)
        if not self._widget_alive(host):
            return
        total = sum(counts.values())
        saved = [str(item).strip() for item in ((self.__dict__.get("_home_state") or {}).get("email_order") or []) if str(item).strip()]
        seen = {item.lower() for item in saved}
        ordered: list[tuple[str, int]] = []
        for email in saved:
            match = next((key for key in counts if key != RECORD_NO_EMAIL and key.lower() == email.lower()), "")
            if match:
                ordered.append((match, counts[match]))
        for email, count in counts.items():
            if email == RECORD_NO_EMAIL or email.lower() in seen:
                continue
            ordered.append((email, count))
            seen.add(email.lower())
        if RECORD_NO_EMAIL in counts:
            ordered.append((RECORD_NO_EMAIL, counts[RECORD_NO_EMAIL]))
        sig = tuple(ordered)
        btns = getattr(self, "_record_tab_btns", None) or {}
        if sig == getattr(self, "_record_tab_sig", None) and btns and all(self._widget_alive(b) for b in btns.values()):
            return
        self._record_tab_sig = sig
        for child in list(host.winfo_children()):
            try:
                child.destroy()
            except Exception:
                pass
        btns = {}
        items = [("", f"전체  {total}")] + [(email, f"{email}  {count}") for email, count in ordered]
        for key, text in items:
            btn = tk.Label(host, text=text, font=FONTS["small_bold"], padx=12, pady=5, cursor="hand2")
            btn._keep_bg = True
            btn.bind("<Button-1>", lambda _e, k=key: self._set_record_email_filter(k))
            btns[key] = btn
        self._record_tab_btns = btns
        if str(getattr(self, "_record_email_filter", "") or "") not in btns:
            self._record_email_filter = ""
        self._paint_record_tabs()
        self._reflow_record_tabs()

    def _paint_record_tabs(self) -> None:
        current = str(getattr(self, "_record_email_filter", "") or "")
        for key, btn in (getattr(self, "_record_tab_btns", None) or {}).items():
            if not self._widget_alive(btn):
                continue
            if key == current:
                bg, fg = COLORS["accent"], "#ffffff"
            elif key == "":
                bg, fg = COLORS["chip_bg"], COLORS["text"]
            else:
                tag = self._record_email_tag(key)
                try:
                    bg = RECORD_EMAIL_PALETTE[int(tag.replace("email", "")) % len(RECORD_EMAIL_PALETTE)]
                except Exception:
                    bg = COLORS["chip_bg"]
                fg = COLORS["text"]
            try:
                btn.configure(bg=bg, fg=fg)
            except Exception:
                pass

    def _reflow_record_tabs(self) -> None:
        """탭이 한 줄에 다 안 들어가면 다음 줄로 접는다. 표를 가리지 않는다."""
        host = getattr(self, "_record_tab_host", None)
        if not self._widget_alive(host):
            return
        width = host.winfo_width()
        if width <= 1:
            width = 980
        x = row = col = 0
        for btn in (getattr(self, "_record_tab_btns", None) or {}).values():
            if not self._widget_alive(btn):
                continue
            need = btn.winfo_reqwidth() + 6
            if col and x + need > width:
                row += 1
                col = 0
                x = 0
            btn.grid(row=row, column=col, padx=(0, 6), pady=(0, 4), sticky="w")
            x += need
            col += 1

    def _set_record_email_filter(self, key: str) -> None:
        if str(getattr(self, "_record_email_filter", "") or "") == key:
            return
        self._record_email_filter = key
        self._paint_record_tabs()
        self._arrange_record_rows()

    def _refresh_record_tree_item(self, blog_id: str) -> None:
        if not blog_id:
            return
        blog = next((item for item in self._record_blogs() if item.id == blog_id), None)
        if blog is None:
            self._schedule_record_view_refresh()
            return
        tree = getattr(self, "_record_tree", None)
        if self._widget_alive(tree) and getattr(self, "_record_mode", "main") != "log":
            try:
                if tree.exists(blog_id):
                    record = self._home_record(blog)
                    tree.item(blog_id, values=hr.record_values(record), tags=self._record_tags(record))
            except Exception:
                pass
        view = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(view):
            return
        work = self._work_record(blog)
        try:
            if view.exists(blog_id):
                view.item(blog_id, values=work["values"], tags=work["tags"])
                self._record_view_fp = None
            else:
                self._schedule_record_view_refresh()
        except Exception:
            self._schedule_record_view_refresh()

    def _home_record(self, blog: BlogInfo, last_events: dict[str, str] | None = None) -> dict:
        meta = self._blog_meta.get(blog.id) or {}
        if last_events is None:
            last_events = self._last_event_map()
        return hr.build_record(
            meta, blog_id=blog.id, address=str(blog.address or meta.get("address") or ""),
            title=str(blog.name or meta.get("name") or ""), last_event_ts=last_events.get(blog.id, ""),
        )

    def _last_event_map(self) -> dict[str, str]:
        out: dict[str, str] = {}
        for event in self._home_events():
            blog_id = str(event.get("blog_id") or "")
            ts = str(event.get("ts") or "")
            if blog_id and ts >= out.get(blog_id, ""):
                out[blog_id] = ts
        return out

    def _record_tags(self, record: dict) -> tuple:
        """줄 색: 노출됨·잘림·삭제됨은 시트 조건부서식, 그 외는 이메일 색."""
        status = hr.normalize_status(record.get("현재상태"))
        if status in hr.ROW_HIGHLIGHT:
            return (f"st_{status}",)
        email = str(record.get("로그인 이메일") or "").strip() or RECORD_NO_EMAIL
        return (self._record_email_tag(email),)

    def _record_email_tag(self, email: str) -> str:
        tones = getattr(self, "_record_email_tones", None)
        if not isinstance(tones, dict):
            tones = {}
            self._record_email_tones = tones
        if email not in tones:
            tones[email] = f"email{len(tones) % len(RECORD_EMAIL_PALETTE)}"
        return tones[email]

    def _on_record_tree_select(self, _event=None) -> None:
        if getattr(self, "_records_rendering", False):
            return
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        selected = tree.selection()
        if selected and not str(selected[0]).startswith("__"):
            self._select_blog(selected[0])

    def _on_record_tree_double(self, event):
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        if tree.identify_region(event.x, event.y) in ("heading", "separator"):
            return
        row = tree.identify_row(event.y)
        index = self._record_col_index_at(tree, event.x)
        if not row or index < 0 or str(row).startswith("__grp"):
            return
        if str(row).startswith("__log"):
            self._show_record_detail(row, index)
            return "break"
        self._select_blog(row)
        self._edit_record_cell(row, index)
        return "break"

    def _render_record_rows(self, force: bool = False) -> None:
        return
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        if not force and getattr(self, "_main_tab", "") != "기록":
            self._record_dirty = True
            return
        if getattr(self, "_record_mode", "main") == "log":
            self._render_log_rows()
            return
        live = self._dashboard_blogs()
        self._fill_program_records(live)
        blogs = self._record_blogs()
        last_events = self._last_event_map()
        records = [self._home_record(blog, last_events) for blog in blogs]
        fp = tuple(tuple(hr.record_values(record)) for record in records)
        all_iids = getattr(self, "_record_all_iids", None) or []
        if fp == getattr(self, "_record_fp", None) and all_iids and all(tree.exists(iid) for iid in all_iids):
            self._record_dirty = False
            self._paint_record_rows()
            return
        self._close_record_edit(True)
        self._records_rendering = True
        try:
            self._record_fp = fp
            self._record_dirty = False
            self._record_email_tones = {}
            # 시트의 sortMasterRows_: 삭제됨 뒤로 → 이메일 → 프로그램 목록 순서/키워드 우선순위 → 처음수집 → 첫색인 → 상태
            state = self.__dict__.get("_home_state") or {}
            ordered = hr.sort_records(records, state.get("email_order") or [], state.get("program_order") or {})
            # 이미 있는 줄은 값만 바꾸고, 없어진 줄만 지우고, 새 줄만 넣는다. 전체를 지웠다 다시 만들지 않는다.
            wanted = [str(record["_id"]) for record in ordered]
            wanted_set = set(wanted)
            existing = set(all_iids) | set(tree.get_children(""))
            for iid in list(existing):
                if iid not in wanted_set:
                    try:
                        tree.delete(iid)
                    except Exception:
                        pass
            for record in ordered:
                iid = str(record["_id"])
                values = hr.record_values(record)
                tags = self._record_tags(record)
                try:
                    if tree.exists(iid):
                        tree.item(iid, values=values, tags=tags)
                    else:
                        tree.insert("", "end", iid=iid, values=values, tags=tags)
                except Exception:
                    pass
            self._record_all_iids = wanted
        finally:
            self._records_rendering = False
        self._arrange_record_rows()
        self._fill_record_view()

    def _render_log_rows(self) -> None:
        """변경 로그(AE:AK) 보기. 최신이 위."""
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        events = list(self._home_events())
        fp = ("log", len(events), str(events[-1].get("ts") if events else ""))
        all_iids = getattr(self, "_record_all_iids", None) or []
        if fp == getattr(self, "_record_fp", None) and all_iids and all(tree.exists(iid) for iid in all_iids):
            return
        self._close_record_edit(True)
        self._records_rendering = True
        try:
            self._record_fp = fp
            self._record_dirty = False
            for iid in list(tree.get_children("")) + list(all_iids):
                try:
                    if tree.exists(iid):
                        tree.delete(iid)
                except Exception:
                    pass
            wanted = []
            emails: dict[str, str] = {}
            for pos, event in enumerate(reversed(events)):
                iid = f"__log_{len(events) - pos}"
                try:
                    tree.insert("", "end", iid=iid, values=hr.log_values(event), tags=("log_row",))
                except Exception:
                    continue
                wanted.append(iid)
                emails[iid] = str(event.get("email") or "").strip()
            self._record_all_iids = wanted
            self._log_email = emails
        finally:
            self._records_rendering = False
        self._arrange_record_rows()

    def _paint_record_rows(self) -> None:
        tree = getattr(self, "_record_tree", None)
        if not self._widget_alive(tree):
            return
        selected = (self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""
        current = tree.selection()
        busy = getattr(self, "_records_rendering", False)
        self._records_rendering = True
        try:
            if selected and tree.exists(selected):
                if current != (selected,):
                    tree.selection_set(selected)
                    tree.focus(selected)
                    if getattr(self, "_main_tab", "") == "기록" and tree.parent(selected) == "" and selected in tree.get_children(""):
                        tree.see(selected)
            elif current:
                tree.selection_remove(*current)
        except Exception:
            pass
        finally:
            if not busy:
                self._records_rendering = False

    def _record_col_px(self, name: str) -> int:
        return max(56, int(hr.COL_CHARS.get(name, 10) * 8.2))

    def on_open_record_view(self) -> None:
        self._close_record_ui()
        return
        self._record_view_email = ""
        self._record_view_fp = None
        self._record_view_tab_sig = None
        if hasattr(self, "record_view_query"):
            try:
                self.record_view_query.set("")
            except Exception:
                pass
        win = getattr(self, "_record_view_win", None)
        if self._widget_alive(win):
            tree = getattr(self, "_record_view_tree", None)
            cols = tuple(item[0] for item in RECORD_VIEW_COLS)
            current = ()
            try:
                if self._widget_alive(tree):
                    current = tuple(str(item) for item in (tree.cget("columns") or ()))
            except Exception:
                current = ()
            if current == cols:
                try:
                    win.lift()
                    win.focus_force()
                except Exception:
                    pass
                self._fill_record_view()
                self._reveal_blog_in_record_view(str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else "")
                return
            try:
                win.destroy()
            except Exception:
                pass
            self._record_view_win = None
            self._record_view_tree = None
        win = tk.Toplevel(self.root)
        self._record_view_win = win
        win.title("기록 보기")
        win.configure(bg=COLORS["card"])
        try:
            win.minsize(980, 560)
        except Exception:
            pass
        inner = tk.Frame(win, bg=COLORS["card"])
        inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=10)

        title_row = tk.Frame(inner, bg=COLORS["card"])
        title_row.pack(fill=tk.X)
        tk.Label(title_row, text="작업 기록", font=FONTS["heading"], fg=COLORS["text"], bg=COLORS["card"]).pack(side=tk.LEFT)
        self._record_view_count = tk.Label(title_row, text="", font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["card"])
        self._record_view_count.pack(side=tk.RIGHT)

        tabs = tk.Frame(inner, bg=COLORS["card"])
        tabs.pack(fill=tk.X, pady=(6, 2))
        self._record_view_tab_host = tabs
        self._record_view_tab_btns = {}
        self._record_view_email = ""

        tools = tk.Frame(inner, bg=COLORS["card"])
        tools.pack(fill=tk.X, pady=(2, 4))
        tk.Label(tools, text="찾기", font=FONTS["small_bold"], fg=COLORS["text_muted"], bg=COLORS["card"]).pack(side=tk.LEFT)
        if not hasattr(self, "record_view_query"):
            self.record_view_query = tk.StringVar(value="")
            self._trace_var(self.record_view_query, lambda *_: self._after_once("record_view_query", 120, self._fill_record_view))
        search = tk.Entry(
            tools, textvariable=self.record_view_query, font=FONTS["body"], width=28,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"], highlightcolor=COLORS["accent"],
        )
        search.pack(side=tk.LEFT, padx=(6, 6), ipady=3)
        flat_button(tools, "지우기", variant="ghost", command=lambda: self.record_view_query.set("")).pack(side=tk.LEFT)
        tk.Label(
            tools,
            text="노출 칸을 누르면 노출/미노출 · 더블클릭하면 메모 · 아래는 날짜별 실행 로그",
            font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["card"],
        ).pack(side=tk.RIGHT)

        wrap = tk.Frame(inner, bg=COLORS["card"])
        wrap.pack(fill=tk.BOTH, expand=True)
        wrap.grid_rowconfigure(0, weight=1)
        wrap.grid_columnconfigure(0, weight=1)
        style = ttk.Style(wrap)
        try:
            style.configure(
                "RecordView.Treeview",
                font=FONTS["body"],
                rowheight=28,
                background=COLORS["card"],
                fieldbackground=COLORS["card"],
                foreground=COLORS["text"],
                borderwidth=0,
            )
            style.configure("RecordView.Treeview.Heading", font=FONTS["small_bold"], padding=(6, 4))
            style.map("RecordView.Treeview", background=[("selected", "#c7d2fe")], foreground=[("selected", COLORS["text"])])
        except Exception:
            pass
        cols = [item[0] for item in RECORD_VIEW_COLS]
        tree = ttk.Treeview(
            wrap,
            columns=cols,
            show="headings",
            selectmode="browse",
            style="RecordView.Treeview",
        )
        self._record_view_tree = tree
        ybar = tk.Scrollbar(wrap, orient="vertical", command=tree.yview)
        xbar = tk.Scrollbar(wrap, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
        tree.grid(row=0, column=0, sticky="nsew")
        ybar.grid(row=0, column=1, sticky="ns")
        xbar.grid(row=1, column=0, sticky="ew")
        detail_host = tk.Frame(inner, bg=COLORS["card"])
        detail_host.pack(fill=tk.X, pady=(8, 0))
        tk.Label(
            detail_host, text="선택한 블로그 실행 로그", font=FONTS["small_bold"],
            fg=COLORS["text_muted"], bg=COLORS["card"],
        ).pack(anchor="w")
        detail = tk.Text(
            detail_host, font=FONTS["small"], wrap=tk.WORD, height=7,
            bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
            highlightthickness=1, highlightbackground=COLORS["border"], highlightcolor=COLORS["accent"],
            takefocus=0,
        )
        detail.pack(fill=tk.X, pady=(4, 0))
        detail.configure(state="disabled")
        self._record_view_detail = detail
        for index, color in enumerate(RECORD_EMAIL_PALETTE):
            tree.tag_configure(f"email{index}", background=color)
        for state, (bg, fg) in hr.ROW_HIGHLIGHT.items():
            options = {"background": bg}
            if fg:
                options["foreground"] = fg
            tree.tag_configure(f"st_{state}", **options)
        self._record_view_sort = None
        self._record_view_autosized = False
        self._apply_record_view_columns()
        tree.bind("<<TreeviewSelect>>", self._on_record_view_select)
        tree.bind("<ButtonRelease-1>", self._on_record_view_click)
        tree.bind("<Double-1>", self._on_record_view_double)

        def on_close() -> None:
            self._record_view_win = None
            self._record_view_tree = None
            self._record_view_tab_host = None
            self._record_view_tab_btns = {}
            self._record_view_fp = None
            self._record_view_detail = None
            memo = getattr(self, "_work_memo_win", None)
            if self._widget_alive(memo):
                try:
                    memo.destroy()
                except Exception:
                    pass
            self._work_memo_win = None
            try:
                win.destroy()
            except Exception:
                pass

        win.protocol("WM_DELETE_WINDOW", on_close)
        self._place_record_view(win)
        self._fill_record_view()
        self._reveal_blog_in_record_view(str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else "")
        self._after_once("record_view_open", 80, lambda: self._reveal_blog_in_record_view(str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""))

    def _place_record_view(self, win) -> None:
        try:
            win.update_idletasks()
            screen_w = win.winfo_screenwidth()
            screen_h = win.winfo_screenheight()
            max_w = max(980, int(screen_w * 0.92))
            max_h = max(560, int(screen_h * 0.86))
            width = min(max_w, max(1180, int(screen_w * 0.84)))
            height = min(max_h, max(720, int(screen_h * 0.78)))
            x = self.root.winfo_rootx() + 24
            y = self.root.winfo_rooty() + 24
            x = min(max(0, x), max(0, screen_w - width))
            y = min(max(0, y), max(0, screen_h - height))
            win.geometry(f"{width}x{height}+{int(x)}+{int(y)}")
            win.maxsize(max_w, max_h)
        except Exception:
            try:
                win.geometry("1280x800")
            except Exception:
                pass

    def _apply_record_view_columns(self) -> None:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        cols = [item[0] for item in RECORD_VIEW_COLS]
        sort = getattr(self, "_record_view_sort", None)
        try:
            current = tuple(str(item) for item in (tree.cget("columns") or ()))
        except Exception:
            current = ()
        if current != tuple(cols):
            self._record_view_fp = None
            try:
                tree.configure(columns=cols, displaycolumns=cols, show="headings")
            except Exception:
                pass
        for key, title, width in RECORD_VIEW_COLS:
            label = title
            if sort and sort[0] == key:
                label = f"{title} {'▼' if sort[1] else '▲'}"
            try:
                tree.heading(key, text=label, anchor="w", command=lambda n=key: self._sort_record_view_col(n))
                tree.column(key, width=width, minwidth=64, stretch=False, anchor="w")
            except Exception:
                pass

    def _sort_record_view_home(self) -> None:
        self._record_view_sort = None
        self._fill_record_view()

    def _sort_record_view_col(self, name: str) -> None:
        current = getattr(self, "_record_view_sort", None)
        if current is None or current[0] != name:
            self._record_view_sort = (name, False)
        elif current[1] is False:
            self._record_view_sort = (name, True)
        else:
            self._record_view_sort = None
        self._fill_record_view()

    def _on_record_view_select(self, _event=None) -> None:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        selected = tree.selection()
        pick = selected[0] if selected and not str(selected[0]).startswith("__") else ""
        if getattr(self, "_syncing_record_pick", False):
            if pick:
                self._show_record_view_detail(pick)
            return
        if pick:
            self._reveal_blog_in_list(pick)
            self._show_record_view_detail(pick)

    def _on_record_view_click(self, event) -> None:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        if tree.identify_region(event.x, event.y) in ("heading", "separator"):
            return
        row = tree.identify_row(event.y)
        if row and not str(row).startswith("__"):
            if getattr(self, "_syncing_record_pick", False):
                self._show_record_view_detail(row)
                return
            self._reveal_blog_in_list(row)
            self._show_record_view_detail(row)
            if self._record_view_col_key(event.x) == "shown":
                self._edit_work_shown(row)

    def _on_record_view_double(self, event) -> None:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        if tree.identify_region(event.x, event.y) in ("heading", "separator"):
            return
        row = tree.identify_row(event.y)
        if row and not str(row).startswith("__"):
            if self._record_view_col_key(event.x) == "shown":
                self._edit_work_shown(row)
                return "break"
            self._open_work_memo(row)
            return "break"

    def _record_view_col_key(self, x) -> str:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return ""
        col = tree.identify_column(x)
        try:
            index = int(str(col).replace("#", "")) - 1
        except ValueError:
            return ""
        keys = [item[0] for item in RECORD_VIEW_COLS]
        if 0 <= index < len(keys):
            return keys[index]
        return ""

    def _work_shown_label(self, status: str) -> str:
        if hr.normalize_status(status) in ("노출됨", "별도키워드노출"):
            return "노출"
        return "미노출"

    def _close_work_shown_edit(self, apply: bool = True) -> None:
        editor = getattr(self, "_work_shown_editor", None)
        self._work_shown_editor = None
        if not editor:
            return
        widget = editor.get("widget")
        blog_id = str(editor.get("blog_id") or "")
        value = ""
        try:
            value = str(widget.get() or "").strip()
        except Exception:
            value = ""
        try:
            widget.destroy()
        except Exception:
            pass
        if apply and blog_id and value in ("노출", "미노출"):
            self._apply_work_shown(blog_id, value == "노출")

    def _edit_work_shown(self, blog_id: str) -> None:
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree) or not blog_id or str(blog_id).startswith("__"):
            return
        self._close_work_shown_edit(True)
        try:
            if not tree.exists(blog_id):
                return
            tree.see(blog_id)
            tree.update_idletasks()
            index = [item[0] for item in RECORD_VIEW_COLS].index("shown")
            bbox = tree.bbox(blog_id, f"#{index + 1}")
        except Exception:
            bbox = None
        if not bbox:
            return
        x, y, width, height = bbox
        meta = self._blog_meta.get(blog_id) or {}
        current = self._work_shown_label(meta.get("confirmed_status") or meta.get("sheet_status"))
        widget = ttk.Combobox(tree, values=("노출", "미노출"), state="readonly", font=FONTS["body"])
        widget.set(current)
        widget.place(x=x, y=y, width=max(width, 90), height=max(height, 24))
        widget.focus_set()
        self._work_shown_editor = {"widget": widget, "blog_id": blog_id}
        widget.bind("<<ComboboxSelected>>", lambda _e: self._close_work_shown_edit(True))
        widget.bind("<Escape>", lambda _e: (self._close_work_shown_edit(False), "break")[1])
        widget.bind("<FocusOut>", lambda _e, w=widget: self._after_once("work_shown_blur", 150, lambda: self._work_shown_blur(w)))

    def _work_shown_blur(self, widget) -> None:
        editor = getattr(self, "_work_shown_editor", None)
        if editor is None or editor.get("widget") is not widget:
            return
        try:
            focus = widget.winfo_toplevel().focus_get()
        except Exception:
            return
        if focus is widget:
            return
        self._close_work_shown_edit(True)

    def _apply_work_shown(self, blog_id: str, shown: bool) -> None:
        cur = self._blog_meta.setdefault(blog_id, {})
        current = hr.normalize_status(cur.get("confirmed_status") or cur.get("sheet_status"))
        if shown:
            if current == "노출됨":
                return
            self._confirm_record(blog_id, "노출됨", source="수동", check_today=True)
            return
        if current not in ("노출됨", "별도키워드노출"):
            return
        if cur.get("naver_indexed") is False:
            nxt = "미색인"
        elif cur.get("naver_indexed") is True or hr.has_index_history(cur):
            nxt = "색인됨"
        else:
            nxt = "색인됨"
        self._confirm_record(blog_id, nxt, source="수동", check_today=True)

    def _step_label(self, done: set[str], keys: tuple[str, ...], *, done_text: str, empty_text: str) -> str:
        finished = [key for key in keys if key in done]
        pending = [SETTING_NAME.get(key, key) for key in keys if key not in done]
        if not pending and finished:
            return done_text
        if not finished:
            return empty_text
        return f"{len(finished)}/{len(keys)} 완료 · {' · '.join(pending)} 남음"

    def _step_marks(self, done: set[str], keys: tuple[str, ...]) -> str:
        parts = []
        for key in keys:
            name = SETTING_NAME.get(key, key)
            parts.append(f"완료 {name}" if key in done else f"남음 {name}")
        return " · ".join(parts)

    def _work_record(self, blog: BlogInfo) -> dict:
        meta = self._blog_meta.get(blog.id) or {}
        done = set(getattr(blog, "done", set()) or [])
        done.update(self._progress_map.get(blog.id) or [])
        created = hr.md(meta.get("created_date")) or "—"
        settings_when = self._fmt_when(str(meta.get("settings_applied_at") or ""))
        settings_done = "완료" + (f" · {settings_when}" if settings_when else "")
        settings = self._step_label(done, SETTINGS_APPLY_KEYS, done_text=settings_done, empty_text="미적용")
        first = str(meta.get("blog_collect_at") or meta.get("last_blog_crawl") or "")
        first_when = self._fmt_when(first)
        posts = len(blog.posts or [])
        if "collect" in done and "collect_post" in done:
            collect_done = "완료" + (f" · {first_when}" if first_when else "")
            if posts:
                collect_done += f" · 글 {posts}"
        elif "collect" in done:
            collect_done = "블로그수집" + (f" · {first_when}" if first_when else "") + " · 글 미수집"
        else:
            collect_done = "미수집"
        collect = self._step_label(done, FIRST_COLLECT_KEYS, done_text=collect_done, empty_text="미수집")
        if "collect" in done and "collect_post" not in done:
            collect = collect_done
        index_name, _tone, extra = self._index_status_view(blog)
        index = index_name if not extra else f"{index_name} · {extra}"
        status = hr.normalize_status(meta.get("confirmed_status") or meta.get("sheet_status"))
        shown = self._work_shown_label(status)
        if shown == "노출":
            when = self._fmt_when(str(meta.get("first_core") or meta.get("last_core") or ""))
            extra_kw = str(meta.get("exposed_keyword") or "").strip()
            if status == "별도키워드노출" and extra_kw:
                shown = f"노출 · {extra_kw}"
            elif when:
                shown = f"노출 · {when}"
        recrawl_n = self._count_value(meta.get("blog_crawl_count"))
        recrawl = f"{recrawl_n}회"
        if recrawl_n:
            last = self._fmt_when(str(meta.get("last_blog_crawl") or ""))
            if last:
                recrawl += f" · {last}"
        note = " ".join(str(meta.get("sheet_note") or "").split())
        title = str(blog.name or meta.get("name") or meta.get("h1") or blog.address or blog.id)
        keyword = str(meta.get("keyword") or "")
        values = (
            title,
            created,
            keyword,
            settings,
            collect,
            index,
            shown,
            recrawl,
            note,
        )
        detail_lines = [
            title,
            f"생성일 {created}" + (f"  ·  키워드 {keyword}" if keyword else ""),
            f"설정적용  {settings}",
            f"  {self._step_marks(done, SETTINGS_APPLY_KEYS)}",
            f"최초수집  {collect}",
            f"  {self._step_marks(done, FIRST_COLLECT_KEYS)}",
            f"색인확인  {index}",
            f"노출  {shown}",
            f"재수집  {recrawl}",
        ]
        if note:
            detail_lines.append(f"메모  {note}")
        flow = str(meta.get("status_flow") or "").strip()
        if flow:
            detail_lines.append(f"흐름  {flow}")
        if status in hr.ROW_HIGHLIGHT:
            tags = (f"st_{status}",)
        else:
            email = str(meta.get("google_email") or "").strip() or RECORD_NO_EMAIL
            tags = (self._record_email_tag(email),)
        return {
            "_id": blog.id,
            "email": str(meta.get("google_email") or "").strip() or RECORD_NO_EMAIL,
            "values": values,
            "tags": tags,
            "search": " ".join(str(item) for item in values).lower(),
            "status": status,
            "detail": "\n".join(detail_lines),
        }

    def _schedule_record_view_refresh(self) -> None:
        return
        if not self._widget_alive(getattr(self, "_record_view_win", None)):
            return
        self._after_once("record_view", 80, self._fill_record_view)

    def _work_sorted_rows(self) -> list[dict]:
        live = self._dashboard_blogs()
        self._fill_program_records(live)
        blogs = self._record_blogs()
        rows = [self._work_record(blog) for blog in blogs]
        last_events = self._last_event_map()
        home = [self._home_record(blog, last_events) for blog in blogs]
        state = self.__dict__.get("_home_state") or {}
        ordered_home = hr.sort_records(home, state.get("email_order") or [], state.get("program_order") or {})
        work_map = {row["_id"]: row for row in rows}
        ordered = [work_map[str(item.get("_id"))] for item in ordered_home if str(item.get("_id")) in work_map]
        for blog_id, row in work_map.items():
            if row not in ordered:
                ordered.append(row)
        sort = getattr(self, "_record_view_sort", None)
        keys = [item[0] for item in RECORD_VIEW_COLS]
        if sort and sort[0] in keys:
            col = keys.index(sort[0])

            def key_of(row):
                values = row.get("values") or ()
                return self._record_sort_key(values[col] if col < len(values) else "")

            ordered.sort(key=key_of, reverse=bool(sort[1]))
        return ordered

    def _open_work_memo(self, blog_id: str) -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        meta = self._blog_meta.setdefault(blog_id, {})
        title = str(meta.get("name") or meta.get("h1") or meta.get("address") or blog_id[-6:])
        win = getattr(self, "_work_memo_win", None)
        if self._widget_alive(win):
            try:
                win.lift()
                win.focus_force()
            except Exception:
                pass
        else:
            parent = getattr(self, "_record_view_win", None)
            win = tk.Toplevel(parent if self._widget_alive(parent) else self.root)
            self._work_memo_win = win
            win.title("메모")
            win.configure(bg=COLORS["card"])
            try:
                win.minsize(420, 280)
            except Exception:
                pass
            inner = tk.Frame(win, bg=COLORS["card"])
            inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=10)
            self._work_memo_title = tk.Label(
                inner, text="", font=FONTS["heading"], fg=COLORS["text"], bg=COLORS["card"], anchor="w",
            )
            self._work_memo_title.pack(fill=tk.X)
            tk.Label(
                inner, text="이 블로그에서 한 일을 적어 두면 기록보기에서 바로 보입니다.",
                font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["card"], anchor="w",
            ).pack(fill=tk.X, pady=(2, 6))
            text = tk.Text(
                inner, font=FONTS["body"], wrap=tk.WORD, height=10,
                bg=COLORS["input_bg"], fg=COLORS["text"], relief="flat",
                highlightthickness=1, highlightbackground=COLORS["border"], highlightcolor=COLORS["accent"],
            )
            text.pack(fill=tk.BOTH, expand=True)
            self._work_memo_text = text
            btns = tk.Frame(inner, bg=COLORS["card"])
            btns.pack(fill=tk.X, pady=(8, 0))
            flat_button(btns, "저장", variant="primary", command=self._save_work_memo).pack(side=tk.RIGHT)
            flat_button(btns, "닫기", variant="ghost", command=lambda: on_close()).pack(side=tk.RIGHT, padx=(0, 6))

            def on_close() -> None:
                self._work_memo_win = None
                self._work_memo_text = None
                self._work_memo_id = ""
                try:
                    win.destroy()
                except Exception:
                    pass

            win.protocol("WM_DELETE_WINDOW", on_close)
            try:
                win.geometry("520x360")
            except Exception:
                pass
        self._work_memo_id = blog_id
        title_lbl = getattr(self, "_work_memo_title", None)
        if self._widget_alive(title_lbl):
            title_lbl.configure(text=title)
        box = getattr(self, "_work_memo_text", None)
        if self._widget_alive(box):
            box.delete("1.0", tk.END)
            box.insert("1.0", str(meta.get("sheet_note") or ""))
            try:
                box.focus_set()
            except Exception:
                pass

    def _save_work_memo(self) -> None:
        blog_id = str(getattr(self, "_work_memo_id", "") or "")
        box = getattr(self, "_work_memo_text", None)
        if not blog_id or not self._widget_alive(box):
            return
        try:
            value = box.get("1.0", "end-1c")
        except Exception:
            value = ""
        self._set_record_field(blog_id, "sheet_note", value)
        self._schedule_record_view_refresh()
        win = getattr(self, "_work_memo_win", None)
        if self._widget_alive(win):
            try:
                win.destroy()
            except Exception:
                pass
        self._work_memo_win = None
        self._work_memo_text = None
        self._work_memo_id = ""

    def _reveal_blog_in_list(self, blog_id: str) -> None:
        """기록보기에서 고른 줄의 블로그를 목록 가운데로 보여 준다."""
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        blog_id = self._live_blog_id(blog_id)
        if not blog_id:
            return
        self._syncing_record_pick = True
        try:
            prev = str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""
            if prev != blog_id:
                self._select_blog(blog_id)
            else:
                self._paint_rows_for(blog_id)
            if self.blog_var.get() != blog_id:
                self.blog_var.set(blog_id)
                self._paint_rows_for(blog_id)
        finally:
            self._syncing_record_pick = False
        wait = 40
        if getattr(self, "_blog_filter", "all") != "all":
            self._set_blog_filter("all")
            wait = 120
        if hasattr(self, "blog_query") and str(self.blog_query.get() or "").strip():
            self.blog_query.set("")
            wait = 120
        self._vis_key = None
        self._apply_blog_visibility()
        was = str(getattr(self, "_main_tab", "") or "")
        self._show_main_tab("블로그")
        if was != "블로그":
            wait = max(wait, 120)
        if getattr(self, "_main_tab", "") == "블로그" and (getattr(self, "_detail_dirty", False) or prev != blog_id):
            self._render_blog_detail()
        self._scroll_blog_list_to(blog_id)
        self._after_once("reveal_blog", wait, lambda: self._scroll_blog_list_to(blog_id, tries=8, wait=50))
        win = getattr(self, "_record_view_win", None)
        tree = getattr(self, "_record_view_tree", None)
        if self._widget_alive(win):
            try:
                win.lift()
            except Exception:
                pass
        if self._widget_alive(tree):
            try:
                tree.focus_set()
            except Exception:
                pass

    def _reveal_blog_in_record_view(self, blog_id: str) -> None:
        return
        """목록에서 고른 블로그를 열린 작업 기록 창에서 보이게 한다."""
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        win = getattr(self, "_record_view_win", None)
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(win) or not self._widget_alive(tree):
            return
        self._syncing_record_pick = True
        try:
            exists = False
            try:
                exists = bool(tree.exists(blog_id))
            except Exception:
                exists = False
            if not exists:
                changed = False
                if str(getattr(self, "_record_view_email", "") or ""):
                    self._record_view_email = ""
                    changed = True
                if hasattr(self, "record_view_query") and str(self.record_view_query.get() or "").strip():
                    self.record_view_query.set("")
                    changed = True
                if changed:
                    self._record_view_fp = None
                    self._paint_record_view_tabs()
                    self._fill_record_view()
                try:
                    exists = bool(tree.exists(blog_id))
                except Exception:
                    exists = False
            if not exists:
                return
            try:
                tree.selection_set(blog_id)
                tree.focus(blog_id)
                tree.see(blog_id)
            except Exception:
                pass
            self._show_record_view_detail(blog_id)
        finally:
            self._syncing_record_pick = False

    def _live_blog_id(self, blog_id: str) -> str:
        """기록 줄 아이디를 지금 목록에 있는 블로그 아이디로 맞춘다."""
        frames = getattr(self, "_blog_row_frames", None) or {}
        if blog_id in frames and self._widget_alive(frames.get(blog_id)):
            return blog_id
        live = {blog.id: blog for blog in self._dashboard_blogs()}
        if blog_id in live:
            return blog_id
        meta = self._blog_meta.get(blog_id) or {}
        name = str(meta.get("name") or meta.get("h1") or "").strip()
        address = str(meta.get("address") or "").strip().rstrip("/").lower()
        if name:
            for blog in live.values():
                if str(blog.name or "").strip() == name:
                    return blog.id
        if address:
            for blog in live.values():
                if str(blog.address or "").strip().rstrip("/").lower() == address:
                    return blog.id
        return blog_id

    def _scroll_blog_list_to(self, blog_id: str, tries: int = 0, wait: int = 40) -> None:
        blog_id = self._live_blog_id(blog_id)
        row = (getattr(self, "_blog_row_frames", None) or {}).get(blog_id)
        host = getattr(self, "blog_list", None)
        if not self._widget_alive(row) or not self._widget_alive(host):
            if tries > 0:
                if getattr(self, "_main_tab", "") == "블로그" and getattr(self, "_blog_dirty", False):
                    self._refresh_dashboard()
                self._after_once("reveal_blog", wait, lambda: self._scroll_blog_list_to(blog_id, tries - 1, wait))
            return
        if not row.winfo_ismapped():
            try:
                row.pack(fill=tk.X, pady=4, padx=2)
            except Exception:
                pass
            if tries > 0:
                self._after_once("reveal_blog", wait, lambda: self._scroll_blog_list_to(blog_id, tries - 1, wait))
            return
        if hasattr(host, "scroll_to_widget"):
            host.scroll_to_widget(row)
        self._paint_rows_for(blog_id)

    def _record_sorted_rows(self) -> list[dict]:
        live = self._dashboard_blogs()
        self._fill_program_records(live)
        blogs = self._record_blogs()
        last_events = self._last_event_map()
        records = [self._home_record(blog, last_events) for blog in blogs]
        state = self.__dict__.get("_home_state") or {}
        return hr.sort_records(records, state.get("email_order") or [], state.get("program_order") or {})

    def _fill_record_view(self) -> None:
        self._close_work_shown_edit(False)
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        rows = self._work_sorted_rows()
        query = ""
        if hasattr(self, "record_view_query"):
            query = str(self.record_view_query.get() or "").strip().lower()
        counts: dict[str, int] = {}
        for row in rows:
            email = str(row.get("email") or "").strip() or RECORD_NO_EMAIL
            counts[email] = counts.get(email, 0) + 1
        self._rebuild_record_view_tabs(counts)
        email_filter = str(getattr(self, "_record_view_email", "") or "")
        if email_filter and email_filter not in counts:
            self._record_view_email = ""
            email_filter = ""
            self._paint_record_view_tabs()
        self._apply_record_view_columns()
        visible = []
        for row in rows:
            email = str(row.get("email") or "").strip() or RECORD_NO_EMAIL
            if email_filter and email != email_filter:
                continue
            if query and query not in str(row.get("search") or ""):
                continue
            iid = str(row.get("_id") or "")
            if not iid:
                continue
            visible.append(row)
        if not visible and rows and (email_filter or query):
            self._record_view_email = ""
            if hasattr(self, "record_view_query"):
                self.record_view_query.set("")
            email_filter = ""
            query = ""
            self._paint_record_view_tabs()
            visible = [row for row in rows if str(row.get("_id") or "")]
        fp = tuple((str(row["_id"]), tuple(row["values"]), tuple(row["tags"])) for row in visible)
        if fp == getattr(self, "_record_view_fp", None):
            count = getattr(self, "_record_view_count", None)
            if self._widget_alive(count):
                text = f"기록 {len(rows)}개 · 이메일 {len(counts)}개"
                if email_filter or query:
                    text += f" · 보이는 {len(visible)}개"
                try:
                    if str(count.cget("text") or "") != text:
                        count.configure(text=text)
                except Exception:
                    pass
            pick = ""
            try:
                sel = list(tree.selection())
                pick = sel[0] if sel else ""
            except Exception:
                pick = ""
            self._show_record_view_detail(pick)
            return
        self._record_view_fp = fp
        try:
            y0 = tree.yview()[0]
        except Exception:
            y0 = 0
        try:
            selected = list(tree.selection())
        except Exception:
            selected = []
        wanted = [str(row["_id"]) for row in visible]
        wanted_set = set(wanted)
        try:
            existing = list(tree.get_children(""))
        except Exception:
            existing = []
        for iid in existing:
            if iid not in wanted_set:
                try:
                    tree.delete(iid)
                except Exception:
                    pass
        for row in visible:
            iid = str(row["_id"])
            try:
                if tree.exists(iid):
                    tree.item(iid, values=row["values"], tags=row["tags"])
                else:
                    tree.insert("", "end", iid=iid, values=row["values"], tags=row["tags"])
            except Exception:
                pass
        try:
            current = list(tree.get_children(""))
            for index, iid in enumerate(wanted):
                if index < len(current) and current[index] != iid and tree.exists(iid):
                    tree.move(iid, "", index)
                    current = list(tree.get_children(""))
        except Exception:
            pass
        keep = [iid for iid in selected if iid in wanted_set]
        current_blog = str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""
        if current_blog and current_blog in wanted_set:
            keep = [current_blog]
        try:
            if keep:
                was = getattr(self, "_syncing_record_pick", False)
                self._syncing_record_pick = True
                try:
                    tree.selection_set(keep)
                finally:
                    self._syncing_record_pick = was
            tree.yview_moveto(y0)
        except Exception:
            pass
        count = getattr(self, "_record_view_count", None)
        if self._widget_alive(count):
            text = f"기록 {len(rows)}개 · 이메일 {len(counts)}개"
            if email_filter or query:
                text += f" · 보이는 {len(visible)}개"
            count.configure(text=text)
        self._autosize_record_view_columns(visible)
        self._record_view_autosized = True
        focus = ""
        try:
            if keep:
                focus = keep[0]
            elif selected:
                focus = selected[0] if selected[0] in wanted_set else ""
            elif wanted:
                focus = wanted[0]
        except Exception:
            focus = wanted[0] if wanted else ""
        self._show_record_view_detail(focus)

    def _autosize_record_view_columns(self, rows: list[dict]) -> None:
        if getattr(self, "_record_view_autosized", False):
            return
        tree = getattr(self, "_record_view_tree", None)
        if not self._widget_alive(tree):
            return
        try:
            body = tkfont.Font(font=FONTS["body"])
            head = tkfont.Font(font=FONTS["small_bold"])
        except Exception:
            return
        for index, (key, title, min_w) in enumerate(RECORD_VIEW_COLS):
            width = head.measure(title) + 36
            for row in rows:
                values = row.get("values") or ()
                text = str(values[index] if index < len(values) else "")
                width = max(width, body.measure(text) + 24)
            width = max(min_w, width)
            try:
                tree.column(key, width=width, minwidth=64, stretch=False, anchor="w")
            except Exception:
                pass

    def _show_record_view_detail(self, blog_id: str = "") -> None:
        box = getattr(self, "_record_view_detail", None)
        if not self._widget_alive(box):
            return
        text = "줄을 누르면 그 블로그의 날짜별 실행 로그가 여기에 보입니다."
        blog_id = str(blog_id or "").strip()
        if blog_id and not blog_id.startswith("__"):
            text = self._blog_execution_log(blog_id)
        try:
            box.configure(state="normal")
            box.delete("1.0", tk.END)
            box.insert("1.0", text)
            box.configure(state="disabled")
        except Exception:
            pass
        if getattr(self, "_work_shown_editor", None):
            return
        tree = getattr(self, "_record_view_tree", None)
        if self._widget_alive(tree):
            try:
                tree.focus_set()
            except Exception:
                pass

    def _event_when(self, raw) -> datetime | None:
        text = str(raw or "").strip()
        if not text:
            return None
        try:
            return datetime.fromisoformat(text.replace("Z", ""))
        except ValueError:
            pass
        for fmt in ("%Y-%m-%d", "%Y/%m/%d"):
            try:
                return datetime.strptime(text[:10], fmt)
            except ValueError:
                continue
        return None

    def _append_work_event(self, blog_id: str, text: str, *, source: str = "프로그램", note: str = "") -> None:
        blog_id = str(blog_id or "").strip()
        label = str(text or "").strip()
        if not blog_id or not label:
            return
        cur = self._blog_meta.get(blog_id) or {}
        self._home_events().append(
            hr.make_event(
                cur,
                blog_id=blog_id,
                domain=self._record_domain(blog_id),
                old=hr.normalize_status(cur.get("confirmed_status") or cur.get("sheet_status")),
                event=label,
                when=datetime.now(),
                source=source,
                note=note,
            )
        )
        self._schedule_home_save()
        self._schedule_record_view_refresh()

    def _blog_execution_log(self, blog_id: str) -> str:
        blog_id = str(blog_id or "").strip()
        items: list[tuple[datetime, str]] = []
        seen: set[tuple[str, str]] = set()

        def add(raw, text) -> None:
            dt = self._event_when(raw)
            label = " ".join(str(text or "").split())
            if dt is None or not label:
                return
            key = (dt.strftime("%Y-%m-%d %H:%M"), label.split(" · ")[0])
            if key in seen:
                return
            seen.add(key)
            items.append((dt, label))

        for event in self._home_events():
            if str(event.get("blog_id") or "") != blog_id:
                continue
            add(event.get("ts"), event.get("event"))
        meta = self._blog_meta.get(blog_id) or {}
        add(meta.get("created_date"), "생성")
        add(meta.get("settings_applied_at"), "설정 적용")
        add(meta.get("blog_collect_at"), "최초 수집")
        first = str(meta.get("blog_collect_at") or "")
        last_blog = str(meta.get("last_blog_crawl") or "")
        if last_blog and last_blog[:16] != first[:16]:
            count = self._count_value(meta.get("blog_crawl_count"))
            add(last_blog, f"재수집 · {count}회" if count else "재수집")
        add(meta.get("last_post_crawl"), "글 수집")
        checked = meta.get("naver_index_checked_at")
        if checked:
            indexed = meta.get("naver_indexed")
            extra = "색인됨" if indexed is True else ("미색인" if indexed is False else "확인")
            add(checked, f"색인 확인 · {extra}")
        add(meta.get("first_core") or meta.get("last_core"), "노출")
        if not items:
            return "이 블로그의 실행 로그가 아직 없습니다."
        items.sort(key=lambda item: item[0], reverse=True)
        groups: dict[str, list[str]] = {}
        order: list[str] = []
        now_year = datetime.now().year
        for dt, label in items:
            day = f"{dt.year}.{dt.month}/{dt.day}" if dt.year != now_year else f"{dt.month}/{dt.day}"
            if day not in groups:
                groups[day] = []
                order.append(day)
            groups[day].append(f"  {dt.strftime('%H:%M')}  {label}")
        lines: list[str] = []
        for day in order:
            lines.append(day)
            lines.extend(groups[day])
            lines.append("")
        return "\n".join(lines).strip()

    def _rebuild_record_view_tabs(self, counts: dict[str, int]) -> None:
        host = getattr(self, "_record_view_tab_host", None)
        if not self._widget_alive(host):
            return
        total = sum(counts.values())
        saved = [str(item).strip() for item in ((self.__dict__.get("_home_state") or {}).get("email_order") or []) if str(item).strip()]
        seen = {item.lower() for item in saved}
        ordered: list[tuple[str, int]] = []
        for email in saved:
            match = next((key for key in counts if key != RECORD_NO_EMAIL and key.lower() == email.lower()), "")
            if match:
                ordered.append((match, counts[match]))
        for email, count in counts.items():
            if email == RECORD_NO_EMAIL or email.lower() in seen:
                continue
            ordered.append((email, count))
            seen.add(email.lower())
        if RECORD_NO_EMAIL in counts:
            ordered.append((RECORD_NO_EMAIL, counts[RECORD_NO_EMAIL]))
        items = [("", f"전체  {total}")] + [(email, f"{email}  {count}") for email, count in ordered]
        sig = tuple(items)
        btns = getattr(self, "_record_view_tab_btns", None) or {}
        if sig == getattr(self, "_record_view_tab_sig", None) and btns and all(self._widget_alive(b) for b in btns.values()):
            self._paint_record_view_tabs()
            return
        self._record_view_tab_sig = sig
        for child in list(host.winfo_children()):
            try:
                child.destroy()
            except Exception:
                pass
        btns = {}
        x = row = col = 0
        width = max(host.winfo_width(), 980)
        for key, text in items:
            btn = tk.Label(host, text=text, font=FONTS["small_bold"], padx=12, pady=5, cursor="hand2")
            btn._keep_bg = True
            btn.bind("<Button-1>", lambda _e, k=key: self._set_record_view_email(k))
            need = btn.winfo_reqwidth() + 6 if btn.winfo_reqwidth() > 1 else len(text) * 8 + 30
            if col and x + need > width:
                row += 1
                col = 0
                x = 0
            btn.grid(row=row, column=col, padx=(0, 6), pady=(0, 4), sticky="w")
            x += need
            col += 1
            btns[key] = btn
        self._record_view_tab_btns = btns
        if str(getattr(self, "_record_view_email", "") or "") not in btns:
            self._record_view_email = ""
        self._paint_record_view_tabs()

    def _paint_record_view_tabs(self) -> None:
        current = str(getattr(self, "_record_view_email", "") or "")
        for key, btn in (getattr(self, "_record_view_tab_btns", None) or {}).items():
            if not self._widget_alive(btn):
                continue
            if key == current:
                bg, fg = COLORS["accent"], "#ffffff"
            elif key == "":
                bg, fg = COLORS["chip_bg"], COLORS["text"]
            else:
                tag = self._record_email_tag(key)
                try:
                    bg = RECORD_EMAIL_PALETTE[int(tag.replace("email", "")) % len(RECORD_EMAIL_PALETTE)]
                except Exception:
                    bg = COLORS["chip_bg"]
                fg = COLORS["text"]
            try:
                btn.configure(bg=bg, fg=fg)
            except Exception:
                pass

    def _set_record_view_email(self, key: str) -> None:
        if str(getattr(self, "_record_view_email", "") or "") == key:
            return
        self._record_view_email = key
        self._paint_record_view_tabs()
        self._fill_record_view()

    def _sheet_url_or_warn(self) -> str:
        url = self.sheet_url_var.get().strip() if hasattr(self, "sheet_url_var") else ""
        try:
            spreadsheet_id(url)
        except ValueError as exc:
            messagebox.showwarning("기록 시트", str(exc))
            return ""
        return url

    def on_sheet_save_url(self) -> None:
        if not self._sheet_url_or_warn():
            return
        self._save_local_settings()
        self.log("기록 시트 주소를 저장했습니다.")

    def on_sheet_apply_memo_email(self) -> None:
        email = ""
        if hasattr(self, "memo_var"):
            email = str(self._parse_memo(self.memo_var.get())[0] or "").strip()
        if not email:
            messagebox.showwarning("기록 시트", "상단 메모에 이메일을 먼저 적어 주세요.")
            return
        blogs = self._checked_blogs()
        if not blogs:
            messagebox.showwarning("기록 시트", "이메일을 넣을 블로그를 선택해 주세요.")
            return
        for blog in blogs:
            cur = self._blog_meta.setdefault(blog.id, {})
            cur["google_email"] = email
        self._schedule_meta_save()
        self._record_fp = None
        for blog in blogs:
            self._refresh_record_tree_item(blog.id)
        self._schedule_sheet_sync([blog.id for blog in blogs], "구글 이메일")
        self.log(f"선택한 {len(blogs)}개 블로그에 메모 이메일을 넣었습니다.")

    def on_sheet_create(self) -> None:
        self.sheet_url_var.set(DEFAULT_SHEET_URL)
        self._save_local_settings()
        self.log("기록은 지정한 스프레드시트의 블로그스팟 기록 탭에 올립니다.")

    def on_sheet_open(self) -> None:
        url = self._sheet_url_or_warn()
        if not url:
            return
        webbrowser.open(sheet_tab_url(url))
        self.log("기록 시트의 블로그스팟 기록 탭을 브라우저에서 열었습니다.")

    def on_sheet_push(self) -> None:
        url = self._sheet_url_or_warn()
        if not url or self._sheet_busy:
            return
        self._close_record_edit(True)
        records = [program_row(item) for item in self._sheet_record_dicts(blogs=self._record_blogs())]
        if not records:
            messagebox.showwarning("기록 시트", "올릴 블로그가 없습니다. 로그인 후 블로그 목록이 보이면 다시 눌러 주세요.")
            return
        self._sheet_busy = True
        self.log(f"기록 {len(records)}개를 시트에 올립니다.")
        threading.Thread(target=self._sheet_push_worker, args=(url, records), daemon=True).start()

    def _sheet_push_worker(self, url: str, records: list[list[str]]) -> None:
        try:
            pushed, extra = push_rows(url, records)
            self.log(f"기록 시트에 {pushed}개 블로그를 올렸습니다. 시트에만 있는 줄 {extra}개도 유지했습니다.")
            self.root.after(
                0,
                lambda n=pushed: messagebox.showinfo("기록 시트", f"블로그 {n}개를 블로그스팟 기록 탭에 정리했습니다."),
            )
        except Exception as exc:
            detail = str(exc)
            self.log(f"시트 올리기 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("기록 시트", m))
        finally:
            self._sheet_busy = False
            self.root.after(0, self._sheet_sync_continue)

    def _schedule_sheet_sync(self, blog_ids, reason: str = "", *, new_ids=None, drop: bool = False) -> None:
        return

    def _queue_sheet_sync(self, blog_ids, reason: str, *, new_ids=None, drop: bool = False) -> None:
        return

    def _flush_sheet_sync(self) -> None:
        return
        ids = set(self._sheet_sync_ids)
        fresh = set(self._sheet_sync_new)
        drop_ids = set(self._sheet_sync_drop)
        reason = self._sheet_sync_reason or "기록"
        self._sheet_sync_ids.clear()
        self._sheet_sync_new.clear()
        self._sheet_sync_drop.clear()
        self._sheet_sync_reason = ""
        if not ids and not drop_ids:
            return
        url = self.sheet_url_var.get().strip() if hasattr(self, "sheet_url_var") else ""
        try:
            spreadsheet_id(url)
        except ValueError:
            return
        self._close_record_edit(True)
        records = [program_row(item) for item in self._sheet_record_dicts(ids)]
        self._sheet_busy = True
        threading.Thread(
            target=self._sheet_auto_worker,
            args=(url, records, drop_ids, fresh, reason),
            daemon=True,
        ).start()

    def _sheet_auto_worker(self, url: str, records, drop_ids: set[str], new_ids: set[str], reason: str) -> None:
        try:
            _updated, pasted = push_updated_rows(url, records, drop_ids, new_ids)
            if pasted:
                self.log(f"기록 시트를 자동으로 갱신했습니다. ({reason})")
        except Exception as exc:
            self.log(f"기록 시트 자동 갱신 오류: {_exc_text(exc)}")
        finally:
            self._sheet_busy = False
            try:
                self.root.after(0, self._sheet_sync_continue)
            except Exception:
                pass

    def _sheet_sync_continue(self) -> None:
        if self._sheet_sync_again or self._sheet_sync_ids or self._sheet_sync_drop:
            self._sheet_sync_again = False
            self._flush_sheet_sync()

    def on_sheet_pull(self) -> None:
        url = self._sheet_url_or_warn()
        if not url or self._sheet_busy:
            return
        self._sheet_busy = True
        self.log("시트에서 키워드와 상태를 가져옵니다.")
        threading.Thread(target=self._sheet_pull_worker, args=(url,), daemon=True).start()

    def _sheet_pull_worker(self, url: str) -> None:
        try:
            rows = pull_rows(url)
        except Exception as exc:
            detail = str(exc)
            self.log(f"시트 가져오기 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("기록 시트", m))
            self._sheet_busy = False
            self.root.after(0, self._sheet_sync_continue)
            return
        self.root.after(0, lambda found=rows: self._apply_sheet_rows(found))

    def _apply_sheet_rows(self, rows: list[dict]) -> None:
        try:
            blogs = self._dashboard_blogs()
            by_id = {blog.id: blog for blog in blogs}
            by_address = {str(blog.address or "").strip().rstrip("/").lower(): blog for blog in blogs if blog.address}
            applied = 0
            self._close_record_edit(False)
            for row in rows:
                blog = by_id.get(row.get("id") or "")
                if blog is None:
                    blog = by_address.get(str(row.get("address") or "").strip().rstrip("/").lower())
                if blog is None:
                    continue
                cur = self._blog_meta.setdefault(blog.id, {})
                for key in RECORD_FIELDS:
                    if key not in row:
                        continue
                    cur[key] = str(row.get(key) or "")
                applied += 1
            self._save_blog_meta()
            self._record_fp = None
            self._render_record_rows()
            self.log(f"시트에서 {applied}개 블로그의 키워드·상태를 가져왔습니다.")
            messagebox.showinfo("기록 시트", f"{applied}개 블로그 기록을 가져왔습니다.")
        finally:
            self._sheet_busy = False
            self.root.after(0, self._sheet_sync_continue)

    def _widget_alive(self, widget) -> bool:
        if widget is None:
            return False
        try:
            return bool(widget.winfo_exists())
        except Exception:
            return False

    def _show_main_tab(self, name: str) -> None:
        page = self._main_pages.get(name)
        if not self._widget_alive(page):
            self._main_pages.pop(name, None)
            if name == "글쓰기" and self._widget_alive(getattr(self, "tab_body", None)):
                self._build_write_page()
                page = self._main_pages.get(name)
        if not self._widget_alive(page):
            return
        same = (
            name == getattr(self, "_main_tab", "")
            and getattr(page, "_tab_placed", False)
            and getattr(self, "_tab_raise_ready", False)
        )
        self._main_tab = name
        self._map_only_tab(page)
        self._tab_raise_ready = True
        self._after_once("tab_paint", 1, self._paint_main_tabs)
        if (not same) or self._tab_needs_refresh(name):
            if self._tab_needs_refresh(name):
                self._schedule_tab_refresh(name)

    def _ensure_tabs_stacked(self) -> None:
        body = getattr(self, "tab_body", None)
        if not self._widget_alive(body):
            return
        try:
            body.grid_rowconfigure(0, weight=1)
            body.grid_columnconfigure(0, weight=1)
        except Exception:
            pass
        self._tabs_stacked = True

    def _map_only_tab(self, page) -> None:
        self._ensure_tabs_stacked()
        for item in list(self._main_pages.values()):
            if not self._widget_alive(item) or item is page:
                continue
            try:
                item.grid_forget()
            except Exception:
                try:
                    item.pack_forget()
                except Exception:
                    pass
            item._tab_placed = False
        try:
            page.pack_forget()
        except Exception:
            pass
        try:
            page.grid(row=0, column=0, sticky="nsew")
        except Exception:
            return
        page._tab_placed = True
        try:
            page.tkraise()
        except Exception:
            try:
                page.lift()
            except Exception:
                pass

    def _tab_needs_refresh(self, name: str) -> bool:
        if name == "글쓰기":
            return True
        if name == "블로그":
            return bool(
                getattr(self, "_blog_dirty", False)
                or getattr(self, "_detail_dirty", False)
                or getattr(self, "_stale_blog_rows", None)
            )
        if name == "기록":
            return bool(getattr(self, "_record_dirty", False) or getattr(self, "_record_fp", None) is None)
        if name == "색인 확인":
            return bool(
                getattr(self, "_index_dirty", False)
                or getattr(self, "_index_fp", None) is None
                or getattr(self, "_stale_index_rows", None)
            )
        return False

    def _mark_hidden_tabs_dirty(self) -> None:
        """보이지 않는 탭은 그리지 않고 표시만 해 둔다. 탭을 열 때 한 번만 그린다."""
        tab = getattr(self, "_main_tab", "")
        if tab != "기록":
            self._record_dirty = True
        if tab != "색인 확인":
            self._index_dirty = True
        if tab != "블로그":
            self._blog_dirty = True

    def _place_main_page(self, page) -> None:
        self._map_only_tab(page)

    def _schedule_tab_refresh(self, name: str) -> None:
        self._after_once("tab_refresh", 16, lambda tab=name: self._refresh_visible_tab(tab))

    def _refresh_visible_tab(self, name: str) -> None:
        if getattr(self, "_main_tab", "") != name:
            return
        if name == "글쓰기":
            self._refresh_write_count()
        elif name == "블로그":
            self._flush_stale_rows("blog")
            if getattr(self, "_blog_dirty", False):
                self._refresh_dashboard()
            if getattr(self, "_detail_dirty", False):
                self._render_blog_detail()
        elif name == "기록":
            self._render_record_rows()
            self._apply_record_column_folds()
        elif name == "색인 확인":
            if getattr(self, "_index_dirty", False) or getattr(self, "_index_fp", None) is None:
                self._refresh_index_tab()
            else:
                self._flush_stale_rows("index")

    def _paint_main_tabs(self) -> None:
        current = getattr(self, "_main_tab", "")
        prev = getattr(self, "_painted_tab", None)
        names = list(self._main_tab_buttons) if prev is None else ([current] if prev == current else [prev, current])
        for name in names:
            btn = self._main_tab_buttons.get(name)
            if btn is None or not self._widget_alive(btn):
                continue
            active = name == current
            if ctk:
                btn.configure(
                    fg_color=COLORS["accent"] if active else COLORS["border"],
                    hover_color=COLORS["accent_hover"] if active else "#e2e8f0",
                    text_color="#ffffff" if active else COLORS["text"],
                )
            else:
                btn.configure(
                    bg=COLORS["accent"] if active else COLORS["border"],
                    fg="#ffffff" if active else COLORS["text"],
                )
        self._painted_tab = current

    def log(self, message: str) -> None:
        stamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{stamp}] {message}\n"
        try:
            path = data_path(LOG_FILE)
            if os.path.isfile(path) and os.path.getsize(path) > _LOG_MAX:
                size = os.path.getsize(path)
                with open(path, "rb") as handle:
                    handle.seek(max(0, size - 400000))
                    tail = handle.read()
                with open(path, "wb") as handle:
                    handle.write(tail)
            with open(path, "a", encoding="utf-8") as handle:
                handle.write(line)
        except Exception:
            pass

        def _append():
            box = getattr(self, "log_box", None)
            if not self._widget_alive(box):
                return
            try:
                if ctk:
                    box.configure(state="normal")
                    box.insert("end", line)
                    box.see("end")
                    box.configure(state="disabled")
                else:
                    box.configure(state=tk.NORMAL)
                    box.insert(tk.END, line)
                    box.see(tk.END)
                    box.configure(state=tk.DISABLED)
            except Exception:
                pass

        if threading.current_thread() is threading.main_thread():
            _append()
        else:
            self.root.after(0, _append)

    def _textbox_get(self, widget) -> str:
        if not self._widget_alive(widget):
            return ""
        try:
            return widget.get("1.0", "end-1c")
        except Exception:
            return ""

    def _textbox_set(self, widget, text: str) -> None:
        if not self._widget_alive(widget):
            return
        try:
            if ctk:
                widget.delete("1.0", "end")
                widget.insert("1.0", text)
            else:
                widget.delete("1.0", tk.END)
                widget.insert("1.0", text)
        except Exception:
            pass

    def _text_cache_get(self, key: str) -> str:
        cache = getattr(self, "_text_cache", None)
        if not isinstance(cache, dict):
            return ""
        return str(cache.get(key) or "")

    def _text_cache_set(self, key: str, value: str) -> None:
        cache = getattr(self, "_text_cache", None)
        if not isinstance(cache, dict):
            cache = {}
            self._text_cache = cache
        cache[key] = value or ""

    def _settings_text(self, file_key: str) -> str:
        path = data_path(SETTINGS_FILE)
        if not os.path.isfile(path):
            return ""
        try:
            with open(path, "r", encoding="utf-8") as handle:
                data = json.load(handle)
        except Exception:
            return ""
        return str((data or {}).get(file_key) or "")

    def _current_text(self, key: str, widget) -> str:
        cached = self._text_cache_get(key)
        if not self._widget_alive(widget):
            return cached or self._settings_text("google_descriptions" if key == "desc" else "create_titles")
        live = self._textbox_get(widget)
        try:
            visible = bool(widget.winfo_viewable())
        except Exception:
            visible = True
        if live.strip() or visible:
            if not (getattr(self, "_reloading", False) and not live.strip() and cached.strip()):
                self._text_cache_set(key, live)
                return live
        kept = cached or live
        if not kept.strip():
            kept = self._settings_text("google_descriptions" if key == "desc" else "create_titles")
            if kept.strip():
                self._text_cache_set(key, kept)
        return kept

    def _bind_text_cache(self, widget, key: str) -> None:
        target = getattr(widget, "_textbox", widget)

        def on_modified(_event=None, box=target, name=key, owner=widget):
            try:
                if box.edit_modified():
                    box.edit_modified(False)
            except Exception:
                pass
            text = self._textbox_get(owner)
            cached = self._text_cache_get(name)
            if getattr(self, "_reloading", False) and not text.strip() and cached.strip():
                return
            self._text_cache_set(name, text)
            if not getattr(self, "_reloading", False):
                self._schedule_text_save()

        try:
            target.bind("<<Modified>>", on_modified, add="+")
        except Exception:
            pass

    def _schedule_text_save(self) -> None:
        self._after_once("text_save", 700, self._save_local_settings)

    def _load_local_settings(self) -> None:
        self._load_progress()
        self._load_blog_meta()
        self._load_home_state()
        path = data_path(SETTINGS_FILE)
        if not os.path.isfile(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                data = json.load(handle)
        except Exception:
            return
        self._textbox_set(self.desc_text, str(data.get("google_descriptions") or ""))
        self._text_cache_set("desc", self._textbox_get(self.desc_text))
        if hasattr(self, "create_titles"):
            self._textbox_set(self.create_titles, str(data.get("create_titles") or ""))
            self._text_cache_set("create", self._textbox_get(self.create_titles))
        self.favicon_var.set(str(data.get("favicon_folder") or ""))
        saved_blog_folder = str(data.get("blog_folder") or "").strip()
        if hasattr(self, "blog_folder_var") and saved_blog_folder:
            self.blog_folder_var.set(saved_blog_folder)
        self.manuscript_var.set(str(data.get("manuscript_folder") or ""))
        self.post_image_var.set(str(data.get("post_image_folder") or ""))
        if hasattr(self, "write_count_var"):
            saved_count = str(data.get("write_count") or "").strip()
            self.write_count_var.set(saved_count if saved_count.isdigit() and int(saved_count) >= 1 else "1")
        if hasattr(self, "theme_html"):
            self._apply_html_codes(
                data.get("html_codes"),
                data.get("html_code_index"),
                fallback_html=str(data.get("theme_html") or ""),
            )
        if hasattr(self, "memo_var"):
            self.memo_var.set(str(data.get("account_memo") or ""))
        if hasattr(self, "sheet_url_var"):
            self.sheet_url_var.set(str(data.get("sheet_url") or "").strip() or DEFAULT_SHEET_URL)

    def _load_progress(self) -> None:
        path = data_path(PROGRESS_FILE)
        if not os.path.isfile(path):
            self._progress_map = {}
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                raw = json.load(handle)
            self._progress_map = {
                str(blog_id): [str(item) for item in items]
                for blog_id, items in (raw or {}).items()
            }
        except Exception:
            self._progress_map = {}

    def _save_progress(self) -> None:
        path = data_path(PROGRESS_FILE)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self._progress_map, handle, ensure_ascii=False, indent=2)

    def _load_blog_meta(self) -> None:
        path = data_path(BLOG_META_FILE)
        if not os.path.isfile(path):
            self._blog_meta = {}
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                raw = json.load(handle)
            self._blog_meta = {}
            for blog_id, item in (raw or {}).items():
                if not isinstance(item, dict):
                    continue
                posts = normalize_posts(item.get("posts") or [])
                if not posts:
                    posts = normalize_posts(
                        [
                            {
                                "url": item.get("post_url"),
                                "title": item.get("post_title"),
                            }
                        ]
                    )
                self._blog_meta[str(blog_id)] = {
                    "name": str(item.get("name") or ""),
                    "address": str(item.get("address") or ""),
                    "posts": posts,
                    "naver_id": str(item.get("naver_id") or ""),
                    "last_blog_crawl": str(item.get("last_blog_crawl") or ""),
                    "blog_collect_at": str(item.get("blog_collect_at") or ""),
                    "blog_crawl_count": self._count_value(item.get("blog_crawl_count")),
                    "last_post_crawl": str(item.get("last_post_crawl") or ""),
                    "last_activity": str(item.get("last_activity") or ""),
                    "folder": str(item.get("folder") or ""),
                    "html_code": str(item.get("html_code") or ""),
                    "post_crawls": item.get("post_crawls") if isinstance(item.get("post_crawls"), dict) else {},
                    "naver_indexed": item.get("naver_indexed") if isinstance(item.get("naver_indexed"), bool) else None,
                    "naver_index_checked_at": str(item.get("naver_index_checked_at") or ""),
                    "naver_index_message": str(item.get("naver_index_message") or ""),
                    "naver_index_sample": str(item.get("naver_index_sample") or ""),
                    "naver_index_count": self._count_value(item.get("naver_index_count")),
                    "naver_index_query": str(item.get("naver_index_query") or ""),
                    "settings_applied_at": str(item.get("settings_applied_at") or ""),
                    "activity_log": _parse_activity_log(item.get("activity_log")),
                    **{key: str(item.get(key) or "") for key in RECORD_FIELDS},
                    **hr.load_fields(item),
                }
                self._migrate_home_meta(self._blog_meta[str(blog_id)])
            self._fill_missing_post_crawls()
        except Exception:
            self._blog_meta = {}

    def _save_blog_meta(self) -> None:
        path = data_path(BLOG_META_FILE)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self._blog_meta, handle, ensure_ascii=False, indent=2)

    def _remember_blog_meta(self, blogs: list[BlogInfo]) -> None:
        changed = False
        gone = self._gone_id_set()
        for blog in blogs:
            if blog.id in gone:
                continue
            cur = self._blog_meta.setdefault(blog.id, {})
            if blog.name and cur.get("name") != blog.name:
                cur["name"] = blog.name
                changed = True
            if blog.address:
                old_address = str(cur.get("address") or "").strip()
                if old_address and not self._same_blog_address(old_address, blog.address):
                    if self._reset_setup_after_address_change(blog, old_address, blog.address):
                        changed = True
                    if self._recreate_blog_folder_for_address(
                        blog.id, old_address, blog.address, blog.name or ""
                    ):
                        changed = True
                    self._append_blog_log(blog.id, "블로그주소 변경 확인")
                if cur.get("address") != blog.address:
                    cur["address"] = blog.address
                    changed = True
            live = bool(getattr(blog, "posts_live", False))
            posts = posts_for_address(blog.posts, blog.address or cur.get("address") or "")
            if live:
                if cur.get("posts") != posts:
                    cur["posts"] = posts
                    changed = True
            elif posts:
                merged = posts_for_address(normalize_posts([*(cur.get("posts") or []), *posts]), blog.address or cur.get("address") or "")
                if cur.get("posts") != merged:
                    cur["posts"] = merged
                    changed = True
            else:
                cleaned = posts_for_address(cur.get("posts") or [], blog.address or cur.get("address") or "")
                if cur.get("posts") != cleaned:
                    cur["posts"] = cleaned
                    changed = True
            if cur.pop("post_url", None) is not None or cur.pop("post_title", None) is not None:
                changed = True
        if self._sync_blog_folders(blogs):
            changed = True
        if not changed:
            return
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _merge_blog_meta(self, blogs: list[BlogInfo]) -> None:
        for blog in blogs:
            meta = self._blog_meta.get(blog.id) or {}
            if not blog.address:
                blog.address = str(meta.get("address") or "")
            saved = posts_for_address(meta.get("posts") or [], blog.address or meta.get("address") or "")
            if not saved:
                saved = posts_for_address(
                    [{"url": meta.get("post_url"), "title": meta.get("post_title")}],
                    blog.address or meta.get("address") or "",
                )
            if getattr(blog, "posts_live", False):
                blog.posts = posts_for_address(blog.posts, blog.address)
                continue
            if saved and not blog.posts:
                blog.posts = saved
            elif saved and blog.posts:
                blog.posts = posts_for_address(normalize_posts([*blog.posts, *saved]), blog.address)
            else:
                blog.posts = posts_for_address(blog.posts, blog.address)

    def _save_local_settings(self) -> None:
        path = data_path(SETTINGS_FILE)
        data = {
            "google_descriptions": self._current_text("desc", getattr(self, "desc_text", None)),
            "create_titles": self._current_text("create", getattr(self, "create_titles", None)),
            "favicon_folder": self.favicon_var.get().strip(),
            "blog_folder": self.blog_folder_var.get().strip() if hasattr(self, "blog_folder_var") else "",
            "manuscript_folder": self.manuscript_var.get().strip(),
            "post_image_folder": self.post_image_var.get().strip(),
            "write_count": self.write_count_var.get().strip() if hasattr(self, "write_count_var") else "1",
            "html_codes": self._export_html_codes(),
            "html_code_index": int(getattr(self, "_html_code_index", 0) or 0),
            "theme_html": self._selected_html_template(),
            "account_memo": self.memo_var.get() if hasattr(self, "memo_var") else "",
            "sheet_url": self.sheet_url_var.get().strip() if hasattr(self, "sheet_url_var") else "",
        }
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(data, handle, ensure_ascii=False, indent=2)

    def _description_lines(self) -> list[str]:
        raw = self._current_text("desc", getattr(self, "desc_text", None))
        return [line.strip() for line in raw.splitlines() if line.strip()]

    def _pick_random_image(self, folder: str) -> str:
        files = []
        for name in os.listdir(folder):
            if os.path.splitext(name)[1].lower() in IMAGE_EXTS:
                files.append(os.path.join(folder, name))
        if not files:
            raise RuntimeError("선택한 폴더에 이미지 파일이 없습니다.")
        return random.choice(files)

    def on_pick_folder(self):
        folder = filedialog.askdirectory(title="파비콘 폴더 선택")
        if folder:
            self.favicon_var.set(folder)
            self._save_local_settings()

    def on_pick_blog_folder(self):
        folder = filedialog.askdirectory(title="블로그 폴더 선택")
        if folder:
            self.blog_folder_var.set(folder)
            self._save_local_settings()

    def _blog_folder_name(self, address: str) -> str:
        host = re.sub(r"^https?://", "", (address or "").strip(), flags=re.I).strip().strip("/")
        host = host.split("/")[0].split("?")[0].strip()
        if host.lower().startswith("www."):
            host = host[4:]
        host = re.sub(r'[<>:"/\\|?*]', "_", host).rstrip(". ")
        return host

    def _blog_folders_root(self) -> str:
        folder = self.blog_folder_var.get().strip() if hasattr(self, "blog_folder_var") else ""
        if not folder:
            folder = os.path.join(get_app_dir(), "블로그")
            if hasattr(self, "blog_folder_var"):
                self.blog_folder_var.set(folder)
        os.makedirs(folder, exist_ok=True)
        return folder

    def _make_blog_address_folder(self, address: str, root: str) -> str:
        name = self._blog_folder_name(address)
        if not name:
            return ""
        path = os.path.join(root, name)
        os.makedirs(path, exist_ok=True)
        return path

    def _remember_blog_folder(self, blog_id: str, address: str, folder: str, title: str = "") -> None:
        if blog_id:
            cur = self._blog_meta.setdefault(blog_id, {})
            cur["folder"] = folder
            if address:
                cur["address"] = address
            if title and not str(cur.get("name") or "").strip():
                cur["name"] = title
            try:
                self._save_blog_meta()
            except Exception:
                pass
        else:
            loose = getattr(self, "_loose_folders", None)
            if not isinstance(loose, list):
                loose = []
                self._loose_folders = loose
            loose.append({"name": title or address or folder, "folder": folder})
        self._dashboard_fp = None
        self._schedule_dashboard()

    def _folder_basename(self, path: str) -> str:
        return os.path.basename((path or "").rstrip("\\/")).casefold()

    def _ensure_blog_folder(self, blog_id: str, address: str, title: str = "") -> str:
        wanted = self._blog_folder_name(address)
        if not blog_id or not wanted:
            return ""
        cur = self._blog_meta.setdefault(blog_id, {})
        current = str(cur.get("folder") or "").strip()
        if current and self._folder_basename(current) == wanted.casefold() and os.path.isdir(current):
            return current
        path = self._make_blog_address_folder(address, self._blog_folders_root())
        if not path:
            return current
        if current == path and os.path.isdir(path):
            return path
        cur["folder"] = path
        if address:
            cur["address"] = address
        if title and not str(cur.get("name") or "").strip():
            cur["name"] = title
        return path

    def _recreate_blog_folder_for_address(
        self, blog_id: str, old_address: str, new_address: str, title: str = ""
    ) -> bool:
        wanted = self._blog_folder_name(new_address)
        if not blog_id or not wanted:
            return False
        path = self._make_blog_address_folder(new_address, self._blog_folders_root())
        if not path:
            return False
        cur = self._blog_meta.setdefault(blog_id, {})
        before = str(cur.get("folder") or "").strip()
        cur["folder"] = path
        if title and not str(cur.get("name") or "").strip():
            cur["name"] = title
        self._dashboard_fp = None
        self._blog_dirty = True
        (getattr(self, "_blog_row_sigs", None) or {}).pop(blog_id, None)
        old_name = self._blog_folder_name(old_address) or self._folder_basename(before) or old_address
        if before and self._folder_basename(before) == wanted.casefold() and os.path.isdir(path):
            return False
        self.log(f"주소가 바뀌어 폴더를 다시 만들었습니다: {old_name} → {path}")
        return True

    def _sync_blog_folders(self, blogs: list[BlogInfo] | None = None) -> bool:
        changed = False
        created = 0
        renamed = 0
        for blog in blogs or []:
            address = str(getattr(blog, "address", "") or "").strip()
            if not address:
                continue
            before = str((self._blog_meta.get(blog.id) or {}).get("folder") or "").strip()
            before_name = self._folder_basename(before) if before else ""
            wanted = self._blog_folder_name(address).casefold()
            path = self._ensure_blog_folder(blog.id, address, getattr(blog, "name", "") or "")
            after = str((self._blog_meta.get(blog.id) or {}).get("folder") or "").strip()
            if not after or after == before:
                continue
            changed = True
            if before_name and before_name != wanted:
                renamed += 1
            else:
                created += 1
            if path and before and before_name != wanted:
                self.log(f"바뀐 주소로 폴더를 만들었습니다: {path}")
        if created:
            self.log(f"블로그 폴더 {created}개를 만들었습니다.")
        return changed

    def _blog_folder_of(self, blog_id: str) -> str:
        meta = (self._blog_meta or {}).get(blog_id) or {}
        return str(meta.get("folder") or "").strip()

    def _copy_blog_folder(self, blog_id: str) -> None:
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        address = str((blog.address if blog else "") or (self._blog_meta.get(blog_id) or {}).get("address") or "").strip()
        if address:
            self._ensure_blog_folder(blog_id, address, getattr(blog, "name", "") if blog else "")
            try:
                self._save_blog_meta()
            except Exception:
                pass
        path = self._blog_folder_of(blog_id)
        if not path:
            self.log("이 블로그 주소로 폴더를 만들지 못했습니다.")
            return
        self._copy_folder_path(path)

    def _copy_folder_path(self, path: str) -> None:
        text = (path or "").strip()
        if not text:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self.root.update_idletasks()
        except Exception as exc:
            self.log(f"폴더 주소를 복사하지 못했습니다: {exc}")
            return
        self.log(f"폴더 주소를 복사했습니다: {text}")

    def _schedule_memo_refresh(self) -> None:
        self._after_once("memo", 180, self._apply_memo_parts)

    def _apply_memo_parts(self) -> None:
        parts = self._parse_memo(self.memo_var.get() if hasattr(self, "memo_var") else "")
        self._memo_parts = parts
        titles = ("이메일", "아이디", "비번", "이름")
        for btn, title, value in zip(getattr(self, "_memo_copy_btns", []), titles, parts):
            shown = title if not value else f"{title} {value}"
            if len(shown) > 16:
                shown = shown[:15] + "…"
            try:
                btn.configure(text=shown)
            except Exception:
                pass
        self._schedule_text_save()

    def _memo_naver_id(self) -> str:
        parts = getattr(self, "_memo_parts", None) or ["", "", "", ""]
        if not any(str(part or "").strip() for part in parts) and hasattr(self, "memo_var"):
            parts = self._parse_memo(self.memo_var.get())
            self._memo_parts = parts
        return str(parts[1] if len(parts) > 1 else "").strip()

    def _index_caption(self) -> str:
        naver_id = self._memo_naver_id()
        if not naver_id:
            return ""
        return f"색인 {naver_id}"

    def _blog_heading_text(self, count: int) -> str:
        account = self._naver_logged_account()
        if count and account:
            return f"블로그 {count} · 생성순 · 서치 {account}"
        if count:
            return f"블로그 {count} · 생성순"
        if account:
            return f"블로그 · 서치 {account}"
        return "블로그"

    def _sync_index_labels(self) -> None:
        for widget in list(getattr(self, "_index_labels", []) or []):
            try:
                if not widget.winfo_exists():
                    continue
            except Exception:
                continue
            indexed = str(getattr(widget, "_fallback_index", "") or "").strip()
            caption = f"색인 {indexed}" if indexed else ""
            color = COLORS["success"] if indexed else COLORS["text_muted"]
            try:
                widget.configure(text=caption, fg=color)
            except Exception:
                try:
                    widget.configure(text=caption, text_color=color)
                except Exception:
                    try:
                        widget.configure(text=caption)
                    except Exception:
                        pass
            try:
                if caption:
                    widget.pack(side=tk.LEFT, padx=(8, 0))
                else:
                    widget.pack_forget()
            except Exception:
                pass
        heading = getattr(self, "blog_heading", None)
        listed = list(getattr(self, "_listed_blogs", None) or [])
        if heading is not None:
            try:
                heading.configure(text=self._blog_heading_text(len(listed)))
            except Exception:
                pass
        if not listed:
            return
        for blog in listed:
            blog._search_text = self._blog_search_text(blog)
        self._vis_key = None
        self._apply_blog_visibility()

    def _parse_memo(self, text: str) -> list[str]:
        line = ""
        for raw in (text or "").replace("\r", "\n").splitlines():
            if raw.strip():
                line = raw.strip()
                break
        if not line:
            return ["", "", "", ""]
        if "\t" in line:
            parts = [part.strip() for part in line.split("\t")]
        else:
            parts = [part for part in re.split(r"\s+", line) if part]
        while len(parts) < 4:
            parts.append("")
        return parts[:4]

    def _copy_memo_index(self, index: int) -> None:
        titles = ("이메일", "네이버아이디", "비밀번호", "이름")
        parts = self._parse_memo(self.memo_var.get() if hasattr(self, "memo_var") else "")
        self._memo_parts = parts
        if index < 0 or index >= len(titles):
            return
        self._copy_memo_part(titles[index], parts[index] if index < len(parts) else "")

    def _copy_memo_part(self, title: str, value: str) -> None:
        text = (value or "").strip()
        if not text:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self.root.update_idletasks()
        except Exception:
            self.log(f"{title} 항목을 복사하지 못했습니다.")
            return
        self.log(f"{title} 항목을 복사했습니다.")

    def _is_typing_widget(self, widget) -> bool:
        cur = widget
        for _ in range(10):
            if cur is None:
                return False
            name = type(cur).__name__
            cls = ""
            try:
                cls = str(cur.winfo_class() or "")
            except Exception:
                cls = ""
            if "Entry" in name or cls in ("Entry", "Text", "TEntry", "TCombobox"):
                return True
            if name in ("Text", "CTkEntry", "CTkComboBox") or (name == "CTkTextbox" and self._widget_allows_copy(cur)):
                return True
            try:
                cur = cur.master
            except Exception:
                return False
        return False

    def _widget_allows_copy(self, widget) -> bool:
        try:
            if str(widget.cget("state") or "") in ("disabled", "readonly"):
                return False
        except Exception:
            pass
        return True

    def _bind_copy_shortcuts(self) -> None:
        def on_copy(event, app=self):
            return app._on_copy_blog_url(event)

        for seq in ("<Control-c>", "<Control-C>", "<Control-Key-c>", "<Control-Key-C>"):
            try:
                self.root.unbind_all(seq)
            except Exception:
                pass
            self.root.bind_all(seq, on_copy)

    def _on_copy_blog_url(self, event=None):
        widget = event.widget if event else None
        focus = None
        try:
            focus = self.root.focus_get()
        except Exception:
            focus = widget
        if self._is_typing_widget(widget) or self._is_typing_widget(focus):
            return
        blog_id = str(self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""
        blogs = []
        if blog_id:
            found = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
            if found is not None:
                blogs = [found]
        if not blogs:
            try:
                blogs = list(self._checked_blogs())
            except Exception:
                blogs = []
        urls = []
        for blog in blogs:
            addr = str(getattr(blog, "address", "") or "").strip()
            if not addr:
                addr = str((self._blog_meta.get(getattr(blog, "id", "")) or {}).get("address") or "").strip()
            if addr and addr not in urls:
                urls.append(addr)
        if not urls:
            if blog_id or blogs:
                self.log("선택한 블로그에 주소가 없어 복사하지 못했습니다.")
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(urls))
            self.root.update_idletasks()
        except Exception:
            self.log("블로그 주소를 복사하지 못했습니다.")
            return
        if len(urls) == 1:
            self.log("블로그 주소를 복사했습니다.")
        else:
            self.log(f"블로그 주소 {len(urls)}개를 복사했습니다.")
        return "break"

    def _naver_logged_account(self) -> str:
        state = getattr(self.naver, "state", None)
        if state is None or not getattr(state, "logged_in", False):
            return ""
        return str(getattr(state, "account", "") or "").strip()

    def on_pick_manuscript_folder(self):
        folder = filedialog.askdirectory(title="원고 폴더 선택")
        if folder:
            self.manuscript_var.set(folder)
            self._save_local_settings()
            self._refresh_write_count()

    def on_pick_post_image_folder(self):
        folder = filedialog.askdirectory(title="이미지 폴더 선택")
        if folder:
            self.post_image_var.set(folder)
            self._save_local_settings()

    def on_login(self):
        if self._login_busy:
            return
        self._login_busy = True
        self._set_login_button("인식 중...", enabled=False)
        self._set_status("블로그스팟 창의 아이디를 읽는 중", COLORS["warning"])
        threading.Thread(target=self._login_worker, daemon=True).start()

    def _login_worker(self):
        try:
            state = self.session.recognize()
            if not self.session.chrome_running():
                self.root.after(0, self._on_browser_closed)
                return
            if not state.logged_in:
                self.root.after(0, self._on_blogger_signed_out)
                return
            self._merge_blog_meta(state.blogs)
            self.root.after(0, lambda: self._on_logged_in(state))
            self._catalog_worker()
        except Exception as exc:
            self.log(f"블로그스팟 인식 오류: {exc}")
            self.root.after(0, lambda: self._login_failed(str(exc)))

    def _redetect_worker(self):
        try:
            self.session.detect()
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.log("블로그 목록을 다시 읽고 주소·글을 인식합니다.")
            self._catalog_worker(refresh_address=True)
        except Exception as exc:
            self.log(f"블로그 다시 인식 오류: {exc}")

    def _catalog_abort(self) -> bool:
        return self._create_busy or self._settings_busy or self._post_busy or self._naver_busy

    def _catalog_worker(self, refresh_address: bool = False):
        self._catalog_running = True
        try:
            self.session.refresh_blog_details(
                should_abort=self._catalog_abort,
                refresh_address=refresh_address,
            )
            self._merge_blog_meta(self.session.state.blogs)
            self.root.after(0, lambda: self._apply_state(self.session.state))
            found = sum(1 for blog in self.session.state.blogs if (blog.address or "").strip())
            posts = sum(len(blog.posts) for blog in self.session.state.blogs)
            self.log(f"로그인 인식 완료. 주소 {found}개 · 글 {posts}개")
        except Exception as exc:
            self.log(f"블로그 상세 인식 오류: {exc}")
        finally:
            self._catalog_running = False

    def _on_logged_in(self, state: SessionState):
        self._login_busy = False
        self._blogger_signed_out_noted = False
        self._set_login_button("다시 인식", enabled=True)
        self._apply_state(state)
        names = ", ".join(blog.name or blog.id for blog in state.blogs) or "(없음)"
        self.log(f"로그인 확인. 계정={state.account or '-'} / 블로그={names}")
        self.log("목록은 바로 쓰고, 주소와 글은 페이지를 바꾸지 않고 이어서 인식합니다.")
        self._start_watch()

    def _login_failed(self, reason: str):
        self._login_busy = False
        self._set_login_button("블로그스팟 로그인", enabled=True)
        self._set_status("로그인 실패", COLORS["danger"])
        messagebox.showerror("로그인", reason)

    def _on_blogger_signed_out(self):
        self._login_busy = False
        self._shown_account = ""
        self._blogger_signed_out_noted = True
        self._set_login_button("다시 인식", enabled=True)
        self._apply_state(self.session.state)

    def _apply_state(self, state: SessionState):
        self._apply_gone_ids()
        gone = getattr(self.session, "_gone_ids", None) or set()
        if gone:
            state.blogs = [blog for blog in state.blogs if blog.id not in gone]
            self.session.state.blogs = state.blogs
        account = (state.account or "").strip()
        self.account_label.configure(text=f"계정: {account or '-'}")
        if state.logged_in and account and self._shown_account and account != self._shown_account:
            self._blog_check_vars.clear()
            self.blog_var.set("")
            self.log(f"다른 계정으로 로그인했습니다. {account} 블로그만 표시합니다.")
        if state.logged_in:
            if account:
                self._shown_account = account
            count = len(state.blogs)
            self._set_status(f"로그인됨 · 이 계정 블로그 {count}개", COLORS["success"])
        else:
            self._shown_account = ""
            self.blog_var.set("")
            self._set_status("로그인 전", COLORS["text"])
        self._merge_progress(state.blogs)
        self._merge_blog_meta(state.blogs)
        self._remember_blog_meta(state.blogs)
        self._remember_program_order(state)
        self._schedule_dashboard()

    def _remember_program_order(self, state: SessionState) -> None:
        """시트 API 'inventory': 로그인 계정의 블로그 목록 순서를 기억해 정렬에 쓴다."""
        if not state.logged_in or not state.blogs:
            return
        email = str(self._logged_google_email() or "").strip().lower()
        if not email:
            return
        home = self.__dict__.setdefault("_home_state", {"email_order": [], "program_order": {}, "program_order_time": {}, "events": []})
        hosts = []
        for blog in state.blogs:
            address = str(blog.address or "").strip()
            if not address:
                continue
            host = hr.match_domain(address)
            if host:
                hosts.append(host)
        if not hosts:
            return
        orders = home.setdefault("program_order", {})
        if orders.get(email) == hosts:
            return
        orders[email] = hosts
        home.setdefault("program_order_time", {})[email] = datetime.now().isoformat(timespec="seconds")
        self._remember_email_order(email)
        self._schedule_home_save()
        self._record_fp = None

    def _any_busy(self) -> bool:
        return any(
            (
                self._login_busy,
                self._naver_login_busy,
                self._post_busy,
                self._settings_busy,
                self._naver_busy,
                self._create_busy,
                getattr(self, "_index_busy", False),
            )
        )

    def _schedule_dashboard(self) -> None:
        self._after_once("dashboard", 80, self._refresh_dashboard)

    def _same_blog_address(self, left: str, right: str) -> bool:
        a = _search_compact(left)
        b = _search_compact(right)
        return bool(a) and a == b

    def _reset_setup_after_address_change(self, blog: BlogInfo, old_address: str, new_address: str) -> bool:
        items = list(self._progress_map.get(blog.id) or [])
        had_progress = any(key in SETUP_KEYS for key in items)
        had_done = bool(blog.done.intersection(SETUP_KEYS))
        cur = self._blog_meta.setdefault(blog.id, {})
        had_applied = bool(str(cur.get("settings_applied_at") or "").strip())
        if not had_progress and not had_done and not had_applied:
            return False
        blog.done.difference_update(SETUP_KEYS)
        self._progress_map[blog.id] = [key for key in items if key not in SETUP_KEYS]
        if had_applied:
            cur["settings_applied_at"] = ""
        try:
            self._save_progress()
        except Exception:
            pass
        self._dashboard_fp = None
        old_host = _search_compact(old_address) or old_address
        new_host = _search_compact(new_address) or new_address
        self.log(f"블로그 주소가 바뀌어 설정을 초기화했습니다: {old_host} → {new_host}")
        return True

    def _merge_progress(self, blogs: list[BlogInfo]) -> None:
        for blog in blogs:
            blog.done.update(self._progress_map.get(blog.id, []))

    def _configure_blog_columns(self, widget) -> None:
        for index, (_title, minsize, weight) in enumerate(self._blog_col_headers):
            widget.grid_columnconfigure(index, minsize=minsize, weight=weight)

    def _on_post_query_changed(self, *_args) -> None:
        self._after_once("post_query", 180, self._render_blog_detail)

    def _on_blog_query_changed(self, *_args) -> None:
        self._after_once("blog_query", 30, self._apply_blog_visibility)

    def _set_blog_filter(self, key: str) -> None:
        if self._blog_filter == key:
            return
        self._blog_filter = key
        self._paint_filter_btns()
        self._apply_blog_visibility()

    def _paint_filter_btns(self) -> None:
        for key, btn in self._blog_filter_btns.items():
            active = key == self._blog_filter
            if ctk:
                btn.configure(
                    fg_color=COLORS["accent"] if active else COLORS["border"],
                    hover_color=COLORS["accent_hover"] if active else "#e2e8f0",
                    text_color="#ffffff" if active else COLORS["text"],
                )
            else:
                btn.configure(
                    bg=COLORS["accent"] if active else COLORS["border"],
                    fg="#ffffff" if active else COLORS["text"],
                )

    def _dashboard_blogs(self) -> list[BlogInfo]:
        if not self.session.state.logged_in:
            return []
        gone = getattr(self.session, "_gone_ids", None) or set()
        blogs: list[BlogInfo] = []
        for blog in self.session.state.blogs:
            if blog.id in gone:
                continue
            meta = self._blog_meta.get(blog.id) or {}
            if hr.normalize_status(meta.get("confirmed_status") or meta.get("sheet_status")) == "삭제됨":
                continue
            if not blog.name:
                blog.name = str(meta.get("name") or blog.address or blog.id[-6:])
            if not (blog.address or "").strip():
                blog.address = str(meta.get("address") or "")
            blog.done.update(self._progress_map.get(blog.id, []))
            addr = blog.address or str(meta.get("address") or "")
            if getattr(blog, "posts_live", False):
                blog.posts = posts_for_address(blog.posts, addr)
            elif not blog.posts:
                blog.posts = posts_for_address(meta.get("posts") or [], addr)
            else:
                blog.posts = posts_for_address(blog.posts, addr)
            blogs.append(blog)
        blogs.sort(key=self._blog_created_sort_key)
        return blogs

    def _blog_created_sort_key(self, blog: BlogInfo) -> tuple:
        blog_id = str(blog.id or "").strip()
        if blog_id.isdigit():
            return (0, int(blog_id))
        return (1, (blog.name or blog.address or blog_id).lower())

    def _blog_times(self, blog_id: str) -> dict:
        meta = self._blog_meta.get(blog_id) or {}
        return {
            "blog": str(meta.get("last_blog_crawl") or ""),
            "post": str(meta.get("last_post_crawl") or ""),
            "activity": str(meta.get("last_activity") or ""),
        }

    def _fmt_when(self, raw: str) -> str:
        value = (raw or "").strip()
        if not value:
            return ""
        try:
            dt = datetime.fromisoformat(value)
        except ValueError:
            return value[5:16].replace("T", " ") if len(value) >= 16 else value
        today = datetime.now().date()
        if dt.date() == today:
            return f"오늘 {dt.strftime('%H:%M')}"
        if dt.date() == today - timedelta(days=1):
            return f"어제 {dt.strftime('%H:%M')}"
        if dt.year == datetime.now().year:
            return dt.strftime("%m-%d %H:%M")
        return dt.strftime("%y-%m-%d")

    def _last_recrawl(self, blog_id: str) -> str:
        times = self._blog_times(blog_id)
        stamps = [item for item in (times["blog"], times["post"]) if item]
        if stamps:
            return max(stamps)
        return times["activity"]

    def _setup_header_hover(self):
        lines = [
            (COLORS["text"], "설정 항목", "body_bold"),
            (COLORS["text_muted"], "마우스를 숫자 위에 올리면 블로그별 완료/미완료가 보입니다.", "caption"),
        ]
        for key, name in SETTING_ITEMS:
            if key in {"collect", "collect_post"}:
                continue
            lines.append((COLORS["text"], f"  · {name}", "body"))
        return lines

    def _setup_status_hover(self, blog: BlogInfo):
        done = [(key, name) for key, name in SETTING_ITEMS if key in SETUP_KEYS and key in blog.done]
        pending = [(key, name) for key, name in SETTING_ITEMS if key in SETUP_KEYS and key not in blog.done]
        title = blog.name or blog.address or blog.id
        if len(title) > 28:
            title = title[:27] + "…"
        lines = [
            (COLORS["text"], title, "body_bold"),
            (COLORS["text_muted"], f"설정 {len(done)}/{len(SETUP_KEYS)}", "small"),
        ]
        if done:
            lines.append((COLORS["success"], f"완료 {len(done)}", "small"))
            for _key, name in done:
                lines.append((COLORS["success"], f"  ✓ {name}", "body"))
        if pending:
            lines.append((COLORS["danger"], f"미완료 {len(pending)}", "small"))
            for _key, name in pending:
                lines.append((COLORS["danger"], f"  · {name}", "body"))
        return lines

    def _filter_blogs(self, blogs: list[BlogInfo]) -> list[BlogInfo]:
        query = (self.blog_query.get() or "").strip()
        return [blog for blog in blogs if self._blog_row_matches(blog, query)]

    def _html_code_of(self, blog_id: str) -> str:
        return str((self._blog_meta.get(blog_id) or {}).get("html_code") or "").strip()

    def _remember_html_code(self, blog_id: str, name: str) -> None:
        name = (name or "").strip()
        if not blog_id or not name:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        if str(cur.get("html_code") or "").strip() == name:
            return
        cur["html_code"] = name
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _naver_id_of(self, blog_id: str) -> str:
        return str((self._blog_meta.get(blog_id) or {}).get("naver_id") or "").strip()

    def _remember_naver_id(self, blog_id: str, account: str = "") -> None:
        registered = (account or self._memo_naver_id()).strip()
        if not blog_id or not registered:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        if str(cur.get("naver_id") or "").strip() == registered:
            return
        cur["naver_id"] = registered
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _dashboard_fingerprint(self, blogs: list[BlogInfo], visible: list[BlogInfo]) -> tuple:
        return (
            self._blog_filter,
            str(self.blog_var.get() or ""),
            str(getattr(self, "_pending_select_id", "") or ""),
            tuple(
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    len(blog.posts or []),
                    tuple(sorted(blog.done)),
                    self._last_recrawl(blog.id),
                    self._naver_id_of(blog.id),
                    self._html_code_of(blog.id),
                    self._blog_folder_of(blog.id),
                    self._naver_logged_account(),
                )
                for blog in blogs
            ),
            tuple(blog.id for blog in visible),
        )

    def _refresh_dashboard(self) -> None:
        if not hasattr(self, "_blog_list_inner") or self._refreshing:
            return
        blogs = self._dashboard_blogs()
        visible = self._filter_blogs(blogs)
        fp = self._dashboard_fingerprint(blogs, visible)
        if fp == self._dashboard_fp:
            if getattr(self, "_main_tab", "") == "색인 확인":
                self._refresh_index_tab()
            return
        tab = getattr(self, "_main_tab", "")
        self._mark_hidden_tabs_dirty()
        if tab == "색인 확인":
            self._refresh_index_tab()
            return
        if tab != "블로그":
            return
        self._dashboard_fp = fp
        self._blog_dirty = False
        self._refreshing = True
        try:
            self._render_blog_summary(blogs)
            self._render_blogs(blogs, all_blogs=blogs)
        finally:
            self._refreshing = False

    def _render_blog_summary(self, blogs: list[BlogInfo]) -> None:
        for child in self.blog_summary.winfo_children():
            child.destroy()
        total = len(blogs)
        blog_ok = sum(1 for blog in blogs if "collect" in blog.done)
        post_ok = sum(1 for blog in blogs if "collect_post" in blog.done)
        today = datetime.now().date()
        recrawl_today = 0
        for blog in blogs:
            raw = self._last_recrawl(blog.id)
            try:
                if raw and datetime.fromisoformat(raw).date() == today:
                    recrawl_today += 1
            except ValueError:
                pass
        items = (
            ("info", f"전체 {total}"),
            ("ok" if blog_ok == total and total else "wait" if blog_ok else "off", f"블로그수집 {blog_ok}/{total or 0}"),
            ("ok" if post_ok == total and total else "wait" if post_ok else "off", f"글수집 {post_ok}/{total or 0}"),
            ("info" if recrawl_today else "off", f"오늘 재수집 {recrawl_today}"),
        )
        for tone, text in items:
            pill(self.blog_summary, text, tone).pack(side=tk.LEFT, padx=(0, 8))

    def _blog_row_sig(self, blog: BlogInfo) -> tuple:
        status, _tone, extra = self._index_status_view(blog)
        return (
            blog.id,
            blog.name,
            blog.address,
            len(blog.posts or []),
            tuple(sorted(blog.done)),
            self._last_recrawl(blog.id),
            self._naver_id_of(blog.id),
            self._html_code_of(blog.id),
            self._blog_folder_of(blog.id),
            status,
            extra,
            blog.id == str(self.blog_var.get() or ""),
        )

    def _drop_blog_row(self, blog_id: str) -> None:
        row = (getattr(self, "_blog_row_frames", None) or {}).pop(blog_id, None)
        (getattr(self, "_blog_row_sigs", None) or {}).pop(blog_id, None)
        if self._widget_alive(row):
            try:
                row.destroy()
            except Exception:
                pass

    def _collect_blog_row_refs(self) -> None:
        frames = getattr(self, "_blog_row_frames", None) or {}
        self._blog_index_btns = [
            row._index_btn for row in frames.values() if getattr(row, "_index_btn", None) is not None
        ]
        self._index_labels = [
            row._naver_lbl for row in frames.values() if getattr(row, "_naver_lbl", None) is not None
        ]
        if getattr(self, "_index_busy", False):
            for btn in self._blog_index_btns:
                try:
                    btn.configure(state="disabled")
                except Exception:
                    pass

    def _render_blogs(self, blogs: list[BlogInfo], all_blogs: list[BlogInfo] | None = None):
        self._hover.hide()
        self._cancel_after("blog_rows")
        parent = self._blog_list_inner
        source = all_blogs if all_blogs is not None else blogs
        self._shown_blog_keys = [
            (blog.id, blog.address, len(blog.posts or []), tuple(sorted(blog.done)), self._last_recrawl(blog.id))
            for blog in source
        ]
        live_ids = {blog.id for blog in source}
        for blog_id in list(self._blog_check_vars):
            if blog_id not in live_ids:
                self._blog_check_vars.pop(blog_id, None)
        for blog_id in list(getattr(self, "_blog_row_frames", {}) or {}):
            if blog_id not in live_ids:
                self._drop_blog_row(blog_id)
        empty = getattr(self, "blog_empty", None)
        if self._widget_alive(empty):
            try:
                empty.destroy()
            except Exception:
                pass
        self.blog_empty = None
        account_line = self._blog_heading_text(len(source))
        self.blog_heading.configure(text=account_line)
        if not source:
            self._listed_blogs = []
            self._vis_key = None
            self._blog_pending_rows = []
            self.blog_empty = label(parent, "로그인한 계정의 블로그만 표시됩니다.", "body", COLORS["text_muted"])
            self.blog_empty.pack(anchor="w", pady=8)
            self.blog_var.set("")
            self._update_sel_count()
            self._render_blog_detail()
            return

        known = {blog.id for blog in source}
        pending_select = str(getattr(self, "_pending_select_id", "") or "").strip()
        if pending_select and pending_select in known:
            if self.blog_var.get() != pending_select:
                self.blog_var.set(pending_select)
            self._pending_select_id = ""
        elif pending_select:
            self.blog_var.set(pending_select)
        elif source and self.blog_var.get() not in known:
            selected = next((blog.id for blog in source if blog.selected), source[0].id)
            self.blog_var.set(selected)

        self._listed_blogs = list(source)
        keep_scroll = not str(getattr(self, "_scroll_blog_id", "") or "")
        offset = self._blog_scroll_offset()
        pending: list[BlogInfo] = []
        sigs = self.__dict__.setdefault("_blog_row_sigs", {})
        for blog in source:
            blog._search_text = self._blog_search_text(blog)
            sig = self._blog_row_sig(blog)
            row = (self._blog_row_frames or {}).get(blog.id)
            if self._widget_alive(row) and sigs.get(blog.id) == sig:
                continue
            if self._widget_alive(row):
                self._drop_blog_row(blog.id)
            pending.append(blog)
            sigs[blog.id] = sig
        self._blog_pending_rows = pending
        self._vis_key = None
        self._flush_blog_row_batch()
        self._order_blog_rows()
        self._sync_blog_row_paints()
        self._update_sel_count()
        self._render_blog_detail()
        if getattr(self, "_scroll_blog_id", ""):
            target = str(self._scroll_blog_id or "")
            self.root.after(80, lambda bid=target: self._scroll_to_blog_row(bid))
        elif keep_scroll:
            self._restore_blog_scroll(offset)
            self.root.after_idle(lambda value=offset: self._restore_blog_scroll(value))

    def _flush_blog_row_batch(self) -> None:
        parent = getattr(self, "_blog_list_inner", None)
        pending = getattr(self, "_blog_pending_rows", None)
        if parent is None or not pending:
            self._collect_blog_row_refs()
            self._vis_key = None
            self._apply_blog_visibility()
            self._order_blog_rows()
            self._sync_blog_row_paints()
            return
        n = 0
        while pending and n < _BLOG_ROW_BATCH:
            blog = pending.pop(0)
            if blog.id in (self._blog_row_frames or {}) and self._widget_alive(self._blog_row_frames.get(blog.id)):
                n += 1
                continue
            self._render_blog_row(parent, blog, before=self._next_listed_row(blog.id))
            n += 1
        self._vis_key = None
        self._apply_blog_visibility()
        self._order_blog_rows()
        self._collect_blog_row_refs()
        if pending:
            self._after_once("blog_rows", 1, self._flush_blog_row_batch)
        else:
            self._sync_blog_row_paints()

    def _blog_search_text(self, blog: BlogInfo) -> str:
        address = str(blog.address or "")
        host = _search_compact(address)
        parts = [
            blog.name or "",
            address,
            host,
            f"https://{host}" if host else "",
            f"http://{host}" if host else "",
            f"https://{host}/" if host else "",
            blog.id or "",
            self._naver_id_of(blog.id),
            self._html_code_of(blog.id),
        ]
        return " ".join(parts).casefold()

    def _blog_row_matches(self, blog: BlogInfo, query: str) -> bool:
        hay = getattr(blog, "_search_text", None) or self._blog_search_text(blog)
        blog._search_text = hay
        if not _query_matches(hay, query):
            return False
        if self._blog_filter == "blog_pending" and "collect" in blog.done:
            return False
        if self._blog_filter == "post_pending" and "collect_post" in blog.done:
            return False
        if self._blog_filter == "setup_pending" and not any(key not in blog.done for key in SETUP_KEYS):
            return False
        return True

    def _blog_scroll_offset(self) -> float:
        widget = getattr(self, "blog_list", None)
        try:
            return float(getattr(widget, "_offset", 0) or 0)
        except Exception:
            return 0.0

    def _restore_blog_scroll(self, offset: float) -> None:
        widget = getattr(self, "blog_list", None)
        if not self._widget_alive(widget) or not hasattr(widget, "_apply_offset"):
            return
        try:
            widget._offset = float(offset)
            widget._apply_offset()
        except Exception:
            pass

    def _next_listed_row(self, blog_id: str):
        frames = getattr(self, "_blog_row_frames", None) or {}
        seen = False
        for blog in getattr(self, "_listed_blogs", None) or []:
            if not seen:
                if blog.id == blog_id:
                    seen = True
                continue
            row = frames.get(blog.id)
            if self._widget_alive(row):
                return row
        return None

    def _order_blog_rows(self) -> int:
        frames = getattr(self, "_blog_row_frames", None) or {}
        listed = getattr(self, "_listed_blogs", None) or []
        query = (self.blog_query.get() or "").strip() if hasattr(self, "blog_query") else ""
        shown = 0
        for blog in listed:
            row = frames.get(blog.id)
            if not self._widget_alive(row):
                continue
            blog._search_text = getattr(blog, "_search_text", None) or self._blog_search_text(blog)
            if self._blog_row_matches(blog, query):
                try:
                    row.pack(fill=tk.X, pady=3, padx=2)
                except Exception:
                    pass
                shown += 1
            else:
                try:
                    row.pack_forget()
                except Exception:
                    pass
        return shown

    def _apply_blog_visibility(self) -> None:
        rows = getattr(self, "_blog_row_frames", None)
        listed = getattr(self, "_listed_blogs", None)
        if not rows or not listed:
            return
        query = (self.blog_query.get() or "").strip()
        key = (query, self._blog_filter)
        if key == getattr(self, "_vis_key", None):
            return
        self._vis_key = key
        shown = self._order_blog_rows()
        empty = getattr(self, "_blog_filter_empty", None)
        if shown or getattr(self, "_blog_pending_rows", None):
            if empty is not None:
                try:
                    empty.pack_forget()
                except Exception:
                    pass
            return
        parent = getattr(self, "_blog_list_inner", None)
        if parent is None:
            return
        if empty is None or not self._widget_alive(empty):
            self._blog_filter_empty = label(parent, "조건에 맞는 블로그가 없습니다.", "body", COLORS["text_muted"])
            empty = self._blog_filter_empty
        empty.pack(anchor="w", pady=8)

    def _ensure_check(self, blog_id: str) -> tk.BooleanVar:
        var = self._blog_check_vars.get(blog_id)
        if var is None:
            var = tk.BooleanVar(value=False)
            self._blog_check_vars[blog_id] = var
        return var

    def _set_visible_checks(self, value: bool) -> None:
        changed: list[str] = []
        self._checks_batch = True
        try:
            for blog in self._filter_blogs(self._dashboard_blogs()):
                var = self._ensure_check(blog.id)
                if bool(var.get()) == value:
                    continue
                var.set(value)
                changed.append(blog.id)
        finally:
            self._checks_batch = False
        self._update_sel_count()
        for blog_id in changed:
            self._paint_rows_for(blog_id)
        self._schedule_write_count()

    def _checked_count(self) -> int:
        return sum(1 for var in self._blog_check_vars.values() if var.get())

    def _update_sel_count(self) -> None:
        if not hasattr(self, "sel_count_label"):
            return
        n = self._checked_count()
        self.sel_count_label.configure(text=f"{n}개 선택")

    def _on_blog_checked(self, blog_id: str) -> None:
        if getattr(self, "_checks_batch", False):
            return
        self._update_sel_count()
        self._paint_rows_for(blog_id)
        self._schedule_write_count()

    def _toggle_blog_check(self, blog_id: str) -> None:
        var = self._ensure_check(blog_id)
        var.set(not var.get())
        self._on_blog_checked(blog_id)

    def _widget_is_check_target(self, widget) -> bool:
        cur = widget
        for _ in range(8):
            if cur is None:
                return False
            if getattr(cur, "_blog_check_hit", False):
                return True
            name = type(cur).__name__
            if "Check" in name:
                return True
            try:
                cur = cur.master
            except Exception:
                return False
        return False

    def _on_row_click(self, event, blog_id: str):
        if self._widget_is_check_target(event.widget):
            return
        self._select_blog(blog_id)
        self._focus_blog_row(blog_id)

    def _bind_row_focus(self, widget, blog_id: str) -> None:
        widget.bind("<Button-1>", lambda e, bid=blog_id: self._on_row_click(e, bid))
        widget.bind("<Double-Button-1>", lambda _e, bid=blog_id: self._open_blog_address(bid))
        try:
            widget.configure(cursor="hand2")
        except Exception:
            pass

    def _focus_blog_row(self, blog_id: str) -> None:
        row = (getattr(self, "_blog_row_frames", None) or {}).get(blog_id)
        if not self._widget_alive(row):
            return
        try:
            row.focus_set()
        except Exception:
            pass

    def _open_blog_address(self, blog_id: str):
        if not self.session.is_alive() or not self.session.state.logged_in:
            self.log("블로그스팟에 로그인된 크롬이 없어 글 목록을 열지 못했습니다.")
            return "break"
        threading.Thread(target=self._open_blog_tab_worker, args=(blog_id,), daemon=True).start()
        return "break"

    def _open_blog_tab_worker(self, blog_id: str) -> None:
        try:
            url = self.session.open_posts_in_new_tab(blog_id)
            self.log(f"로그인된 크롬 새 탭에서 열었습니다: {url}")
        except Exception as exc:
            self.log(f"블로그 글 목록을 열지 못했습니다: {_exc_text(exc)}")

    def on_delete_blogs(self) -> None:
        blogs = self._selected_blogs("블로그 삭제", require_naver=False, require_address=False)
        if not blogs:
            return
        lines = "\n".join(f"· {blog.name or blog.id}" for blog in blogs[:12])
        extra = f"\n외 {len(blogs) - 12}개" if len(blogs) > 12 else ""
        if not messagebox.askyesno(
            "블로그 삭제",
            f"선택한 블로그 {len(blogs)}개를 블로그스팟에서 삭제합니다.\n글도 함께 지워지며 되돌릴 수 없습니다.\n\n{lines}{extra}",
        ):
            return
        self._settings_busy = True
        self._paused = False
        self._run_control.reset()
        self.settings_btn.configure(state="disabled")
        self.post_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, len(blogs), "블로그 삭제")
        payload = [(blog.id, blog.name or blog.id) for blog in blogs]
        threading.Thread(target=self._delete_blogs_worker, args=(payload,), daemon=True).start()

    def _delete_blogs_worker(self, blogs: list[tuple[str, str]]) -> None:
        failed: list[str] = []
        total = len(blogs)
        try:
            self.session.control = self._run_control
            for index, (blog_id, name) in enumerate(blogs, 1):
                self._run_control.checkpoint()
                self.root.after(0, lambda i=index, t=total, n=name: self._set_progress(i - 1, t, f"블로그 삭제: {n}"))
                self.log(f"블로그 삭제 {index}/{total}: {name}")
                try:
                    self.session.delete_blog(blog_id, name)
                    self._append_blog_log(blog_id, "블로그 삭제")
                    self._drop_deleted_blog(blog_id)
                    self.log(f"블로그를 삭제했습니다: {name}")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    failed.append(f"{name}: {detail}")
                    self.log(f"블로그 삭제 실패: {name} · {detail}")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.root.after(0, lambda: self._set_progress(total, total, "블로그 삭제 완료"))
            if failed:
                text = "\n".join(failed[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("블로그 삭제", m))
        except StopRequested:
            self.log("블로그 삭제를 중지했습니다.")
            self.root.after(0, lambda: self._set_progress(0, total, "중지됨"))
            self.root.after(0, lambda: self._apply_state(self.session.state))
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"블로그 삭제 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("블로그 삭제", m))
        finally:
            self.root.after(0, self._delete_blogs_done)

    def _drop_deleted_blog(self, blog_id: str) -> None:
        self._remember_gone_id(blog_id)
        self.session.state.blogs = [blog for blog in self.session.state.blogs if blog.id != blog_id]
        self._blog_meta.pop(blog_id, None)
        self._progress_map.pop(blog_id, None)
        self._blog_check_vars.pop(blog_id, None)
        if self.blog_var.get() == blog_id:
            self.blog_var.set("")
        self._record_fp = None
        self._record_view_fp = None
        try:
            self._save_blog_meta()
            self._save_progress()
        except Exception:
            pass
        self._schedule_record_view_refresh()
        self._queue_sheet_sync([blog_id], "블로그 삭제", drop=True)

    def _delete_blogs_done(self) -> None:
        self._settings_busy = False
        self._paused = False
        self.settings_btn.configure(state="normal")
        self.post_btn.configure(state="normal")
        self._set_naver_buttons(True)
        self._set_run_controls(False)

    def _mark_check_hit(self, widget) -> None:
        widget._blog_check_hit = True

    def _sync_blog_row_paints(self) -> None:
        frames = getattr(self, "_blog_row_frames", None) or {}
        for blog_id, row in list(frames.items()):
            self._paint_row_frame(row, blog_id)

    def _row_look(self, blog_id: str) -> tuple[str, str, int]:
        if self._ensure_check(blog_id).get():
            return COLORS["row_checked"], COLORS["row_checked_border"], 2
        if blog_id == self.blog_var.get():
            return COLORS["row_focus"], COLORS["row_focus_border"], 2
        return COLORS["card"], COLORS["card_border"], 2

    def _paint_row_widget(self, widget, bg: str, border: str, width: int) -> None:
        signature = (bg, border, width)
        if getattr(widget, "_paint_sig", None) == signature:
            return
        mode = getattr(widget, "_paint_mode", None)
        if mode is None and type(widget) is tk.Frame:
            mode = "tk-border" if "highlightthickness" in widget.keys() else "tk-fill"
        try:
            if mode == "ctk-border":
                widget.configure(fg_color=bg, border_color=border, border_width=width)
            elif mode == "ctk-fill":
                widget.configure(fg_color=bg)
            elif mode == "tk-border":
                widget.configure(bg=bg, highlightbackground=border, highlightthickness=width)
            elif mode == "tk-fill":
                widget.configure(bg=bg)
            else:
                try:
                    widget.configure(fg_color=bg, border_color=border, border_width=width)
                    mode = "ctk-border"
                except Exception:
                    try:
                        widget.configure(fg_color=bg)
                        mode = "ctk-fill"
                    except Exception:
                        try:
                            widget.configure(bg=bg, highlightbackground=border, highlightthickness=width)
                            mode = "tk-border"
                        except Exception:
                            widget.configure(bg=bg)
                            mode = "tk-fill"
                widget._paint_mode = mode
        except Exception:
            return
        widget._paint_sig = signature

    def _render_blog_row(self, parent, blog: BlogInfo, before=None) -> None:
        """블로그 한 줄. 줄마다 캔버스를 그리는 CTk 위젯 대신 가벼운 tk 위젯만 쓴다.

        줄이 50개를 넘어도 스크롤이 끊기지 않게 하려면 한 줄의 위젯 수와 무게를 줄이는 것이 핵심이다.
        """
        bg, border, width = self._row_look(blog.id)
        row = tk.Frame(parent, bg=bg, highlightbackground=border, highlightthickness=width, takefocus=1)
        pack_kw = {"fill": tk.X, "pady": 3, "padx": 2}
        if before is not None and self._widget_alive(before):
            pack_kw["before"] = before
        row.pack(**pack_kw)
        self._blog_row_frames[blog.id] = row
        self._bind_row_focus(row, blog.id)
        row.bind("<Control-c>", lambda e: self._on_copy_blog_url(e))
        row.bind("<Control-C>", lambda e: self._on_copy_blog_url(e))

        top = tk.Frame(row, bg=bg)
        top.pack(fill=tk.X, padx=8, pady=(6, 0))
        self._bind_row_focus(top, blog.id)
        check_var = self._ensure_check(blog.id)
        check = tk.Checkbutton(
            top, text="", variable=check_var, bg=bg, activebackground=bg,
            highlightthickness=0, bd=0, padx=0, pady=0,
            command=lambda bid=blog.id: self._on_blog_checked(bid),
        )
        check.pack(side=tk.LEFT)
        check._blog_id = blog.id
        self._mark_check_hit(check)
        self._blog_buttons.append(check)

        id_chip = tk_pill(top, blog.id[-6:], "info", cursor="hand2")
        id_chip.pack(side=tk.LEFT, padx=(4, 0))
        id_chip._blog_id = blog.id
        id_chip._blog_check_hit = True
        id_chip.bind("<Button-1>", lambda _e, bid=blog.id: self._on_id_chip_click(bid))
        self._hover.bind(id_chip, lambda b=blog: (
            (COLORS["text"], "다중 선택", "body_bold"),
            (COLORS["text_muted"], "아이디를 누르면 작업 대상에 넣거나 뺍니다.", "small"),
            (COLORS["text"], b.id, "caption"),
        ))

        tools = tk.Frame(top, bg=bg)
        tools.pack(side=tk.RIGHT)
        self._bind_row_focus(tools, blog.id)
        setup_done = sum(1 for key in SETUP_KEYS if key in blog.done)
        setup_tone = "ok" if setup_done == len(SETUP_KEYS) else "wait" if setup_done else "off"
        setup_pill = tk_pill(tools, f"설정 {setup_done}/{len(SETUP_KEYS)}", setup_tone)
        setup_pill.pack(side=tk.RIGHT)
        self._hover.bind(setup_pill, lambda b=blog: self._setup_status_hover(b))
        self._bind_row_focus(setup_pill, blog.id)
        folder_path = self._blog_folder_of(blog.id)
        if not folder_path and (blog.address or "").strip():
            folder_path = self._ensure_blog_folder(blog.id, blog.address, blog.name or "")
        if folder_path:
            flat_button(
                tools, "폴더 복사", variant="primary",
                command=lambda bid=blog.id: self._copy_blog_folder(bid),
            ).pack(side=tk.RIGHT, padx=(0, 6))
        index_btn = flat_button(
            tools, "색인확인", variant="ghost",
            command=lambda bid=blog.id: self.on_blog_row_index_check(bid),
        )
        index_btn.pack(side=tk.RIGHT, padx=(0, 6))
        self._blog_index_btns.append(index_btn)
        row._index_btn = index_btn
        if getattr(self, "_index_busy", False):
            index_btn.configure(state="disabled")

        name = blog.name or blog.address or blog.id
        name_lbl = tk.Label(top, text=name, font=FONTS["body_bold"], fg=COLORS["text"], bg=bg)
        name_lbl.pack(side=tk.LEFT, padx=(6, 0))
        self._bind_row_focus(name_lbl, blog.id)
        code_name = self._html_code_of(blog.id)
        if code_name:
            code_pill = tk_pill(top, code_name, "info")
            code_pill.pack(side=tk.LEFT, padx=(6, 0))
            self._bind_row_focus(code_pill, blog.id)

        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/")
        bottom = tk.Frame(row, bg=bg)
        bottom.pack(fill=tk.X, padx=8, pady=(2, 6))
        self._bind_row_focus(bottom, blog.id)
        addr_lbl = tk.Label(
            bottom, text=host or "주소 없음", font=FONTS["small"],
            fg=COLORS["accent"] if host else COLORS["text_light"], bg=bg,
        )
        addr_lbl.pack(side=tk.LEFT)
        self._bind_row_focus(addr_lbl, blog.id)
        status, tone, extra = self._index_status_view(blog)
        index_chip = tk_pill(bottom, status, tone, padx=6, pady=1)
        index_chip.pack(side=tk.LEFT, padx=(8, 0))
        self._bind_row_focus(index_chip, blog.id)
        extra_chip = tk.Label(bottom, text=extra, font=FONTS["small"], fg=COLORS["text_muted"], bg=bg)
        if extra:
            extra_chip.pack(side=tk.LEFT, padx=(4, 0))
        self._bind_row_focus(extra_chip, blog.id)
        row._index_status_pill = index_chip
        row._index_extra_label = extra_chip
        stored = self._naver_id_of(blog.id)
        collected = "collect" in blog.done or "collect_post" in blog.done
        indexed = stored if collected and stored else ""
        caption = f"색인 {indexed}" if indexed else ""
        naver_lbl = tk.Label(
            bottom, text=caption, font=FONTS["small"],
            fg=COLORS["success"] if indexed else COLORS["text_muted"], bg=bg,
        )
        naver_lbl._fallback_index = indexed
        self._bind_row_focus(naver_lbl, blog.id)
        if caption:
            naver_lbl.pack(side=tk.LEFT, padx=(8, 0))
        self._index_labels.append(naver_lbl)
        row._naver_lbl = naver_lbl
        post_count = len(blog.posts)
        if post_count:
            post_text, post_tone = f"글 {post_count}", "ok" if "collect_post" in blog.done else "wait"
        else:
            post_text, post_tone = "글 없음", "off"
        post_pill = tk_pill(bottom, post_text, post_tone)
        post_pill.pack(side=tk.RIGHT)
        self._bind_row_focus(post_pill, blog.id)
        if "collect" in blog.done:
            crawl_lbl = tk.Label(
                bottom, text=self._blog_collect_label(blog.id), font=FONTS["small"],
                fg=COLORS["text_muted"], bg=bg, wraplength=280, anchor="e", justify="right",
            )
            crawl_lbl.pack(side=tk.RIGHT, padx=(0, 8))
            self._bind_row_focus(crawl_lbl, blog.id)
        row._paint_parts = [row, top, tools, bottom]

    def _on_id_chip_click(self, blog_id: str):
        self._toggle_blog_check(blog_id)
        return "break"

    def _select_blog(self, blog_id: str) -> None:
        prev = self.blog_var.get()
        if prev != blog_id:
            self.blog_var.set(blog_id)
            self._paint_rows_for(prev)
            self._paint_rows_for(blog_id)
            if getattr(self, "_main_tab", "") == "기록":
                self._paint_record_rows()
            else:
                self._record_dirty = True
            if getattr(self, "_main_tab", "") == "블로그":
                self._render_blog_detail()
            else:
                self._detail_dirty = True
            self._schedule_write_count()
        self._focus_blog_row(blog_id)

    def _on_blog_selected(self) -> None:
        self._paint_rows_for(self.blog_var.get())
        if getattr(self, "_main_tab", "") == "기록":
            self._paint_record_rows()
        if getattr(self, "_main_tab", "") == "블로그":
            self._render_blog_detail()

    def _paint_rows_for(self, blog_id: str) -> None:
        if not blog_id:
            return
        tab = getattr(self, "_main_tab", "")
        blog_row = (getattr(self, "_blog_row_frames", {}) or {}).get(blog_id)
        index_row = (getattr(self, "_index_row_frames", {}) or {}).get(blog_id)
        if tab == "색인 확인":
            self._paint_row_frame(index_row, blog_id)
            self._mark_row_stale("blog", blog_id)
        elif tab == "블로그":
            self._paint_row_frame(blog_row, blog_id)
            self._mark_row_stale("index", blog_id)
        else:
            self._mark_row_stale("blog", blog_id)
            self._mark_row_stale("index", blog_id)

    def _mark_row_stale(self, kind: str, blog_id: str) -> None:
        name = "_stale_blog_rows" if kind == "blog" else "_stale_index_rows"
        stale = getattr(self, name, None)
        if stale is None:
            stale = set()
            setattr(self, name, stale)
        stale.add(blog_id)

    def _flush_stale_rows(self, kind: str) -> None:
        name = "_stale_blog_rows" if kind == "blog" else "_stale_index_rows"
        stale = getattr(self, name, None) or set()
        if not stale:
            return
        frames = self._blog_row_frames if kind == "blog" else getattr(self, "_index_row_frames", {})
        for blog_id in list(stale):
            self._paint_row_frame((frames or {}).get(blog_id), blog_id)
        stale.clear()

    def _paint_row_frame(self, row, blog_id: str) -> None:
        if not self._widget_alive(row):
            return
        bg, border, width = self._row_look(blog_id)
        parts = getattr(row, "_paint_parts", None) or [row]
        for part in parts:
            if not self._widget_alive(part):
                continue
            self._paint_row_widget(part, bg, border, width if part is row else 0)
            if part is row:
                continue
            for child in part.winfo_children():
                if child is getattr(row, "_status_pill", None) or getattr(child, "_keep_bg", False):
                    continue
                if not isinstance(child, (tk.Label, tk.Checkbutton)):
                    continue
                try:
                    child.configure(bg=bg, activebackground=bg)
                except Exception:
                    try:
                        child.configure(bg=bg)
                    except Exception:
                        pass

    def _paint_blog_rows(self) -> None:
        ids = set(getattr(self, "_blog_row_frames", {}) or {})
        ids.update(getattr(self, "_index_row_frames", {}) or {})
        for blog_id in ids:
            self._paint_rows_for(blog_id)

    def _render_blog_detail(self) -> None:
        self._detail_dirty = False
        wrap = self.blog_detail_wrap
        for child in wrap.winfo_children():
            child.destroy()
        blog = next((item for item in self._dashboard_blogs() if item.id == self.blog_var.get()), None)
        if blog is None:
            if hasattr(self, "posts_heading"):
                self.posts_heading.configure(text="글")
                self.posts_meta.configure(text="왼쪽 목록을 누르면 그 블로그의 글만 보입니다. 아이디는 여러 개 선택용입니다.")
            self._shown_posts = []
            self._update_post_sel_count()
            return
        last = self._fmt_when(self._last_recrawl(blog.id)) or "기록 없음"
        naver_id = self._naver_id_of(blog.id) or "없음"
        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/") or "주소 없음"
        posts = list(reversed(normalize_posts(blog.posts)))
        query = (self.post_query.get() or "").strip()
        shown = []
        for post in posts:
            url = str(post.get("url") or "")
            title = str(post.get("title") or "")
            hay = f"{title} {url} {_search_compact(url)}".casefold()
            if not _query_matches(hay, query):
                continue
            shown.append(post)
        self.posts_heading.configure(text=blog.name or host)
        crawl = "글 수집 완료" if "collect_post" in blog.done else "글 수집 전"
        self.posts_meta.configure(
            text=f"{host}  ·  글 {len(shown)}/{len(posts)}  ·  {crawl}  ·  네이버 {naver_id}  ·  재수집 {last}"
        )
        self._shown_posts = [
            (blog.id, str(post.get("url") or ""), str(post.get("title") or "").strip() or str(post.get("url") or ""))
            for post in shown
            if is_post_permalink(str(post.get("url") or ""))
        ]
        if not shown:
            label(
                wrap,
                "이 블로그에서 인식된 글이 없습니다." if not posts else "검색과 맞는 글이 없습니다.",
                "body",
                COLORS["text_muted"],
            ).pack(anchor="w", pady=8)
            self._update_post_sel_count()
            return
        for index, post in enumerate(shown, start=1):
            url = str(post.get("url") or "")
            if not is_post_permalink(url):
                continue
            title = str(post.get("title") or "").strip() or url
            self._add_post_card(wrap, index, title, url, blog.id)
        self._update_post_sel_count()

    def _blog_collect_label(self, blog_id: str) -> str:
        meta = self._blog_meta.get(blog_id) or {}
        first = str(meta.get("blog_collect_at") or meta.get("last_blog_crawl") or "")
        last = str(meta.get("last_blog_crawl") or first)
        count = self._count_value(meta.get("blog_crawl_count"))
        if not first and not last:
            return "수집 완료"
        return f"수집 {self._fmt_when(first)} · 마지막 {self._fmt_when(last)} · 재수집 {count}"

    def _post_crawl_item(self, blog_id: str, url: str) -> dict:
        crawls = (self._blog_meta.get(blog_id) or {}).get("post_crawls") or {}
        if not isinstance(crawls, dict):
            return {}
        if isinstance(crawls.get(url), dict):
            return crawls[url]
        key = str(url or "").strip().rstrip("/").lower()
        for existing, item in crawls.items():
            if str(existing).strip().rstrip("/").lower() == key and isinstance(item, dict):
                return item
        return {}

    def _post_crawl_label(self, blog_id: str, url: str) -> str:
        item = self._post_crawl_item(blog_id, url)
        if not str(item.get("at") or "").strip():
            return "수집 전"
        first = self._fmt_when(str(item.get("first") or item.get("at") or ""))
        last = self._fmt_when(str(item.get("at") or ""))
        count = self._count_value(item.get("count"))
        return f"수집 {first} · 마지막 {last} · 재수집 {count}"

    def _post_check_key(self, blog_id: str, url: str) -> str:
        return f"{blog_id}\n{str(url or '').strip().rstrip('/').lower()}"

    def _ensure_post_check(self, blog_id: str, url: str) -> tk.BooleanVar:
        key = self._post_check_key(blog_id, url)
        vars_map = self.__dict__.setdefault("_post_check_vars", {})
        var = vars_map.get(key)
        if var is None:
            var = tk.BooleanVar(value=False)
            vars_map[key] = var
        return var

    def _shown_post_items(self) -> list[tuple[str, str, str]]:
        return list(getattr(self, "_shown_posts", None) or [])

    def _set_visible_post_checks(self, value: bool) -> None:
        for blog_id, url, _title in self._shown_post_items():
            self._ensure_post_check(blog_id, url).set(value)
        self._update_post_sel_count()

    def _checked_post_urls(self, blog_id: str) -> list[str]:
        urls: list[str] = []
        seen: set[str] = set()
        for item_blog, url, _title in self._shown_post_items():
            if item_blog != blog_id or not url:
                continue
            if not self._ensure_post_check(item_blog, url).get():
                continue
            key = str(url).strip().rstrip("/").lower()
            if key in seen:
                continue
            seen.add(key)
            urls.append(url)
        return urls

    def _update_post_sel_count(self) -> None:
        label_w = getattr(self, "post_sel_count_label", None)
        if label_w is None:
            return
        n = 0
        for blog_id, url, _title in self._shown_post_items():
            if self._ensure_post_check(blog_id, url).get():
                n += 1
        try:
            label_w.configure(text=f"{n}개 선택")
        except Exception:
            pass

    def on_recrawl_selected_posts(self) -> None:
        if self._any_busy():
            return
        blog = next((item for item in self._dashboard_blogs() if item.id == self.blog_var.get()), None)
        if blog is None or not (blog.address or "").strip():
            messagebox.showwarning("선택 글 재수집", "블로그 주소가 없습니다. 먼저 주소를 인식해 주세요.")
            return
        urls = self._checked_post_urls(blog.id)
        if not urls:
            messagebox.showwarning("선택 글 재수집", "재수집할 글을 먼저 선택해 주세요.")
            return
        self._start_naver_job(
            len(urls),
            "선택 글 재수집",
            self._naver_post_worker,
            [(blog.id, blog.address, urls)],
            True,
        )

    def _add_post_card(self, parent, index: int, title: str, url: str, blog_id: str) -> None:
        """글 한 장. 글이 100개여도 가볍게 스크롤되도록 tk 위젯만 쓴다."""
        bg = COLORS["input_bg"]
        card_row = tk.Frame(parent, bg=bg, highlightbackground=COLORS["border"], highlightthickness=1)
        card_row.pack(fill=tk.X, pady=2, padx=2)
        check_var = self._ensure_post_check(blog_id, url)
        check = tk.Checkbutton(
            card_row, text="", variable=check_var, bg=bg, activebackground=bg,
            highlightthickness=0, bd=0, padx=0, pady=0,
            command=self._update_post_sel_count,
        )
        check.pack(side=tk.LEFT, padx=(6, 0))
        right = tk.Frame(card_row, bg=bg)
        right.pack(side=tk.RIGHT, padx=(6, 8), pady=4)
        tk.Label(
            right, text=self._post_crawl_label(blog_id, url), font=FONTS["small"],
            fg=COLORS["text_muted"], bg=bg, wraplength=240, anchor="e", justify="right",
        ).pack(anchor="e")
        actions = tk.Frame(right, bg=bg)
        actions.pack(anchor="e", pady=(2, 0))
        flat_button(
            actions, "이글 수집", variant="primary",
            command=lambda target=url, blog=blog_id: self.on_collect_one_post(blog, target, False),
        ).pack(side=tk.LEFT, padx=(0, 4))
        flat_button(
            actions, "이글 재수집", variant="ghost",
            command=lambda target=url, blog=blog_id: self.on_collect_one_post(blog, target, True),
        ).pack(side=tk.LEFT, padx=(0, 4))
        flat_button(
            actions, "글 삭제", variant="danger",
            command=lambda target=url, blog=blog_id, name=title: self.on_delete_post(blog, target, name),
        ).pack(side=tk.LEFT)
        left = tk.Frame(card_row, bg=bg)
        left.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(4, 0), pady=4)
        tk.Label(left, text=f"{index}. {title}", font=FONTS["body_bold"], fg=COLORS["text"], bg=bg).pack(anchor="w")

        def open_url(_event=None, target=url):
            webbrowser.open(target)

        link = tk.Label(left, text=url, font=FONTS["small"], fg=COLORS["accent"], bg=bg, cursor="hand2", anchor="w")
        link.pack(anchor="w")
        link.bind("<Button-1>", open_url)

    def _fit_window(self) -> None:
        try:
            self.root.update_idletasks()
            screen_w = self.root.winfo_screenwidth()
            screen_h = self.root.winfo_screenheight()
            max_w = max(980, int(screen_w * 0.92))
            max_h = max(720, int(screen_h * 0.88))
            cur_w = self.root.winfo_width()
            cur_h = self.root.winfo_height()
            self.root.minsize(min(1100, max_w), min(760, max_h))
            self.root.maxsize(max_w, max_h)
            if not getattr(self, "_window_fitted", False):
                self._window_fitted = True
                if cur_w < 400 or cur_h < 400:
                    cur_w, cur_h = 1280, 900
                target_w = min(max_w, max(cur_w, int(screen_w * 0.82)))
                target_h = min(max_h, max(cur_h, int(screen_h * 0.84)))
                self.root.geometry(f"{target_w}x{target_h}")
                return
            if cur_w > max_w or cur_h > max_h:
                self.root.geometry(f"{min(cur_w, max_w)}x{min(cur_h, max_h)}")
        except Exception:
            pass

    def _restore_naver_if_open(self):
        if self._naver_login_busy:
            return
        self._naver_login_busy = True
        self._set_naver_login_button("인식 중...", enabled=False)
        threading.Thread(target=self._naver_restore_worker, daemon=True).start()

    def _naver_restore_worker(self):
        try:
            state = self.naver.recognize()
            if state.logged_in:
                self.root.after(0, lambda: self._on_naver_logged_in(self.naver.state))
            elif self.naver.chrome_running():
                self.root.after(0, self._on_naver_signed_out)
            else:
                self.root.after(0, lambda: self._set_naver_login_button("서치어드바이저 로그인", enabled=True))
                self._naver_login_busy = False
        except Exception as exc:
            self.log(f"서치어드바이저 자동 재연결 실패: {exc}")
            self._naver_login_busy = False
            self.root.after(0, lambda: self._set_naver_login_button("서치어드바이저 로그인", enabled=True))

    def on_naver_login(self):
        if self._naver_login_busy:
            return
        self._naver_login_busy = True
        self._set_naver_login_button("인식 중...", enabled=False)
        self._set_naver_status("서치어드바이저 창의 아이디를 읽는 중", COLORS["warning"])
        threading.Thread(target=self._naver_login_worker, daemon=True).start()

    def _naver_login_worker(self):
        try:
            state = self.naver.recognize()
            if not self.naver.chrome_running():
                self.root.after(0, self._on_naver_closed)
                return
            if not state.logged_in:
                self.root.after(0, self._on_naver_signed_out)
                return
            self.root.after(0, lambda: self._on_naver_logged_in(state))
        except Exception as exc:
            self.log(f"서치어드바이저 인식 오류: {exc}")
            self.root.after(0, lambda: self._naver_login_failed(str(exc)))

    def _naver_count_worker(self):
        try:
            self.naver.count_sites(force_reload=True)
            self.root.after(0, lambda: self._on_naver_logged_in(self.naver.state))
        except Exception as exc:
            self.log(f"사이트 수 인식 오류: {exc}")

    def _on_naver_logged_in(self, state):
        self._naver_login_busy = False
        self._naver_signed_out_noted = False
        self._shown_naver_account = (state.account or "").strip()
        self._set_naver_login_button("다시 인식", enabled=True)
        self._apply_naver_state(state)
        count = state.site_count
        extra = f" / 사이트 {count}개" if count is not None else ""
        self.log(f"서치어드바이저 로그인 확인{extra}")
        self._start_watch()

    def _naver_login_failed(self, reason: str):
        self._naver_login_busy = False
        self._set_naver_login_button("서치어드바이저 로그인", enabled=True)
        self._set_naver_status("서치어드바이저: 로그인 실패", COLORS["danger"])
        messagebox.showerror("서치어드바이저", reason)

    def _on_naver_signed_out(self):
        self._naver_login_busy = False
        self._naver_signed_out_noted = True
        self._shown_naver_account = ""
        self._set_naver_login_button("다시 인식", enabled=True)
        self._apply_naver_state(self.naver.state)

    def _apply_naver_state(self, state) -> None:
        if state.logged_in:
            count = state.site_count
            account = (state.account or "").strip()
            text = "서치어드바이저: 로그인됨"
            if account:
                text = f"서치어드바이저: {account}"
            self._set_naver_status(text, COLORS["success"])
            self._set_naver_site_count(count)
            self._warn_naver_site_limit(count)
        else:
            self._naver_limit_warned_key = None
            self._set_naver_status("서치어드바이저: 로그인 전", COLORS["text_muted"])
            self._set_naver_site_count(None)
        self._dashboard_fp = None
        if hasattr(self, "_blog_list_inner"):
            self._refresh_dashboard()

    def _set_naver_site_count(self, count) -> None:
        widget = getattr(self, "naver_count_label", None)
        if not self._widget_alive(widget):
            return
        parent_bg = COLORS["bg"]
        try:
            parent_bg = widget.master.cget("bg")
        except Exception:
            pass
        if count is None:
            try:
                widget.configure(text="", fg=COLORS["text_muted"], bg=parent_bg, font=FONTS["small"], padx=0, pady=0)
            except Exception:
                widget.configure(text="")
            return
        n = int(count)
        alert = n >= 99
        try:
            widget.configure(
                text=f"사이트 {n}개  한도 주의" if alert else f"사이트 {n}개",
                fg=COLORS["danger"] if alert else COLORS["success"],
                bg=COLORS["wait_bg"] if alert else parent_bg,
                font=FONTS["heading"] if alert else FONTS["small"],
                padx=10 if alert else 0,
                pady=3 if alert else 0,
            )
        except Exception:
            widget.configure(text=f"사이트 {n}개")

    def _warn_naver_site_limit(self, count) -> None:
        if count is None:
            return
        try:
            n = int(count)
        except (TypeError, ValueError):
            return
        if n < 99 or getattr(self, "_reloading", False):
            if n < 99:
                self._naver_limit_warned_key = None
            return
        account = str(self._naver_logged_account() or "").strip()
        key = (account, n)
        if getattr(self, "_naver_limit_warned_key", None) == key:
            return
        self._naver_limit_warned_key = key
        messagebox.showwarning(
            "서치어드바이저",
            f"등록 사이트가 {n}개입니다.\n한도 100개에 거의 찼습니다. 더 등록하기 전에 사이트를 정리해 주세요.",
        )

    def _set_naver_login_button(self, text: str, enabled: bool):
        self.naver_login_btn.configure(text=text, state="normal" if enabled else "disabled")

    def _set_naver_status(self, text: str, color: str):
        try:
            self.naver_status_label.configure(text=text, fg=color)
        except Exception:
            self.naver_status_label.configure(text=text)

    def _require_sessions(self, title: str, require_naver: bool = True, require_blogger: bool = True) -> bool:
        if self._naver_busy or self._settings_busy or self._create_busy:
            messagebox.showwarning(title, "다른 작업이 끝나기를 기다려 주세요.")
            return False
        if require_naver:
            if not self.naver.is_alive() or not self.naver.state.logged_in:
                if self.naver.chrome_running() and self.naver.reattach() and self.naver.state.logged_in:
                    self._apply_naver_state(self.naver.state)
                else:
                    messagebox.showwarning(title, "먼저 서치어드바이저에 로그인해 주세요.")
                    return False
        if require_blogger:
            if not self.session.is_alive() or not self.session.state.logged_in:
                messagebox.showwarning(title, "먼저 블로그스팟에 로그인해 주세요.")
                return False
        return True

    def _checked_blogs(self) -> list[BlogInfo]:
        blogs = self._dashboard_blogs()
        checked = [blog for blog in blogs if self._ensure_check(blog.id).get()]
        if checked:
            return checked
        blog_id = self.blog_var.get().strip()
        blog = next((item for item in blogs if item.id == blog_id), None)
        return [blog] if blog else []

    def _selected_blogs(
        self,
        title: str,
        require_naver: bool = True,
        require_blogger: bool = True,
        require_address: bool = True,
    ) -> list[BlogInfo] | None:
        if not self._require_sessions(title, require_naver=require_naver, require_blogger=require_blogger):
            return None
        blogs = self._checked_blogs()
        if not blogs:
            messagebox.showwarning(title, "적용할 블로그를 선택해 주세요. 아이디나 체크박스로 여러 개를 고를 수 있습니다.")
            return None
        if require_address:
            missing = [blog for blog in blogs if not (blog.address or "").strip()]
            if missing:
                names = ", ".join((blog.name or blog.id) for blog in missing[:4])
                extra = f" 외 {len(missing) - 4}개" if len(missing) > 4 else ""
                messagebox.showwarning(
                    title,
                    f"블로그 주소가 없습니다: {names}{extra}\n먼저 설정 적용으로 주소를 인식해 주세요.",
                )
                return None
        return blogs

    def _post_urls_of(self, blog: BlogInfo) -> list[str]:
        return [str(item.get("url") or "") for item in normalize_posts(blog.posts) if item.get("url")]

    def _offset_progress(self, offset: int, grand_total: int, prefix: str):
        def inner(step: int, total: int, text: str) -> None:
            self._on_settings_progress(offset + step, grand_total, f"{prefix}{text}")

        return inner

    def _start_naver_job(self, total: int, label_text: str, worker, *args):
        self._naver_busy = True
        self._paused = False
        self._run_control.reset()
        self._set_naver_buttons(False)
        self.settings_btn.configure(state="disabled")
        self._set_run_controls(True)
        self._set_progress(0, total, label_text)
        threading.Thread(target=worker, args=args, daemon=True).start()

    def _set_naver_buttons(self, enabled: bool) -> None:
        state = "normal" if enabled else "disabled"
        for btn in (
            self.naver_html_btn,
            self.naver_first_btn,
            self.select_all_btn,
            self.select_none_btn,
            self.blog_recrawl_btn,
            self.blog_delete_btn,
            self.create_blogs_btn,
            self.create_side_btn,
            getattr(self, "post_select_all_btn", None),
            getattr(self, "post_select_none_btn", None),
            getattr(self, "post_recrawl_btn", None),
        ):
            if btn is None:
                continue
            try:
                btn.configure(state=state)
            except Exception:
                pass

    def _install_centered_dialogs(self) -> None:
        if getattr(messagebox, "_app_centered", False):
            return
        root = self.root

        def wrap(fn):
            def inner(*args, **kwargs):
                kwargs.setdefault("parent", root)
                return fn(*args, **kwargs)

            return inner

        for name in (
            "showinfo",
            "showwarning",
            "showerror",
            "askyesno",
            "askokcancel",
            "askquestion",
            "askretrycancel",
            "askyesnocancel",
        ):
            current = getattr(messagebox, name, None)
            if current is not None:
                setattr(messagebox, name, wrap(current))
        for name in ("askdirectory", "askopenfilename", "asksaveasfilename", "askopenfilenames"):
            current = getattr(filedialog, name, None)
            if current is not None:
                setattr(filedialog, name, wrap(current))
        messagebox._app_centered = True

    def _center_on_app(self, win) -> None:
        try:
            win.update_idletasks()
            self.root.update_idletasks()
            width = max(win.winfo_reqwidth(), win.winfo_width())
            height = max(win.winfo_reqheight(), win.winfo_height())
            if width < 80:
                width = 420
            if height < 40:
                height = 180
            x = self.root.winfo_rootx() + max(0, (self.root.winfo_width() - width) // 2)
            y = self.root.winfo_rooty() + max(0, (self.root.winfo_height() - height) // 2)
            screen_w = self.root.winfo_screenwidth()
            screen_h = self.root.winfo_screenheight()
            x = min(max(0, x), max(0, screen_w - width))
            y = min(max(0, y), max(0, screen_h - height))
            win.geometry(f"+{int(x)}+{int(y)}")
        except Exception:
            pass

    def _place_child_win(self, win, width: int, height: int) -> None:
        try:
            win.update_idletasks()
            screen_w = self.root.winfo_screenwidth()
            screen_h = self.root.winfo_screenheight()
            max_w = max(420, int(screen_w * 0.92))
            max_h = max(360, int(screen_h * 0.82))
            width = min(max(int(width), 420), max_w)
            height = min(max(int(height), 360), max_h)
            x = self.root.winfo_rootx() + max(0, (self.root.winfo_width() - width) // 2)
            y = self.root.winfo_rooty() + max(0, (self.root.winfo_height() - height) // 2)
            x = min(max(0, x), max(0, screen_w - width))
            y = min(max(0, y), max(0, screen_h - height))
            win.minsize(420, 360)
            win.maxsize(max_w, max_h)
            win.geometry(f"{width}x{height}+{int(x)}+{int(y)}")
        except Exception:
            pass

    def _open_blog_log_win(self, blog_id: str) -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        win = getattr(self, "_blog_log_win", None)
        self._sync_blog_log_from_disk(blog_id)
        if getattr(self, "_blog_log_open_for", "") != blog_id:
            self._blog_log_open_for = blog_id
            self._blog_log_open_days = None
        if self._widget_alive(win) and self._widget_alive(getattr(self, "_blog_log_list", None)):
            self._blog_log_blog_id = blog_id
            self._fill_blog_log_win()
            try:
                win.lift()
                win.focus_force()
            except Exception:
                pass
            return
        if self._widget_alive(win):
            try:
                win.destroy()
            except Exception:
                pass
            self._blog_log_win = None
        win = tk.Toplevel(self.root)
        self._blog_log_win = win
        self._blog_log_blog_id = blog_id
        win.title("블로그 로그")
        win.configure(bg=COLORS["card"])
        inner = tk.Frame(win, bg=COLORS["card"])
        inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
        inner.grid_columnconfigure(0, weight=1)
        inner.grid_rowconfigure(1, weight=1)

        head = tk.Frame(inner, bg=COLORS["card"])
        head.grid(row=0, column=0, sticky="ew")
        self._blog_log_addr = tk.Label(
            head, text="", font=FONTS["heading"], fg=COLORS["text"], bg=COLORS["card"],
            anchor="w", wraplength=460, justify="left",
        )
        self._blog_log_addr.pack(fill=tk.X)
        self._blog_log_naver = tk.Label(
            head, text="", font=FONTS["body"], fg=COLORS["text"], bg=COLORS["card"], anchor="w",
        )
        self._blog_log_naver.pack(fill=tk.X, pady=(6, 0))
        self._blog_log_posts = tk.Label(
            head, text="", font=FONTS["body"], fg=COLORS["text"], bg=COLORS["card"], anchor="w",
        )
        self._blog_log_posts.pack(fill=tk.X, pady=(2, 0))
        tk.Label(
            head, text="날짜를 누르면 그날 시간만 펼칩니다. 아래 요약은 날짜별로 한 줄입니다.",
            font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["card"],
            anchor="w", wraplength=500, justify="left",
        ).pack(fill=tk.X, pady=(10, 6))

        log_list = scrollable(inner, height=240, bg=COLORS["input_bg"])
        log_list.grid(row=1, column=0, sticky="nsew")
        self._blog_log_list = log_list
        self._blog_log_inner = log_list.inner

        summary_wrap = tk.Frame(inner, bg=COLORS["card"])
        summary_wrap.grid(row=2, column=0, sticky="ew", pady=(10, 0))
        tk.Label(
            summary_wrap, text="날짜별 요약", font=FONTS["subheading"],
            fg=COLORS["text"], bg=COLORS["card"], anchor="w",
        ).pack(fill=tk.X)
        summary_list = scrollable(summary_wrap, height=128, bg=COLORS["input_bg"])
        summary_list.pack(fill=tk.X, pady=(6, 0))
        self._blog_log_summary = summary_list
        self._blog_log_summary_inner = summary_list.inner

        btns = tk.Frame(inner, bg=COLORS["card"])
        btns.grid(row=3, column=0, sticky="ew", pady=(10, 0))
        flat_button(btns, "닫기", variant="ghost", command=lambda: self._close_blog_log_win()).pack(side=tk.RIGHT)

        def on_close() -> None:
            self._close_blog_log_win()

        def on_resize(_event=None) -> None:
            try:
                wrap = max(240, win.winfo_width() - 48)
                self._blog_log_addr.configure(wraplength=wrap)
            except Exception:
                pass

        win.bind("<Configure>", on_resize)
        win.protocol("WM_DELETE_WINDOW", on_close)
        self._fill_blog_log_win()
        self._place_child_win(win, 560, 640)

    def _sync_blog_log_from_disk(self, blog_id: str) -> None:
        path = data_path(BLOG_META_FILE)
        if not os.path.isfile(path):
            return
        try:
            with open(path, "r", encoding="utf-8") as handle:
                raw = json.load(handle) or {}
        except Exception:
            return
        item = raw.get(blog_id) if isinstance(raw, dict) else None
        disk = _parse_activity_log((item or {}).get("activity_log") if isinstance(item, dict) else None)
        if not disk:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        mem = cur.get("activity_log")
        if not isinstance(mem, list) or len(disk) > len(mem):
            cur["activity_log"] = disk
            return
        disk_last = _BLOG_POST_ADD_RE.match(str((disk[-1] or {}).get("text") or ""))
        mem_last = _BLOG_POST_ADD_RE.match(str((mem[-1] or {}).get("text") or "")) if mem else None
        if disk_last and (not mem_last or int(disk_last.group(1)) > int(mem_last.group(1))):
            mem[-1] = dict(disk[-1])

    def _close_blog_log_win(self) -> None:
        win = getattr(self, "_blog_log_win", None)
        self._blog_log_win = None
        self._blog_log_blog_id = ""
        self._blog_log_box = None
        self._blog_log_list = None
        self._blog_log_inner = None
        self._blog_log_summary = None
        self._blog_log_summary_inner = None
        if self._widget_alive(win):
            try:
                win.destroy()
            except Exception:
                pass

    def _blog_log_act_tag(self, text: str) -> str:
        if "미색인" in text or "실패" in text:
            return "bad"
        if "색인됨" in text or "추가" in text:
            return "ok"
        if "변경" in text or "재신청" in text:
            return "wait"
        return "act"

    def _refresh_blog_log_win(self, blog_id: str = "") -> None:
        if not self._widget_alive(getattr(self, "_blog_log_win", None)):
            return
        if blog_id and str(blog_id) != str(getattr(self, "_blog_log_blog_id", "") or ""):
            return
        self._fill_blog_log_win()

    def _toggle_blog_log_day(self, key: str) -> None:
        opened = getattr(self, "_blog_log_open_days", None)
        if opened is None:
            opened = set()
            self._blog_log_open_days = opened
        if key in opened:
            opened.discard(key)
        else:
            opened.add(key)
        self._fill_blog_log_lists()

    def _clear_log_frame(self, widget) -> None:
        if not self._widget_alive(widget):
            return
        for child in list(widget.winfo_children()):
            try:
                child.destroy()
            except Exception:
                pass

    def _bind_log_click(self, widget, handler) -> None:
        widget.bind("<Button-1>", handler)
        for child in widget.winfo_children():
            self._bind_log_click(child, handler)

    def _fill_blog_log_win(self) -> None:
        win = getattr(self, "_blog_log_win", None)
        inner = getattr(self, "_blog_log_inner", None)
        blog_id = str(getattr(self, "_blog_log_blog_id", "") or "").strip()
        if not self._widget_alive(win) or not self._widget_alive(inner) or not blog_id:
            return
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        meta = self._blog_meta.get(blog_id) or {}
        address = str((blog.address if blog else "") or meta.get("address") or "").strip()
        host = re.sub(r"^https?://", "", address, flags=re.I).rstrip("/") or "주소 없음"
        naver_id = self._naver_id_of(blog_id) or "없음"
        posts = normalize_posts((blog.posts if blog else None) or meta.get("posts") or [])
        try:
            self._blog_log_addr.configure(text=host)
            self._blog_log_naver.configure(text=f"색인신청 아이디  {naver_id}")
            self._blog_log_posts.configure(text=f"글 작성  {len(posts)}개")
            win.title(f"블로그 로그 · {host}")
        except Exception:
            pass
        self._blog_log_groups = self._group_blog_logs(_parse_activity_log(meta.get("activity_log")))
        if getattr(self, "_blog_log_open_days", None) is None:
            groups = self._blog_log_groups
            self._blog_log_open_days = {groups[0]["key"]} if groups else set()
        self._fill_blog_log_lists()

    def _fill_blog_log_lists(self) -> None:
        inner = getattr(self, "_blog_log_inner", None)
        summary_inner = getattr(self, "_blog_log_summary_inner", None)
        if not self._widget_alive(inner):
            return
        groups = getattr(self, "_blog_log_groups", None) or []
        opened = getattr(self, "_blog_log_open_days", None) or set()
        log_list = getattr(self, "_blog_log_list", None)
        offset = float(getattr(log_list, "_offset", 0) or 0) if log_list is not None else 0.0
        self._clear_log_frame(inner)
        self._clear_log_frame(summary_inner)
        if not groups:
            tk.Label(
                inner, text="아직 기록이 없습니다.\n글 작성, 재수집, 색인확인을 하면 여기에 남습니다.",
                font=FONTS["body"], fg=COLORS["text_muted"], bg=COLORS["input_bg"],
                justify="left", anchor="w",
            ).pack(anchor="w", padx=12, pady=12)
        else:
            for group in groups:
                self._render_blog_log_day(inner, group, group["key"] in opened)
            if self._widget_alive(summary_inner):
                for group in groups:
                    self._render_blog_log_summary_row(summary_inner, group)
        for widget in (log_list, getattr(self, "_blog_log_summary", None)):
            if widget is None:
                continue
            try:
                widget._offset = offset if widget is log_list else 0.0
                widget._measure_content()
                widget._apply_offset()
            except Exception:
                pass

    def _render_blog_log_day(self, parent, group: dict, opened: bool) -> None:
        key = str(group.get("key") or "")
        items = group.get("items") or []
        summary = str(group.get("summary") or "")
        bg = COLORS["accent_light"] if opened else COLORS["card"]
        block = tk.Frame(parent, bg=COLORS["input_bg"])
        block.pack(fill=tk.X, padx=8, pady=(8, 0))
        head = tk.Frame(
            block, bg=bg, cursor="hand2",
            highlightbackground=COLORS["border"], highlightthickness=1,
        )
        head.pack(fill=tk.X)
        top = tk.Frame(head, bg=bg)
        top.pack(fill=tk.X, padx=10, pady=(8, 2 if opened else 8))
        arrow = "▾" if opened else "▸"
        tk.Label(
            top, text=f"{arrow}  {self._blog_log_day_label(group.get('dt'))}",
            font=FONTS["body_bold"], fg=COLORS["text"], bg=bg, cursor="hand2",
        ).pack(side=tk.LEFT)
        tk.Label(
            top, text=f"{len(items)}건", font=FONTS["small"],
            fg=COLORS["text_muted"], bg=bg, cursor="hand2",
        ).pack(side=tk.RIGHT)
        if not opened and summary:
            tk.Label(
                head, text=summary, font=FONTS["small"], fg=COLORS["text_muted"], bg=bg,
                anchor="w", justify="left", wraplength=460, cursor="hand2",
            ).pack(fill=tk.X, padx=10, pady=(0, 8))
        self._bind_log_click(head, lambda _e, day=key: self._toggle_blog_log_day(day))
        if not opened:
            return
        body = tk.Frame(block, bg=COLORS["card"], highlightbackground=COLORS["border"], highlightthickness=1)
        body.pack(fill=tk.X, pady=(0, 2))
        for item in items:
            dt = item.get("dt")
            stamp = dt.strftime("%H:%M") if dt is not None else "--:--"
            text = str(item.get("text") or "")
            row = tk.Frame(body, bg=COLORS["card"])
            row.pack(fill=tk.X, padx=12, pady=3)
            tk.Label(
                row, text=stamp, font=FONTS["small_bold"], fg=COLORS["text_muted"],
                bg=COLORS["card"], width=6, anchor="w",
            ).pack(side=tk.LEFT)
            tk.Label(
                row, text=text, font=FONTS["body_bold"], fg=self._blog_log_fg(text),
                bg=COLORS["card"], anchor="w",
            ).pack(side=tk.LEFT, fill=tk.X, expand=True)

    def _render_blog_log_summary_row(self, parent, group: dict) -> None:
        row = tk.Frame(parent, bg=COLORS["input_bg"])
        row.pack(fill=tk.X, padx=10, pady=(8, 0))
        tk.Label(
            row, text=self._blog_log_day_label(group.get("dt")),
            font=FONTS["small_bold"], fg=COLORS["text"], bg=COLORS["input_bg"],
            width=14, anchor="w",
        ).pack(side=tk.LEFT, padx=(0, 8))
        tk.Label(
            row, text=str(group.get("summary") or "기록 없음"),
            font=FONTS["small"], fg=COLORS["text_muted"], bg=COLORS["input_bg"],
            anchor="w", justify="left", wraplength=360,
        ).pack(side=tk.LEFT, fill=tk.X, expand=True)

    def _ask_html_code_name(self, title: str, heading: str, initial: str, taken: set[str]) -> str | None:
        outcome: dict[str, str | None] = {"value": None}
        win = ctk.CTkToplevel(self.root) if ctk else tk.Toplevel(self.root)
        win.title(title)
        win.withdraw()
        win.transient(self.root)
        win.resizable(False, False)
        if ctk:
            win.configure(fg_color=COLORS["card"])
        else:
            win.configure(bg=COLORS["card"])
        body = frame(win, COLORS["card"])
        body.pack(fill=tk.BOTH, expand=True, padx=18, pady=16)
        label(body, heading, "heading", COLORS["text"]).pack(anchor="w")
        label(body, "블로그 목록과 기록에 같은 이름으로 표시됩니다.", "small", COLORS["text_muted"]).pack(
            anchor="w", pady=(4, 10)
        )
        var = tk.StringVar(value=initial)
        if ctk:
            entry = ctk.CTkEntry(
                body, textvariable=var, width=360, height=36, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            entry = tk.Entry(body, textvariable=var, width=36, font=FONTS["body"])
        entry.pack(anchor="w")
        error = label(body, "", "small", COLORS["danger"])
        error.pack(anchor="w", pady=(6, 0))
        actions = frame(body, COLORS["card"])
        actions.pack(fill=tk.X, pady=(12, 0))

        def close(value: str | None) -> None:
            outcome["value"] = value
            try:
                win.grab_release()
            except Exception:
                pass
            win.destroy()

        def confirm() -> None:
            name = " ".join(var.get().split())
            if not name:
                error.configure(text="이름을 입력해 주세요.")
                return
            if len(name) > 40:
                error.configure(text="이름은 40자까지 입력할 수 있습니다.")
                return
            if name in taken:
                error.configure(text="이미 있는 코드 이름입니다.")
                return
            close(name)

        button(actions, "취소", variant="ghost", width=88, height=34, command=lambda: close(None)).pack(side=tk.RIGHT)
        button(actions, "확인", variant="primary", width=88, height=34, command=confirm).pack(side=tk.RIGHT, padx=(0, 8))
        win.protocol("WM_DELETE_WINDOW", lambda: close(None))
        win.bind("<Return>", lambda _event: confirm())
        win.bind("<Escape>", lambda _event: close(None))
        self._center_on_app(win)
        try:
            win.deiconify()
            win.lift()
            win.grab_set()
            win.focus_force()
        except Exception:
            pass
        try:
            entry.focus_set()
            entry.select_range(0, "end")
        except Exception:
            pass
        self.root.wait_window(win)
        return outcome["value"]

    def _html_tab_width(self, name: str) -> int:
        return max(88, min(280, 36 + len(name or "코드") * 16))

    def _on_html_code_tab(self, index: int) -> None:
        if getattr(self, "_html_rename_open", False):
            return
        now = time.monotonic()
        if now < getattr(self, "_html_rename_skip_until", 0):
            return
        last_index, last_at = getattr(self, "_html_tab_click", (-1, 0.0))
        self._html_tab_click = (index, now)
        if last_index == index and (now - last_at) <= 0.5:
            self._html_tab_click = (-1, 0.0)
            self.on_rename_html_code(index)
            return
        self.on_select_html_code(index)

    def _bind_html_tab_double(self, widget, index: int) -> None:
        def on_double(_event, pick=index):
            self._html_tab_click = (-1, 0.0)
            self.on_rename_html_code(pick)
            return "break"

        try:
            widget.bind("<Double-Button-1>", on_double, add="+")
        except Exception:
            pass
        for child in widget.winfo_children():
            self._bind_html_tab_double(child, index)

    def _apply_html_code_rename(self, old: str, new: str) -> None:
        changed: list[str] = []
        for blog_id, meta in list((self._blog_meta or {}).items()):
            if not isinstance(meta, dict):
                continue
            if str(meta.get("html_code") or "").strip() != old:
                continue
            meta["html_code"] = new
            changed.append(str(blog_id))
        if not changed:
            return
        try:
            self._save_blog_meta()
        except Exception:
            pass
        self._record_fp = None
        self._dashboard_fp = None
        self._blog_dirty = True
        self._index_dirty = True
        try:
            self._refresh_dashboard()
        except Exception:
            pass
        try:
            self._render_record_rows(force=True)
        except Exception:
            pass
        try:
            self._queue_sheet_sync(changed, "HTML 코드 이름")
        except Exception:
            pass

    def _next_html_code_name(self, used: set[str] | None = None) -> str:
        taken = set(used or set())
        if used is None:
            taken = {str(item.get("name") or "") for item in getattr(self, "_html_codes", [])}
        for offset in range(26):
            name = f"{chr(ord('A') + offset)}코드"
            if name not in taken:
                return name
        number = 27
        while f"{number}코드" in taken:
            number += 1
        return f"{number}코드"

    def _normalize_html_codes(self, raw, fallback_html: str = "") -> list[dict]:
        codes = []
        if isinstance(raw, list):
            for item in raw:
                if isinstance(item, str):
                    codes.append({"name": "", "html": item})
                elif isinstance(item, dict):
                    codes.append({
                        "name": str(item.get("name") or "").strip(),
                        "html": str(item.get("html") if item.get("html") is not None else ""),
                    })
        if not codes:
            codes.append({"name": "A코드", "html": fallback_html or ""})
        used: set[str] = set()
        for item in codes:
            name = item["name"]
            if not name or name in used:
                name = self._next_html_code_name(used)
                item["name"] = name
            used.add(item["name"])
        return codes

    def _flush_html_editor(self) -> None:
        codes = getattr(self, "_html_codes", None)
        widget = getattr(self, "theme_html", None)
        if not isinstance(codes, list) or not codes or not self._widget_alive(widget):
            return
        index = int(getattr(self, "_html_code_index", 0) or 0)
        if index < 0 or index >= len(codes):
            return
        live = self._textbox_get(widget)
        try:
            visible = bool(widget.winfo_viewable())
        except Exception:
            visible = True
        if live.strip() or visible:
            codes[index]["html"] = live

    def _load_html_editor(self) -> None:
        widget = getattr(self, "theme_html", None)
        if not self._widget_alive(widget):
            return
        codes = getattr(self, "_html_codes", None) or []
        index = int(getattr(self, "_html_code_index", 0) or 0)
        html_text = ""
        if codes and 0 <= index < len(codes):
            html_text = str(codes[index].get("html") or "")
        self._textbox_set(widget, html_text)

    def _render_html_code_buttons(self) -> None:
        widget = getattr(self, "html_code_list", None)
        if not self._widget_alive(widget):
            return
        host = getattr(widget, "inner", widget)
        for child in list(host.winfo_children()):
            child.destroy()
        current = int(getattr(self, "_html_code_index", 0) or 0)
        for index, item in enumerate(getattr(self, "_html_codes", []) or []):
            name = str(item.get("name") or f"{index + 1}코드")
            tab = button(
                host,
                name,
                variant="primary" if index == current else "ghost",
                width=self._html_tab_width(name),
                height=32,
                command=lambda pick=index: self._on_html_code_tab(pick),
            )
            tab.pack(side=tk.LEFT, padx=(0, 6), pady=4)
            self._bind_html_tab_double(tab, index)

    def _apply_html_codes(self, raw, index, fallback_html: str = "") -> None:
        self._html_codes = self._normalize_html_codes(raw, fallback_html)
        try:
            picked = int(index or 0)
        except (TypeError, ValueError):
            picked = 0
        if picked < 0 or picked >= len(self._html_codes):
            picked = 0
        self._html_code_index = picked
        self._render_html_code_buttons()
        self._load_html_editor()

    def _export_html_codes(self) -> list[dict]:
        self._flush_html_editor()
        exported = []
        for item in getattr(self, "_html_codes", []) or []:
            exported.append({
                "name": str(item.get("name") or ""),
                "html": str(item.get("html") or ""),
            })
        return exported or [{"name": "A코드", "html": ""}]

    def _selected_html_template(self) -> str:
        self._flush_html_editor()
        codes = getattr(self, "_html_codes", None) or []
        index = int(getattr(self, "_html_code_index", 0) or 0)
        if codes and 0 <= index < len(codes):
            return str(codes[index].get("html") or "")
        widget = getattr(self, "theme_html", None)
        if self._widget_alive(widget):
            return self._textbox_get(widget)
        return ""

    def _selected_html_name(self) -> str:
        codes = getattr(self, "_html_codes", None) or []
        index = int(getattr(self, "_html_code_index", 0) or 0)
        if codes and 0 <= index < len(codes):
            return str(codes[index].get("name") or "")
        return ""

    def on_select_html_code(self, index: int) -> None:
        codes = getattr(self, "_html_codes", None) or []
        if index < 0 or index >= len(codes) or index == int(getattr(self, "_html_code_index", 0) or 0):
            return
        self._flush_html_editor()
        self._html_code_index = index
        self._render_html_code_buttons()
        self._load_html_editor()

    def on_add_html_code(self) -> None:
        self._flush_html_editor()
        if not isinstance(getattr(self, "_html_codes", None), list):
            self._html_codes = []
        taken = {str(item.get("name") or "") for item in self._html_codes}
        name = self._ask_html_code_name("코드 추가", "새 코드 탭 이름", "", taken)
        if not name:
            return
        self._html_codes.append({"name": name, "html": ""})
        self._html_code_index = len(self._html_codes) - 1
        self._render_html_code_buttons()
        self._load_html_editor()
        self.log(f"HTML 코드를 추가했습니다: {name}")
        try:
            self._save_local_settings()
        except Exception:
            pass

    def on_rename_html_code(self, index: int) -> None:
        self._flush_html_editor()
        codes = getattr(self, "_html_codes", None) or []
        if index < 0 or index >= len(codes):
            return
        if getattr(self, "_html_rename_open", False):
            return
        old = str(codes[index].get("name") or "").strip()
        taken = {str(item.get("name") or "") for pos, item in enumerate(codes) if pos != index}
        self._html_rename_open = True
        try:
            name = self._ask_html_code_name("코드 이름", "코드 탭 이름", old, taken)
        finally:
            self._html_rename_open = False
            self._html_rename_skip_until = time.monotonic() + 0.4
        if not name or name == old:
            return
        codes[index]["name"] = name
        self._render_html_code_buttons()
        self._apply_html_code_rename(old, name)
        self.log(f"코드 이름을 바꿨습니다: {old} → {name}")
        try:
            self._save_local_settings()
        except Exception:
            pass

    def on_delete_html_code(self) -> None:
        codes = getattr(self, "_html_codes", None) or []
        if len(codes) <= 1:
            messagebox.showwarning("HTML 편집", "코드는 하나 이상 남겨 주세요.")
            return
        index = int(getattr(self, "_html_code_index", 0) or 0)
        name = str(codes[index].get("name") or "이 코드")
        if not messagebox.askyesno("HTML 편집", f"{name}를 삭제할까요?"):
            return
        del codes[index]
        self._html_codes = codes
        self._html_code_index = min(index, len(codes) - 1)
        self._render_html_code_buttons()
        self._load_html_editor()
        self.log(f"HTML 코드를 삭제했습니다: {name}")
        try:
            self._save_local_settings()
        except Exception:
            pass

    def on_naver_html_insert(self):
        template = self._selected_html_template()
        code_name = self._selected_html_name() or "선택한 코드"
        if not template.strip():
            messagebox.showwarning("네이버 최초 HTML 코드 넣기", f"HTML 편집 탭의 {code_name}에 붙여 넣을 코드를 먼저 적어 주세요.")
            self._show_main_tab("HTML 편집")
            return
        if not re.search(r"<head\b|&lt;head", template, re.I):
            messagebox.showwarning("네이버 최초 HTML 코드 넣기", f"{code_name}에서 <head>를 찾지 못했습니다.")
            self._show_main_tab("HTML 편집")
            return
        blogs = self._selected_blogs("네이버 최초 HTML 코드 넣기")
        if not blogs:
            return
        try:
            self._save_local_settings()
        except Exception:
            pass
        self.log(f"HTML 코드 사용: {code_name}")
        jobs = [(blog.id, blog.address) for blog in blogs]
        self._start_naver_job(
            2 * len(jobs),
            "네이버 최초 HTML 코드 넣기",
            self._naver_html_worker,
            jobs,
            template,
            code_name,
        )

    def on_naver_first_setup(self):
        blogs = self._selected_blogs("네이버 최초 수집")
        if not blogs:
            return
        plan = []
        total = 0
        for blog in blogs:
            posts = self._post_urls_of(blog)
            steps = 5 + len(posts) if posts else 5
            plan.append((blog.id, blog.address, posts, steps))
            total += steps
        self._start_naver_job(total, "네이버 최초 수집", self._naver_first_worker, plan)

    def on_naver_blog_crawl(self):
        self._start_blog_crawl("블로그 수집요청")

    def on_naver_blog_recrawl(self):
        self._start_blog_crawl("블로그 재수집")

    def _start_blog_crawl(self, title: str) -> None:
        blogs = self._selected_blogs(title)
        if not blogs:
            return
        jobs = [(blog.id, blog.address) for blog in blogs]
        self._start_naver_job(len(jobs), title, self._naver_blog_worker, jobs, title)

    def on_naver_post_crawl(self):
        blogs = self._selected_blogs("글페이지 수집요청")
        if not blogs:
            return
        jobs = []
        for blog in blogs:
            posts = self._post_urls_of(blog)
            if posts:
                jobs.append((blog.id, blog.address, posts))
        if not jobs:
            messagebox.showwarning("글페이지 수집요청", "인식된 글 주소가 없습니다. 먼저 글 목록을 인식해 주세요.")
            return
        total = sum(len(posts) for _blog_id, _address, posts in jobs)
        self._start_naver_job(total, "글페이지 수집요청", self._naver_post_worker, jobs)

    def on_collect_one_post(self, blog_id: str, url: str, recrawl: bool = False):
        title = "이글 재수집" if recrawl else "이글 수집"
        if self._any_busy():
            return
        if not self._require_sessions(title, require_blogger=False):
            return
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        if blog is None or not (blog.address or "").strip():
            messagebox.showwarning(title, "블로그 주소가 없습니다. 먼저 주소를 인식해 주세요.")
            return
        if not (url or "").strip():
            messagebox.showwarning(title, "글 주소가 없습니다.")
            return
        self._start_naver_job(
            1,
            title,
            self._naver_one_post_worker,
            blog.id,
            blog.address,
            url,
            recrawl,
        )

    def on_delete_post(self, blog_id: str, url: str, title: str) -> None:
        if self._any_busy():
            return
        if not self.session.is_alive() or not self.session.state.logged_in:
            messagebox.showwarning("글 삭제", "먼저 블로그스팟에 로그인해 주세요.")
            return
        name = (title or url or "이 글").strip()
        if not messagebox.askyesno("글 삭제", f"블로그스팟에서 이 글을 휴지통으로 옮길까요?\n\n{name}"):
            return
        self._post_busy = True
        self._paused = False
        self._run_control.reset()
        self.post_btn.configure(state="disabled")
        self.settings_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, 1, "글 삭제")
        threading.Thread(
            target=self._delete_post_worker,
            args=(blog_id, url, name),
            daemon=True,
        ).start()

    def _delete_post_worker(self, blog_id: str, url: str, title: str) -> None:
        try:
            self._run_control.checkpoint()
            self.session.control = self._run_control
            self.log(f"글 삭제: {title}")
            self.session.delete_published_post(blog_id, url)
            self._forget_deleted_post(blog_id, url)
            self._append_blog_log(blog_id, "글 삭제")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.root.after(0, lambda: self._set_progress(1, 1, "글 삭제 완료"))
        except StopRequested:
            self.log("글 삭제를 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"글 삭제 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("글 삭제", m))
        finally:
            self.root.after(0, self._write_done)
            self._queue_sheet_sync([blog_id], "글 삭제")

    def _forget_deleted_post(self, blog_id: str, url: str) -> None:
        key = (url or "").strip().rstrip("/").lower()
        cur = self._blog_meta.setdefault(blog_id, {})
        posts = []
        for item in normalize_posts(cur.get("posts") or []):
            if str(item.get("url") or "").strip().rstrip("/").lower() == key:
                continue
            posts.append(item)
        cur["posts"] = posts
        crawls = cur.get("post_crawls")
        if isinstance(crawls, dict):
            for existing in list(crawls):
                if str(existing).strip().rstrip("/").lower() == key:
                    crawls.pop(existing, None)
        for blog in self.session.state.blogs:
            if blog.id != blog_id:
                continue
            blog.posts = [
                item
                for item in normalize_posts(blog.posts)
                if str(item.get("url") or "").strip().rstrip("/").lower() != key
            ]
            break
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _naver_html_worker(self, jobs: list[tuple[str, str]], template: str, code_name: str = ""):
        warnings: list[str] = []
        grand = 2 * len(jobs)
        try:
            for index, (blog_id, address) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                blog = next((item for item in self.session.state.blogs if item.id == blog_id), None)
                name = blog.name if blog else blog_id
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"네이버 최초 HTML 코드 넣기: {name} · {address}")
                self.naver.read_account()
                self.session.control = self._run_control

                def inject_theme(snippet: str, target=blog_id, base=template):
                    full = insert_meta_under_head(base, snippet)
                    self.log("메타 태그를 head 바로 아래에 넣었습니다. 편집 코드 전체를 붙여 넣습니다.")
                    self.session.replace_theme_html(target, full)

                try:
                    self.naver.insert_verify_html(
                        address,
                        inject_theme,
                        blog_id=blog_id,
                        control=self._run_control,
                        on_progress=self._offset_progress((index - 1) * 2, grand, prefix),
                        on_item_done=self._on_item_done,
                    )
                    self.log(f"편집 코드 전체를 테마에 붙여 넣었습니다: {name} · {code_name or '코드'}")
                    self._remember_html_code(blog_id, code_name)
                    self._append_blog_log(blog_id, "최초코드 적용")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"네이버 최초 HTML 코드 넣기 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
                    self._append_blog_log(blog_id, "최초코드 실패")
            if not warnings:
                self.log("테마에 HTML 코드를 넣었습니다. 서치어드바이저에서 소유확인을 진행한 뒤 최초 수집을 눌러 주세요.")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.root.after(0, lambda: self._apply_naver_state(self.naver.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("네이버 최초 HTML 코드 넣기", m))
        except StopRequested:
            self.log("네이버 최초 HTML 코드 넣기를 중지했습니다.")
            self.root.after(0, lambda: self._set_progress(0, grand, "중지됨"))
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"네이버 최초 HTML 코드 넣기 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("네이버 최초 HTML 코드 넣기", m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id for blog_id, _address in jobs], "HTML 코드")

    def _naver_first_worker(self, plan: list[tuple[str, str, list[str], int]]):
        warnings: list[str] = []
        grand = sum(item[3] for item in plan)
        offset = 0
        try:
            for index, (blog_id, address, posts, steps) in enumerate(plan, 1):
                self._run_control.checkpoint()
                blog = next((item for item in self.session.state.blogs if item.id == blog_id), None)
                name = blog.name if blog else blog_id
                prefix = f"{index}/{len(plan)} · " if len(plan) > 1 else ""
                self.log(f"네이버 최초 수집 시작: {name} · {address} · 글 {len(posts)}개")
                self.naver.read_account()
                self._remember_naver_id(blog_id)
                self.session.control = self._run_control
                try:
                    result = self.naver.apply_first_collect(
                        address,
                        blog_id=blog_id,
                        post_urls=posts or None,
                        control=self._run_control,
                        on_progress=self._offset_progress(offset, grand, prefix),
                        on_item_done=self._on_item_done,
                    )
                    posts_result = result.get("posts") or {}
                    if posts:
                        self.log(
                            f"네이버 최초 수집 완료: {name} · 글 성공 {posts_result.get('success') or 0} · 실패 {posts_result.get('fail') or 0}"
                        )
                        done_urls = list(posts_result.get("urls") or [])
                        if done_urls:
                            self.root.after(
                                0,
                                lambda bid=blog_id, urls=done_urls: self._stamp_posts(bid, urls, bump_if_exists=True),
                            )
                    else:
                        self.log(f"네이버 최초 수집 완료: {name} · 인식된 글 없음")
                    self._append_blog_log(blog_id, "최초 수집 신청")
                except OwnershipPending as exc:
                    self.log(f"{name}: {exc}")
                    warnings.append(f"{name}: {exc}")
                    self._append_blog_log(blog_id, "최초 수집 대기")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"네이버 최초 수집 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
                    self._append_blog_log(blog_id, "최초 수집 실패")
                offset += steps
            self.log("네이버 최초 수집을 마쳤습니다.")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.root.after(0, lambda: self._apply_naver_state(self.naver.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("네이버 최초 수집", m))
        except StopRequested:
            self.log("네이버 최초 수집을 중지했습니다.")
            self.root.after(0, lambda: self._set_progress(0, grand or 5, "중지됨"))
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"네이버 최초 수집 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("네이버 최초 수집", m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id for blog_id, _address, _posts, _steps in plan], "최초 수집")

    def _naver_blog_worker(self, jobs: list[tuple[str, str]], title: str = "블로그 수집요청"):
        warnings: list[str] = []
        try:
            for index, (blog_id, address) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"{title}: {address}")
                self.naver.read_account()
                self._remember_naver_id(blog_id)
                self.naver.control = self._run_control
                self.naver._on_progress = self._offset_progress(index - 1, len(jobs), prefix)
                self.naver._on_item_done = self._on_item_done
                try:
                    self.naver.request_blog_crawl(address, blog_id=blog_id)
                    self._on_settings_progress(index, len(jobs), f"{prefix}{title}")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"{title} 오류: {address} · {detail}")
                    warnings.append(f"{address}: {detail}")
                    self._append_blog_log(blog_id, "재수집 실패" if "재수집" in title else "수집 실패")
            self.log(f"{title}을 마쳤습니다.")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text, t=title: messagebox.showwarning(t, m))
        except StopRequested:
            self.log(f"{title}을 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"{title} 오류: {detail}")
            self.root.after(0, lambda m=detail, t=title: messagebox.showerror(t, m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id for blog_id, _address in jobs], title)

    def _naver_post_worker(self, jobs: list[tuple[str, str, list[str]]], recrawl: bool = False):
        warnings: list[str] = []
        grand = sum(len(posts) for _blog_id, _address, posts in jobs)
        offset = 0
        title = "선택 글 재수집" if recrawl else "글페이지 수집요청"
        try:
            for index, (blog_id, address, posts) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"{title} {len(posts)}개 · {address}")
                self.naver.read_account()
                self._remember_naver_id(blog_id)
                self.naver.control = self._run_control
                self.naver._on_progress = self._offset_progress(offset, grand, prefix)
                self.naver._on_item_done = self._on_item_done
                try:
                    result = self.naver.request_post_crawls(
                        address,
                        posts,
                        blog_id=blog_id,
                        progress_base=0,
                        progress_total=len(posts),
                    )
                    self.log(
                        f"{title}을 마쳤습니다. {address} · 성공 {result.get('success') or 0} · 실패 {result.get('fail') or 0}"
                    )
                    done_urls = list(result.get("urls") or [])
                    if done_urls:
                        self.root.after(
                            0,
                            lambda bid=blog_id, urls=done_urls, again=recrawl: self._stamp_posts(
                                bid, urls, recrawl=again, bump_if_exists=not again
                            ),
                        )
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"{title} 오류: {address} · {detail}")
                    warnings.append(f"{address}: {detail}")
                offset += len(posts)
            self.root.after(0, lambda: self._apply_state(self.session.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text, t=title: messagebox.showwarning(t, m))
        except StopRequested:
            self.log(f"{title}을 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"{title} 오류: {detail}")
            self.root.after(0, lambda m=detail, t=title: messagebox.showerror(t, m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id for blog_id, _address, _posts in jobs], title)

    def _naver_one_post_worker(self, blog_id: str, address: str, url: str, recrawl: bool):
        title = "이글 재수집" if recrawl else "이글 수집"
        try:
            self._run_control.checkpoint()
            self.log(f"{title}: {url}")
            self.naver.read_account()
            self._remember_naver_id(blog_id)
            self.naver.control = self._run_control
            self.naver._on_progress = lambda step, total, text: self._on_settings_progress(step, 1, f"{title} {text}")
            self.naver._on_item_done = self._on_item_done
            result = self.naver.request_post_crawls(
                address,
                [url],
                blog_id=blog_id,
                progress_base=0,
                progress_total=1,
            )
            if result.get("success"):
                self.root.after(0, lambda: self._stamp_one_post(blog_id, url, recrawl))
                self.log(f"{title} 완료: {url}")
            else:
                self.log(f"{title} 실패: {url}")
                self.root.after(0, lambda: messagebox.showwarning(title, f"수집 요청에 실패했습니다.\n{url}"))
            self.root.after(0, lambda: self._apply_state(self.session.state))
        except StopRequested:
            self.log(f"{title}을 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"{title} 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror(title, m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id], title)

    def _count_value(self, raw) -> int:
        try:
            return max(0, int(raw or 0))
        except (TypeError, ValueError):
            return 0

    def _fill_missing_post_crawls(self) -> None:
        changed = False
        for meta in self._blog_meta.values():
            if not isinstance(meta, dict):
                continue
            when = str(meta.get("last_post_crawl") or "").strip()
            crawls = meta.get("post_crawls")
            if not when or not isinstance(crawls, dict) or crawls:
                continue
            filled = {}
            for post in normalize_posts(meta.get("posts") or []):
                url = str(post.get("url") or "").strip()
                if not url:
                    continue
                filled[url] = {"at": when, "first": when, "kind": "collect", "count": 0}
            if not filled:
                continue
            meta["post_crawls"] = filled
            changed = True
        if changed:
            try:
                self._save_blog_meta()
            except Exception:
                pass

    def _stamp_posts(self, blog_id: str, urls: list[str], recrawl: bool = False, bump_if_exists: bool = False) -> None:
        for url in urls:
            self._stamp_one_post(blog_id, url, recrawl, bump_if_exists=bump_if_exists, refresh=False)
        self._append_blog_log(blog_id, "재수집 신청" if recrawl else "글 수집 신청")
        self._dashboard_fp = None
        self._refresh_dashboard()

    def _stamp_one_post(
        self,
        blog_id: str,
        url: str,
        recrawl: bool,
        bump_if_exists: bool = False,
        refresh: bool = True,
    ) -> None:
        now = datetime.now().isoformat(timespec="minutes")
        cur = self._blog_meta.setdefault(blog_id, {})
        crawls = cur.get("post_crawls")
        if not isinstance(crawls, dict):
            crawls = {}
            cur["post_crawls"] = crawls
        prev = self._post_crawl_item(blog_id, url)
        count = self._count_value(prev.get("count"))
        repeat = bool(str(prev.get("at") or "").strip())
        if recrawl or (bump_if_exists and repeat):
            count += 1
        first = str(prev.get("first") or "").strip() or now
        stored = next(
            (
                existing
                for existing in crawls
                if str(existing).strip().rstrip("/").lower() == str(url).strip().rstrip("/").lower()
            ),
            url,
        )
        crawls[stored] = {
            "at": now,
            "first": first,
            "kind": "recrawl" if recrawl or (bump_if_exists and repeat) else "collect",
            "count": count,
        }
        cur["last_post_crawl"] = now
        cur["last_activity"] = now
        try:
            self._save_blog_meta()
        except Exception:
            pass
        if refresh:
            self._append_blog_log(blog_id, "재수집 신청" if recrawl else "글 수집 신청")
            self._dashboard_fp = None
            self._refresh_dashboard()

    def _naver_apply_done(self):
        self._naver_busy = False
        self._paused = False
        self._set_naver_buttons(True)
        self.settings_btn.configure(state="normal")
        self._set_run_controls(False)

    def on_apply_settings(self):
        blogs = self._selected_blogs("설정 적용", require_naver=False, require_address=False)
        if not blogs:
            return

        lines = self._description_lines()
        folder = self.favicon_var.get().strip()
        try:
            if folder:
                self._pick_random_image(folder)
        except Exception as exc:
            messagebox.showerror("파비콘", str(exc))
            return

        jobs = []
        for blog in blogs:
            description = random.choice(lines) if lines else ""
            favicon_path = ""
            if folder:
                try:
                    favicon_path = self._pick_random_image(folder)
                except Exception:
                    favicon_path = ""
            jobs.append((blog.id, description, favicon_path))
            if description:
                self.log(f"구글,네이버 디스크립션 랜덤 선택: {blog.name or blog.id} · {description}")
            if favicon_path:
                self.log(f"파비콘 랜덤 선택: {blog.name or blog.id} · {os.path.basename(favicon_path)}")
        if jobs and jobs[0][1]:
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append(jobs[0][1])
            except Exception:
                pass

        self._save_local_settings()
        self._settings_busy = True
        self._paused = False
        self._run_control.reset()
        self.settings_btn.configure(state="disabled")
        self.post_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, 8 * len(jobs), "시작")
        threading.Thread(
            target=self._settings_worker,
            args=(jobs,),
            daemon=True,
        ).start()

    def _settings_worker(self, jobs: list[tuple[str, str, str]]):
        warnings: list[str] = []
        grand = 8 * len(jobs)
        try:
            for index, (blog_id, description, favicon_path) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                blog = next((item for item in self.session.state.blogs if item.id == blog_id), None)
                name = blog.name if blog else blog_id
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"설정 적용 시작: {name}")
                try:
                    address = self.session.apply_basic_settings(
                        blog_id,
                        description,
                        favicon_path,
                        control=self._run_control,
                        on_progress=self._offset_progress((index - 1) * 8, grand, prefix),
                        on_item_done=self._on_item_done,
                    )
                    if address and blog:
                        blog.address = address
                    self.log(f"설정 적용을 마쳤습니다: {name}")
                    self._log_settings_apply(blog_id, ok=True)
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"설정 적용 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
                    self._log_settings_apply(blog_id, ok=False)
            self.log("설정 적용을 마쳤습니다.")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("설정 적용", m))
        except StopRequested:
            self.log("설정을 중지했습니다.")
            self.root.after(0, lambda: self._set_progress(0, grand or 8, "중지됨"))
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"설정 적용 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("설정 적용", m))
        finally:
            self.root.after(0, self._settings_done)
            self._queue_sheet_sync([blog_id for blog_id, _description, _favicon in jobs], "설정 적용")

    def _on_settings_progress(self, step: int, total: int, label_text: str) -> None:
        self.root.after(0, lambda: self._set_progress(step, total, label_text))

    def _on_item_done(self, blog_id: str, key: str) -> None:
        self.root.after(0, lambda: self._item_done_ui(blog_id, key))

    def _item_done_ui(self, blog_id: str, key: str) -> None:
        for blog in self.session.state.blogs:
            if blog.id == blog_id:
                blog.done.add(key)
                break
        items = self._progress_map.setdefault(blog_id, [])
        if key not in items:
            items.append(key)
        try:
            self._save_progress()
        except Exception:
            pass
        self._stamp_activity(blog_id, key)
        self._dashboard_fp = None
        self._schedule_record_view_refresh()
        self._refresh_dashboard()

    def _stamp_activity(self, blog_id: str, key: str) -> None:
        now = datetime.now().isoformat(timespec="minutes")
        cur = self._blog_meta.setdefault(blog_id, {})
        cur["last_activity"] = now
        if key == "collect":
            had_collect = bool(str(cur.get("blog_collect_at") or "").strip())
            count = self._count_value(cur.get("blog_crawl_count"))
            if str(cur.get("last_blog_crawl") or "").strip():
                count += 1
            if not had_collect:
                cur["blog_collect_at"] = str(cur.get("last_blog_crawl") or "").strip() or now
            cur["blog_crawl_count"] = count
            cur["last_blog_crawl"] = now
            self._append_work_event(blog_id, "블로그 수집")
            self._append_blog_log(blog_id, "재수집 신청" if had_collect else "최초 수집 신청")
        elif key == "collect_post":
            cur["last_post_crawl"] = now
            self._append_work_event(blog_id, "글 수집")
        if key in SETTINGS_APPLY_KEYS:
            done = set(self._progress_map.get(blog_id) or [])
            done.add(key)
            if all(item in done for item in SETTINGS_APPLY_KEYS):
                cur["settings_applied_at"] = now
        elif key in {"theme_head", "naver_verify"}:
            self._append_blog_log(blog_id, "최초코드 적용")
        if key in {"collect", "collect_post"}:
            self._remember_naver_id(blog_id)
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _set_progress(self, step: int, total: int, label_text: str) -> None:
        total = total or 1
        ratio = max(0.0, min(1.0, step / total))
        extra = " · 일시정지" if self._paused else ""
        text = f"{step}/{total}  {label_text}{extra}"
        self.progress_label.configure(text=text)
        try:
            self.progress_bar["value"] = ratio * 100
        except Exception:
            pass

    def _set_run_controls(self, enabled: bool) -> None:
        state = "normal" if enabled else "disabled"
        self.pause_btn.configure(state=state)
        self.stop_btn.configure(state=state)
        if not enabled:
            self._paused = False
            self.pause_btn.configure(text="일시정지")

    def on_toggle_pause(self):
        if not self._settings_busy and not self._naver_busy and not self._create_busy and not self._post_busy:
            return
        if self._paused:
            self._paused = False
            self._run_control.request_resume()
            self.pause_btn.configure(text="일시정지")
            self.log("작업을 계속합니다.")
        else:
            self._paused = True
            self._run_control.request_pause()
            self.pause_btn.configure(text="계속")
            self.log("작업을 일시정지했습니다.")

    def on_stop_settings(self):
        if not self._settings_busy and not self._naver_busy and not self._create_busy and not self._post_busy:
            return
        self._run_control.request_stop()
        self._paused = False
        self.pause_btn.configure(text="일시정지")
        self.log("중지를 요청했습니다.")

    def _settings_done(self):
        self._settings_busy = False
        self._paused = False
        self.settings_btn.configure(state="normal")
        self.post_btn.configure(state="normal")
        self._set_naver_buttons(True)
        self._set_run_controls(False)

    def _create_title_lines(self) -> list[str]:
        raw = self._current_text("create", getattr(self, "create_titles", None))
        return [line.strip() for line in raw.splitlines() if line.strip()]

    def on_create_blogs(self):
        if self._any_busy():
            return
        if not self.session.is_alive() or not self.session.state.logged_in:
            messagebox.showwarning("블로그 생성", "먼저 블로그스팟에 로그인해 주세요.")
            return
        titles = self._create_title_lines()
        if not titles:
            messagebox.showwarning("블로그 생성", "만들기 탭에 만들 블로그 제목을 한 줄에 하나씩 적어 주세요.")
            return
        self._create_busy = True
        self._paused = False
        self._run_control.reset()
        self.settings_btn.configure(state="disabled")
        self.post_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, len(titles), "블로그 생성 시작")
        self.log(f"블로그 {len(titles)}개를 순서대로 만듭니다.")
        folder_root = self._blog_folders_root()
        self._save_local_settings()
        threading.Thread(target=self._create_blogs_worker, args=(titles, folder_root), daemon=True).start()

    def _create_blogs_worker(self, titles: list[str], folder_root: str = ""):
        warnings: list[str] = []
        total = len(titles)
        try:
            self.session.control = self._run_control
            results = self.session.create_blogs(
                titles,
                control=self._run_control,
                on_progress=self._on_settings_progress,
            )
            made = [item for item in results if item.get("ok")]
            failed = [item for item in results if not item.get("ok")]
            if made:
                self.log(f"블로그 {len(made)}개를 만들었습니다.")
            for item in made:
                address = str(item.get("address") or "").strip()
                folder = self._make_blog_address_folder(address, folder_root) if folder_root else ""
                if folder:
                    self.log(f"블로그 폴더를 만들었습니다: {folder}")
                    self.root.after(
                        0,
                        lambda bid=str(item.get("id") or ""), addr=address, path=folder, title=str(item.get("title") or ""): self._remember_blog_folder(bid, addr, path, title),
                    )
                else:
                    self.log(f"블로그 주소를 몰라 폴더를 만들지 못했습니다: {item.get('title') or address or '?'}")
            for item in failed:
                name = item.get("title") or "?"
                detail = str(item.get("error") or "생성 결과를 확인하지 못했습니다")
                warnings.append(f"{name}: {detail}")
                self.log(f"블로그 생성 실패: {name} · {detail}")
            created_ids = [str(item.get("id") or "") for item in made if item.get("id")]
            created_titles = [
                str(item.get("title") or "")
                for item in made
                if not item.get("id") and item.get("title")
            ]
            self.root.after(
                0,
                lambda ids=list(created_ids), titles=list(created_titles): self._select_created_blogs(ids, titles),
            )
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("블로그 생성", m))
        except StopRequested:
            self.log("블로그 생성을 중지했습니다.")
            self.root.after(0, lambda: self._set_progress(0, total, "중지됨"))
            self.root.after(0, lambda: self._apply_state(self.session.state))
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"블로그 생성 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("블로그 생성", m))
        finally:
            self.root.after(0, self._create_blogs_done)

    def _select_created_blogs(self, ids: list[str], titles: list[str] | None = None) -> None:
        picked: list[str] = []
        seen: set[str] = set()
        for raw in ids:
            blog_id = str(raw or "").strip()
            if blog_id and blog_id not in seen:
                seen.add(blog_id)
                picked.append(blog_id)
        by_name: dict[str, list[str]] = {}
        for blog in self.session.state.blogs:
            by_name.setdefault(blog.name or "", []).append(blog.id)
        for raw_title in titles or []:
            matches = by_name.get(str(raw_title or "").strip()) or []
            if not matches:
                continue
            numeric = [item for item in matches if str(item).isdigit()]
            blog_id = max(numeric, key=int) if numeric else matches[-1]
            if blog_id not in seen:
                seen.add(blog_id)
                picked.append(blog_id)
        live = {blog.id for blog in self.session.state.blogs}
        if live:
            picked = [blog_id for blog_id in picked if blog_id in live] or picked
        prev = str(self.blog_var.get() or "")
        if picked:
            focus_id = picked[-1]
            self._pending_select_id = focus_id
            self.blog_var.set(focus_id)
            self._scroll_blog_id = focus_id
            self._paint_rows_for(prev)
            self._paint_rows_for(focus_id)
        self._apply_state(self.session.state)
        if not picked:
            return
        self._update_sel_count()
        self._show_main_tab("블로그")
        self._dashboard_fp = None
        self._schedule_dashboard()
        self._schedule_sheet_sync(picked, "블로그 생성", new_ids=picked)
        for blog_id in picked:
            self._append_blog_log(blog_id, "블로그 생성")
        self.root.after(150, lambda bid=picked[-1], old=prev: self._finish_created_select(bid, old))

    def _finish_created_select(self, blog_id: str, prev_id: str = "") -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            return
        self._pending_select_id = blog_id
        if self.blog_var.get() != blog_id:
            self.blog_var.set(blog_id)
        self._pending_select_id = ""
        if prev_id and prev_id != blog_id:
            self._paint_rows_for(prev_id)
        self._sync_blog_row_paints()
        self._paint_rows_for(blog_id)
        self._scroll_to_blog_row(blog_id)
        if getattr(self, "_main_tab", "") == "블로그":
            self._render_blog_detail()

    def _scroll_blog_list_to_end(self) -> None:
        widget = getattr(self, "blog_list", None)
        if not self._widget_alive(widget) or not hasattr(widget, "scroll_to_end"):
            return
        try:
            widget.update_idletasks()
            widget.scroll_to_end()
        except Exception:
            pass

    def _scroll_to_blog_row(self, blog_id: str) -> None:
        blog_id = str(blog_id or "").strip()
        if not blog_id:
            self._scroll_blog_id = ""
            return
        row = (getattr(self, "_blog_row_frames", None) or {}).get(blog_id)
        if not self._widget_alive(row):
            if getattr(self, "_blog_pending_rows", None):
                self.root.after(80, lambda bid=blog_id: self._scroll_to_blog_row(bid))
                return
            self._scroll_blog_id = ""
            return
        self._scroll_blog_id = ""
        widget = getattr(self, "blog_list", None)
        if self._widget_alive(widget) and hasattr(widget, "scroll_to_widget"):
            try:
                widget.scroll_to_widget(row)
            except Exception:
                pass
        self._focus_blog_row(blog_id)
        self._paint_rows_for(blog_id)

    def _create_blogs_done(self):
        self._create_busy = False
        self._paused = False
        self.settings_btn.configure(state="normal")
        self.post_btn.configure(state="normal")
        self._set_naver_buttons(True)
        self._set_run_controls(False)

    def _manuscript_files(self, folder: str) -> list[str]:
        files = []
        for name in os.listdir(folder):
            path = os.path.join(folder, name)
            if not os.path.isfile(path):
                continue
            if os.path.splitext(name)[1].lower() != ".txt":
                continue
            files.append(path)
        files.sort(key=lambda item: os.path.basename(item).lower())
        return files

    def _read_manuscript(self, path: str) -> str:
        for encoding in ("utf-8-sig", "utf-8", "cp949"):
            try:
                with open(path, "r", encoding=encoding) as handle:
                    return handle.read()
            except UnicodeDecodeError:
                continue
        raise RuntimeError(f"원고를 읽지 못했습니다: {os.path.basename(path)}")

    def _manuscript_html(self, text: str) -> str:
        raw = (text or "").replace("\r\n", "\n").replace("\r", "\n").strip()
        if re.search(r"<\s*(p|div|br|img|h[1-6]|span|table|a|ul|ol|li)\b", raw, re.I):
            return raw
        parts = []
        for line in raw.split("\n"):
            if line.strip():
                parts.append(f"<p>{html.escape(line)}</p>")
            else:
                parts.append("<p><br></p>")
        return "\n".join(parts)

    def _move_manuscript_to_success(self, path: str, folder: str) -> str:
        dest_dir = os.path.join(folder, "성공")
        os.makedirs(dest_dir, exist_ok=True)
        name = os.path.basename(path)
        stem, ext = os.path.splitext(name)
        dest = os.path.join(dest_dir, name)
        index = 2
        while os.path.exists(dest):
            dest = os.path.join(dest_dir, f"{stem}_{index}{ext}")
            index += 1
        shutil.move(path, dest)
        return dest

    def _schedule_write_count(self) -> None:
        self._after_once("write_count", 200, self._refresh_write_count)

    def _manuscript_file_count(self, folder: str) -> int:
        if not folder or not os.path.isdir(folder):
            return 0
        try:
            stamp = os.path.getmtime(folder)
        except OSError:
            stamp = 0
        cached = getattr(self, "_manuscript_count_cache", None)
        key = (folder, stamp)
        if cached and cached[0] == key:
            return cached[1]
        try:
            count = len(self._manuscript_files(folder))
        except Exception:
            count = 0
        self._manuscript_count_cache = (key, count)
        return count

    def _refresh_write_count(self) -> None:
        widget = getattr(self, "write_count_label", None)
        if not self._widget_alive(widget):
            return
        blog_count = self._checked_count() if hasattr(self, "_blog_check_vars") else 0
        if blog_count == 0 and hasattr(self, "blog_var") and self.blog_var.get().strip():
            blog_count = 1
        folder = self.manuscript_var.get().strip() if hasattr(self, "manuscript_var") else ""
        file_count = self._manuscript_file_count(folder)
        raw = self.write_count_var.get().strip() if hasattr(self, "write_count_var") else ""
        count = int(raw) if raw.isdigit() and int(raw) >= 1 else 0
        if count == 0:
            text = "작성할 글 개수를 1 이상으로 적어 주세요."
        elif blog_count == 0:
            text = f"작성할 글 {count}개 · 블로그를 체크하거나 목록에서 눌러 주세요."
        elif file_count < count:
            text = f"작성할 글 {count}개 · 원고는 {file_count}개뿐입니다."
        else:
            text = f"작성할 글 {count}개 · 블로그 {blog_count}개 · 원고 {file_count}개"
        try:
            widget.configure(text=text)
        except Exception:
            pass

    def _ask_write_count(self, plans: list[tuple]) -> int | None:
        counts = [len(files) for _blog, _folder, files in plans]
        same = len(set(counts)) == 1
        default = str(counts[0]) if same else ""
        outcome: dict[str, int | None] = {"value": None}
        win = ctk.CTkToplevel(self.root) if ctk else tk.Toplevel(self.root)
        win.title("글 작성")
        win.withdraw()
        win.transient(self.root)
        win.resizable(False, False)
        if ctk:
            win.configure(fg_color=COLORS["card"])
        else:
            win.configure(bg=COLORS["card"])
        body = frame(win, COLORS["card"])
        body.pack(fill=tk.BOTH, expand=True, padx=18, pady=16)
        label(body, "폴더의 txt", "heading", COLORS["text"]).pack(anchor="w")
        lines = []
        for blog, _folder, files in plans:
            lines.append(f"{blog.name or blog.id} · txt {len(files)}개")
        label(body, "\n".join(lines), "body", COLORS["text"], justify="left").pack(anchor="w", pady=(8, 6))
        if same:
            hint = "기본값은 폴더 안 txt 전부입니다. 숫자를 줄이면 그만큼만 씁니다."
        else:
            hint = "비워 두면 블로그마다 폴더의 txt를 모두 씁니다. 숫자를 적으면 블로그마다 그 개수만 씁니다."
        label(body, hint, "small", COLORS["text_muted"], wraplength=440, justify="left").pack(anchor="w", pady=(0, 10))
        row = frame(body, COLORS["card"])
        row.pack(fill=tk.X)
        label(row, "작성할 글 개수", "body_bold", COLORS["text"]).pack(side=tk.LEFT)
        var = tk.StringVar(value=default)
        if ctk:
            entry = ctk.CTkEntry(
                row, textvariable=var, width=88, height=34, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            entry = tk.Entry(row, textvariable=var, width=8, font=FONTS["body"])
        entry.pack(side=tk.LEFT, padx=(8, 0))
        actions = frame(body, COLORS["card"])
        actions.pack(fill=tk.X, pady=(14, 0))

        def close(value: int | None) -> None:
            outcome["value"] = value
            try:
                win.grab_release()
            except Exception:
                pass
            win.destroy()

        def confirm() -> None:
            raw = var.get().strip()
            if not raw:
                close(0)
                return
            if not raw.isdigit() or int(raw) < 1:
                messagebox.showwarning("글 작성", "1 이상의 개수를 적거나, 비워 두면 폴더의 txt를 모두 씁니다.", parent=win)
                return
            close(int(raw))

        button(actions, "취소", variant="ghost", width=88, height=34, command=lambda: close(None)).pack(side=tk.RIGHT)
        button(actions, "글 작성", variant="success", width=100, height=34, command=confirm).pack(side=tk.RIGHT, padx=(0, 8))
        win.protocol("WM_DELETE_WINDOW", lambda: close(None))
        win.bind("<Return>", lambda _event: confirm())
        win.bind("<Escape>", lambda _event: close(None))
        self._center_on_app(win)
        try:
            win.deiconify()
            win.lift()
            win.grab_set()
            win.focus_force()
        except Exception:
            pass
        entry.focus_set()
        self.root.wait_window(win)
        return outcome["value"]

    def on_write_post(self):
        if self._any_busy():
            return
        if not self.session.is_alive() or not self.session.state.logged_in:
            messagebox.showwarning("글 작성", "먼저 블로그스팟에 로그인해 주세요.")
            return
        blogs = self._checked_blogs()
        if not blogs:
            messagebox.showwarning("글 작성", "글을 쓸 블로그를 체크하거나 목록에서 눌러 주세요.")
            return
        missing_folder = []
        empty_folder = []
        plans = []
        for blog in blogs:
            folder = self._blog_folder_of(blog.id)
            if not folder or not os.path.isdir(folder):
                missing_folder.append(blog.name or blog.id)
                continue
            files = self._manuscript_files(folder)
            if not files:
                empty_folder.append(blog.name or blog.id)
                continue
            plans.append((blog, folder, files))
        if missing_folder:
            names = ", ".join(missing_folder[:4])
            messagebox.showwarning("글 작성", f"블로그를 만들 때 생긴 폴더가 없습니다: {names}")
            return
        if empty_folder:
            names = ", ".join(empty_folder[:4])
            messagebox.showwarning("글 작성", f"폴더에 txt 파일이 없습니다: {names}\n성공 폴더 안의 파일은 다시 쓰지 않습니다.")
            return
        count = self._ask_write_count(plans)
        if count is None:
            return
        if count:
            short = [blog.name or blog.id for blog, _folder, files in plans if len(files) < count]
            if short:
                names = ", ".join(short[:4])
                messagebox.showwarning("글 작성", f"txt가 {count}개보다 적습니다: {names}")
                return
        image_folder = self.post_image_var.get().strip() if hasattr(self, "post_image_var") else ""
        use_images = bool(image_folder and os.path.isdir(image_folder))
        if image_folder and not use_images:
            messagebox.showwarning("글 작성", "이미지 폴더를 찾지 못했습니다. 폴더를 다시 고르거나 비워 두면 원고만 씁니다.")
            return
        if use_images:
            try:
                self._pick_random_image(image_folder)
            except RuntimeError as exc:
                messagebox.showwarning("글 작성", str(exc))
                return
        else:
            image_folder = ""
        jobs = []
        for blog, folder, files in plans:
            chosen = files if not count else files[:count]
            jobs.extend((blog, path, folder) for path in chosen)
        self.log(f"작성할 글 {len(jobs)}개")
        self._post_busy = True
        self._paused = False
        self._run_control.reset()
        self.post_btn.configure(state="disabled")
        self.settings_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, len(jobs), f"작성할 글 {len(jobs)}개")
        threading.Thread(target=self._write_worker, args=(jobs, image_folder), daemon=True).start()

    def _write_worker(self, jobs: list, image_folder: str):
        done = 0
        total = len(jobs)
        try:
            self.session.control = self._run_control
            for index, (blog, path, folder) in enumerate(jobs, start=1):
                self._run_control.checkpoint()
                title = os.path.splitext(os.path.basename(path))[0].strip() or "제목 없음"
                body = self._manuscript_html(self._read_manuscript(path))
                image_path = self._pick_random_image(image_folder) if image_folder else ""
                name = blog.name or blog.id
                self.root.after(0, lambda i=index, t=total, n=name: self._set_progress(i - 1, t, f"글 작성: {n}"))
                image_note = os.path.basename(image_path) if image_path else "없음"
                self.log(f"글 작성 {index}/{total}: [{name}] {title} · 이미지 {image_note}")
                post_url = self.session.publish_manuscript(blog.id, title, body, image_path)
                if not post_url:
                    raise RuntimeError(f"{name}: 게시는 시도했지만 글 주소를 찾지 못했습니다. 원고는 그대로 둡니다.")
                self._append_work_event(blog.id, "글 작성")
                moved = self._move_manuscript_to_success(path, folder)
                done += 1
                self.log(f"작성된 글 주소: {post_url}")
                self.log(f"원고를 성공 폴더로 옮겼습니다: {os.path.basename(moved)}")
                self.root.after(0, lambda: self._apply_state(self.session.state))
                self._append_blog_log(blog.id, "글 1개 추가")
                self.root.after(0, lambda i=index, t=total, n=name: self._set_progress(i, t, f"글 작성 완료: {n}"))
            self.log(f"글 작성 {done}/{total}개를 마쳤습니다.")
        except StopRequested:
            self.log(f"글 작성을 중지했습니다. 완료 {done}/{total}")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"글 작성 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("글 작성", m))
        finally:
            self.root.after(0, self._write_done)
            self._queue_sheet_sync([blog.id for blog, _path, _folder in jobs], "글 작성")

    def _write_done(self):
        self._post_busy = False
        self._paused = False
        self.post_btn.configure(state="normal")
        self.settings_btn.configure(state="normal")
        self._set_naver_buttons(True)
        self._set_run_controls(False)

    def _set_login_button(self, text: str, enabled: bool):
        self.login_btn.configure(text=text, state="normal" if enabled else "disabled")

    def _set_status(self, text: str, color: str):
        try:
            self.status_label.configure(text=text, fg=color)
        except Exception:
            self.status_label.configure(text=text)

    def _start_watch(self):
        if self._watch_id is not None:
            self.root.after_cancel(self._watch_id)
        self._watch()

    def _watch(self):
        if (
            not self._any_busy()
            and not self._watch_detect_running
            and not self._catalog_running
        ):
            self._watch_detect_running = True
            threading.Thread(target=self._watch_detect_worker, daemon=True).start()
        self._watch_id = self.root.after(6000, self._watch)

    def _watch_detect_worker(self):
        try:
            if self._any_busy() or self._catalog_running:
                return
            blogger_up = self.session.driver is not None and self.session.chrome_running()
            if self.session.driver is not None and not blogger_up:
                self.root.after(0, self._on_browser_closed)
                return
            naver_should_probe = self.naver.driver is not None or bool(getattr(self.naver.state, "logged_in", False))
            if naver_should_probe:
                naver_up = self.naver.chrome_running()
                if self.naver.driver is not None and not naver_up:
                    self.root.after(0, self._on_naver_closed)
                elif self.naver.driver is None and naver_up and self.naver.reattach():
                    self.root.after(0, lambda: self._apply_naver_state(self.naver.state))
                elif self.naver.driver is not None and naver_up:
                    naver_url = self.naver._url()
                    if self.naver._on_naver_login_page(naver_url):
                        if not getattr(self, "_naver_signed_out_noted", False):
                            self.naver.state.logged_in = False
                            self.naver.state.account = ""
                            self.naver.state.url = naver_url
                            self.root.after(0, self._on_naver_signed_out)
                    elif self.naver._on_advisor_console():
                        account = self.naver.read_account()
                        shown = getattr(self, "_shown_naver_account", "")
                        if account and account != shown:
                            self._shown_naver_account = account
                            self._naver_signed_out_noted = False
                            self.root.after(0, lambda: self._apply_naver_state(self.naver.state))
            if not blogger_up:
                return
            state = self.session.detect()
            url = state.url or ""
            signed_out = self.session._on_google_login_page(url)
            if signed_out:
                self.session.state = SessionState(url=url, title=state.title)
                if not getattr(self, "_blogger_signed_out_noted", False):
                    self.root.after(0, self._on_blogger_signed_out)
                return
            if not state.logged_in:
                return
            self._blogger_signed_out_noted = False
            account = (state.account or "").strip()
            if account and account != (self._shown_account or ""):
                self.root.after(0, lambda found=state: self._apply_state(found))
            current = [
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    len(blog.posts or []),
                    tuple(sorted(blog.done)),
                )
                for blog in state.blogs
            ]
            if current and current != self._shown_session_keys:
                self._shown_session_keys = current
                self.root.after(0, lambda found=state: self._apply_state(found))
        except Exception:
            pass
        finally:
            self._watch_detect_running = False

    def _on_browser_closed(self):
        self._login_busy = False
        self._settings_busy = False
        self._create_busy = False
        self.session.close()
        self._set_login_button("블로그스팟 로그인", enabled=True)
        self.settings_btn.configure(state="normal")
        if not self._naver_busy:
            self._set_naver_buttons(True)
            self._set_run_controls(False)
        self._apply_state(self.session.state)
        self.log("블로그스팟 창이 닫혔습니다. 다시 로그인하면 Chrome 창이 열립니다.")

    def _on_naver_closed(self):
        self._naver_login_busy = False
        self._naver_busy = False
        self.naver.close()
        self._set_naver_login_button("서치어드바이저 로그인", enabled=True)
        self._set_naver_status("서치어드바이저: 로그인 전", COLORS["text_muted"])
        if not self._settings_busy:
            self._set_naver_buttons(True)
            self.settings_btn.configure(state="normal")
            self._set_run_controls(False)
        self.log("서치어드바이저 창이 닫혔습니다. 다시 로그인하면 창이 열립니다.")

    def _restore_blogger_if_open(self):
        if self._login_busy:
            return
        self._login_busy = True
        self._set_login_button("인식 중...", enabled=False)
        threading.Thread(target=self._blogger_restore_worker, daemon=True).start()

    def _blogger_restore_worker(self):
        try:
            state = self.session.recognize()
            if state.logged_in:
                self._merge_blog_meta(state.blogs)
                self.root.after(0, lambda: self._on_logged_in(state))
                self._catalog_worker()
            elif self.session.chrome_running():
                self.root.after(0, self._on_blogger_signed_out)
            else:
                self._login_busy = False
                self.root.after(0, lambda: self._set_login_button("블로그스팟 로그인", enabled=True))
        except Exception as exc:
            self.log(f"블로그스팟 자동 재연결 실패: {exc}")
            self._login_busy = False
            self.root.after(0, lambda: self._set_login_button("블로그스팟 로그인", enabled=True))

    def _start_code_watch(self):
        if self._code_watch_started or is_frozen():
            return
        self._code_watch_started = True
        self._code_seen = None
        self.log("개발 실행입니다. 코드를 저장하면 이 창은 켜 둔 채로 화면만 다시 그립니다. 로그인도 유지됩니다.")
        self.root.after(1000, self._poll_code_changes)

    def _code_signature(self) -> tuple:
        root = get_app_dir()
        found = []
        try:
            names = os.listdir(root)
        except OSError:
            return tuple()
        for name in names:
            if not name.endswith(".py"):
                continue
            path = os.path.join(root, name)
            try:
                found.append((name, os.path.getmtime(path), os.path.getsize(path)))
            except OSError:
                continue
        return tuple(sorted(found))

    def _poll_code_changes(self):
        try:
            current = self._code_signature()
            seen = getattr(self, "_code_seen", None)
            if seen is None:
                self._code_seen = current
            elif current != seen or self._code_reload_pending:
                stable = getattr(self, "_code_stable", None)
                if stable != current:
                    self._code_stable = current
                elif not self._reloading and not self._any_busy() and not self._catalog_running:
                    self._code_seen = current
                    self._code_reload_pending = False
                    self._code_stable = None
                    self._reload_running_code()
                    if self._code_reload_pending:
                        self._code_seen = seen
        except Exception as exc:
            try:
                self.log(f"코드 감시 오류: {exc}")
            except Exception:
                pass
        if not is_frozen():
            self.root.after(700, self._poll_code_changes)

    def _snapshot_inputs(self) -> dict:
        data = {
            "title": "",
            "body": "",
            "desc": self._current_text("desc", getattr(self, "desc_text", None)),
            "theme": self._selected_html_template(),
            "html_codes": self._export_html_codes(),
            "html_code_index": int(getattr(self, "_html_code_index", 0) or 0),
            "create": self._current_text("create", getattr(self, "create_titles", None)),
            "manuscript": self.manuscript_var.get() if hasattr(self, "manuscript_var") else "",
            "blog_folder": self.blog_folder_var.get() if hasattr(self, "blog_folder_var") else "",
            "post_image": self.post_image_var.get() if hasattr(self, "post_image_var") else "",
            "write_count": self.write_count_var.get() if hasattr(self, "write_count_var") else "1",
            "memo": self.memo_var.get() if hasattr(self, "memo_var") else "",
            "sheet_url": self.sheet_url_var.get() if hasattr(self, "sheet_url_var") else "",
            "log": "",
        }
        box = getattr(self, "log_box", None)
        if box is not None:
            try:
                if ctk:
                    box.configure(state="normal")
                    data["log"] = box.get("1.0", "end-1c")
                    box.configure(state="disabled")
                else:
                    data["log"] = box.get("1.0", "end-1c")
            except Exception:
                pass
        return data

    def _restore_inputs(self, data: dict) -> None:
        if hasattr(self, "title_entry"):
            try:
                self.title_entry.delete(0, "end")
                self.title_entry.insert(0, data.get("title") or "")
            except Exception:
                pass
        if hasattr(self, "body_text"):
            self._textbox_set(self.body_text, data.get("body") or "")
        if hasattr(self, "desc_text"):
            desc = str(data.get("desc") or "") or self._text_cache_get("desc") or self._settings_text("google_descriptions")
            self._textbox_set(self.desc_text, desc)
            self._text_cache_set("desc", self._textbox_get(self.desc_text) or desc)
        if hasattr(self, "theme_html"):
            codes = data.get("html_codes")
            if isinstance(codes, list) and codes:
                self._apply_html_codes(codes, data.get("html_code_index"), fallback_html=str(data.get("theme") or ""))
            elif "theme" in data:
                self._apply_html_codes(None, 0, fallback_html=str(data.get("theme") or ""))
        if hasattr(self, "create_titles"):
            create = str(data.get("create") or "") or self._text_cache_get("create") or self._settings_text("create_titles")
            self._textbox_set(self.create_titles, create)
            self._text_cache_set("create", self._textbox_get(self.create_titles) or create)
        if "manuscript" in data and hasattr(self, "manuscript_var"):
            self.manuscript_var.set(data.get("manuscript") or "")
        if "blog_folder" in data and hasattr(self, "blog_folder_var") and str(data.get("blog_folder") or "").strip():
            self.blog_folder_var.set(str(data.get("blog_folder") or ""))
        if "post_image" in data and hasattr(self, "post_image_var"):
            self.post_image_var.set(data.get("post_image") or "")
        if "write_count" in data and hasattr(self, "write_count_var"):
            self.write_count_var.set(str(data.get("write_count") or "1"))
        if "memo" in data and hasattr(self, "memo_var"):
            self.memo_var.set(str(data.get("memo") or ""))
        if hasattr(self, "sheet_url_var"):
            url = str(data.get("sheet_url") or "").strip()
            if not url:
                url = self._settings_text("sheet_url").strip()
            self.sheet_url_var.set(url or DEFAULT_SHEET_URL)
        text = data.get("log") or ""
        if text and hasattr(self, "log_box"):
            if ctk:
                self.log_box.configure(state="normal")
                self.log_box.insert("end", text + "\n")
                self.log_box.see("end")
                self.log_box.configure(state="disabled")
            else:
                self.log_box.configure(state=tk.NORMAL)
                self.log_box.insert(tk.END, text + "\n")
                self.log_box.see(tk.END)
                self.log_box.configure(state=tk.DISABLED)

    def _release_ctk_traces(self, widget) -> None:
        """CTkEntry(5.2.2)는 destroy 때 textvariable 추적을 지우지 않는다.

        그대로 두면 화면을 다시 만들 때마다 죽은 위젯을 가리키는 추적이 쌓여 메모 칸 입력이 점점 느려진다.
        """
        stack = [widget]
        while stack:
            node = stack.pop()
            var = getattr(node, "_textvariable", None)
            name = getattr(node, "_textvariable_callback_name", "")
            if var not in (None, "") and name and hasattr(var, "trace_remove"):
                try:
                    var.trace_remove("write", name)
                except Exception:
                    pass
                try:
                    node._textvariable_callback_name = ""
                except Exception:
                    pass
            try:
                stack.extend(node.winfo_children())
            except Exception:
                pass

    def _clear_input_traces(self) -> None:
        ids = self.__dict__.setdefault("_var_trace_ids", [])
        for var, cbname in ids:
            try:
                var.trace_remove("write", cbname)
            except Exception:
                pass
        ids.clear()

    def _destroy_ui(self) -> None:
        try:
            self._hover.hide()
        except Exception:
            pass
        try:
            self._close_record_edit(False)
        except Exception:
            pass
        if self._watch_id is not None:
            try:
                self.root.after_cancel(self._watch_id)
            except Exception:
                pass
            self._watch_id = None
        self._cancel_all_afters()
        self._clear_input_traces()
        try:
            self._remove_drag_hook()
        except Exception:
            pass
        try:
            self.root.unbind("<Configure>")
        except Exception:
            pass
        self._close_record_ui()
        self._close_blog_log_win()
        self._cancel_after("blog_rows")
        self._index_row_frames = {}
        self._index_fp = None
        self._record_fp = None
        self._record_tree = None
        self._blog_row_sigs = {}
        self._blog_pending_rows = []
        self._tab_stacked = False
        self._tabs_stacked = False
        self._tab_raise_ready = False
        self._painted_tab = None
        self._pending_select_id = ""
        self._scroll_blog_id = ""
        self._ui_ready = False
        self._resize_frozen = False
        self._root_size = (0, 0)
        self._resize_ignore_until = 0.0
        try:
            set_resize_frozen(False)
        except Exception:
            pass
        for child in list(self.root.winfo_children()):
            self._release_ctk_traces(child)
            try:
                child.destroy()
            except Exception:
                pass
        self._blog_buttons.clear()
        self._blog_row_frames.clear()
        self._blog_filter_btns.clear()
        self._dock_buttons.clear()
        self._blog_index_btns = []
        self._index_labels = []
        self._dashboard_fp = None
        self._dock_width = None
        self._tab_width = None

    def _reload_running_code(self) -> None:
        if self._reloading:
            return
        if self._any_busy() or self._catalog_running:
            self._code_reload_pending = True
            return
        self._reloading = True
        snapshot = {}
        try:
            snapshot = self._snapshot_inputs()
            import importlib

            importlib.invalidate_caches()
            import home_records
            import sheet_sync
            import naver_index_check
            import blogger_session
            import naver_advisor_session
            import paths
            import ui_theme
            import app as app_module

            importlib.reload(paths)
            importlib.reload(ui_theme)
            importlib.reload(home_records)
            importlib.reload(sheet_sync)
            importlib.reload(naver_index_check)
            importlib.reload(blogger_session)
            importlib.reload(naver_advisor_session)
            importlib.reload(app_module)
            self.root.title(f"블로그스팟 글 작성  {paths.APP_VERSION}")
            self.session.__class__ = blogger_session.BloggerSession
            self.naver.__class__ = naver_advisor_session.NaverAdvisorSession
            fresh = app_module.BloggerApp
            for name, attr in fresh.__dict__.items():
                if name.startswith("__"):
                    continue
                setattr(type(self), name, attr)
            self._destroy_ui()
            self._build()
            self._restore_inputs(snapshot)
            self._refresh_dashboard()
            if self.session.state.logged_in or self.session.chrome_running():
                self._set_login_button("다시 인식", enabled=True)
            if self.session.state.logged_in:
                self._apply_state(self.session.state)
                self._start_watch()
            if getattr(self.naver.state, "logged_in", False) or self.naver.chrome_running():
                self._set_naver_login_button("다시 인식", enabled=True)
                self._apply_naver_state(self.naver.state)
            self.log("코드를 반영했습니다. 프로그램과 로그인은 그대로입니다.")
            self._schedule_text_save()
        except Exception as exc:
            self._code_reload_pending = False
            try:
                pages = getattr(self, "_main_pages", {})
                write_ok = self._widget_alive(pages.get("글쓰기")) if hasattr(self, "_widget_alive") else False
                alive = bool(self.root.winfo_children()) and hasattr(self, "_blog_list_inner") and write_ok
                if not alive:
                    self._destroy_ui()
                    self._build()
                    self._restore_inputs(snapshot)
            except Exception:
                pass
            try:
                self.log(f"코드 반영 실패. 창은 유지합니다: {exc}")
            except Exception:
                pass
        finally:
            self._reloading = False

    def _on_close(self):
        try:
            self._save_local_settings()
        except Exception:
            pass
        if self._watch_id is not None:
            try:
                self.root.after_cancel(self._watch_id)
            except Exception:
                pass
        self._cancel_all_afters()
        try:
            self._remove_drag_hook()
        except Exception:
            pass
        self.session.close(kill_chrome=False)
        self.naver.close(kill_chrome=False)
        self.root.destroy()
