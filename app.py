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
from tkinter import filedialog, messagebox, ttk

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
)
from naver_advisor_session import NaverAdvisorSession, OwnershipPending
from naver_index_check import DEFAULT_DELAY_SEC, check_naver_index
from paths import APP_VERSION, data_path, get_app_dir, is_frozen
from sheet_sync import (
    DEFAULT_SHEET_URL,
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
from ui_theme import COLORS, FONTS, HoverPopup, button, card, frame, label, light_scroll, pill, scrollable

try:
    import customtkinter as ctk
except ImportError:
    ctk = None

IMAGE_EXTS = {".ico", ".jpg", ".jpeg", ".gif", ".png", ".bmp", ".tif", ".tiff", ".webp"}
PROGRAM_STATUSES = {"생성만", "설정완료", "수집요청", "재수집요청"}
SETTINGS_DONE_KEYS = {"description", "search_desc", "timezone", "robots", "headers"}
SETTINGS_FILE = "settings.json"
PROGRESS_FILE = "blog_progress.json"
BLOG_META_FILE = "blog_meta.json"
LOG_FILE = "app.log"
_LOG_MAX = 1_500_000
SETUP_KEYS = tuple(key for key, _name in SETTING_ITEMS if key not in {"collect", "collect_post"})
BLOG_FILTERS = (
    ("all", "전체"),
    ("blog_pending", "블로그 미수집"),
    ("post_pending", "글 미수집"),
    ("setup_pending", "설정 미완료"),
)


class BloggerApp:
    def __init__(self, root):
        self.root = root
        self.root.title(f"블로그스팟 글 작성  {APP_VERSION}")
        self.root.geometry("1280x900")
        self.root.minsize(1100, 760)
        if ctk:
            self.root.configure(fg_color=COLORS["bg"])
        else:
            self.root.configure(bg=COLORS["bg"])

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
        self._dash_after = None
        self.blog_var = tk.StringVar(value="")
        self.favicon_var = tk.StringVar(value="")
        self.manuscript_var = tk.StringVar(value="")
        self.post_image_var = tk.StringVar(value="")
        self.blog_folder_var = tk.StringVar(value=os.path.join(get_app_dir(), "블로그"))
        self.write_count_var = tk.StringVar(value="1")
        self.write_count_var.trace_add("write", lambda *_: self._refresh_write_count())
        self._blog_buttons: list = []
        self._blog_check_vars: dict[str, tk.BooleanVar] = {}
        self._blog_row_frames: dict[str, object] = {}
        self._blog_filter_btns: dict[str, object] = {}
        self._shown_blog_keys: list[tuple] = []
        self._shown_session_keys: list[tuple] = []
        self._dashboard_fp = None
        self._refreshing = False
        self._query_after = None
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
        self._text_save_job = None
        self._html_codes: list[dict] = [{"name": "A코드", "html": ""}]
        self._html_code_index = 0
        self.memo_var = tk.StringVar(value="")
        self.sheet_url_var = tk.StringVar(value=DEFAULT_SHEET_URL)
        self._sheet_busy = False
        self._sheet_sync_ids: set[str] = set()
        self._sheet_sync_new: set[str] = set()
        self._sheet_sync_drop: set[str] = set()
        self._sheet_sync_reason = ""
        self._sheet_sync_job = None
        self._sheet_sync_again = False
        self._record_vars: dict[str, dict[str, tk.StringVar]] = {}
        self._record_row_frames: dict[str, object] = {}
        self._records_rendering = False
        self._record_fp: tuple | None = None
        self._meta_save_job = None
        self._memo_parts = ["", "", "", ""]
        self._index_labels: list = []

        self._build()
        self._load_local_settings()
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
            self.write_count_var.trace_add("write", lambda *_: self._refresh_write_count())
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

    def _build(self):
        self._install_centered_dialogs()
        self._ensure_write_folders()
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
        if ctk:
            self.memo_entry = ctk.CTkEntry(
                title_row,
                textvariable=self.memo_var,
                height=34,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="이메일    네이버아이디    비밀번호    이름",
            )
        else:
            self.memo_entry = tk.Entry(title_row, textvariable=self.memo_var, font=FONTS["body"])
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
        self.memo_var.trace_add("write", lambda *_: self._schedule_memo_refresh())
        self.status_label = label(title_wrap, "로그인 전", "body_bold", COLORS["text"])
        self.status_label.pack(anchor="w", pady=(2, 0))
        self.account_label = label(title_wrap, "계정: -", "body", COLORS["text_muted"])
        self.account_label.pack(anchor="w")

        login_wrap = frame(header, COLORS["bg"])
        login_wrap.pack(side=tk.RIGHT, padx=(12, 0))
        self.naver_status_label = label(
            login_wrap, "서치어드바이저: 로그인 전", "small", COLORS["text_muted"]
        )
        self.naver_status_label.pack(anchor="e", pady=(0, 6))
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
        self.action_host.bind("<Configure>", self._layout_dock)
        self.root.after(60, self._layout_dock)
        self._set_run_controls(False)
        self.progress_label = label(dock_inner, "대기 중", "body", COLORS["text_muted"])
        self.progress_label.pack(anchor="w", pady=(8, 4))
        if ctk:
            self.progress_bar = ctk.CTkProgressBar(
                dock_inner,
                height=12,
                progress_color=COLORS["accent"],
                fg_color=COLORS["border"],
            )
            self.progress_bar.set(0)
        else:
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
            ("기록", 90),
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
        self.tab_bar.bind("<Configure>", self._layout_tabs)
        self.root.after(70, self._layout_tabs)

        self.tab_body = frame(shell, COLORS["bg"])
        self.tab_body.pack(fill=tk.BOTH, expand=True)
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
        if ctk:
            self.blog_search = ctk.CTkEntry(
                blog_inner,
                textvariable=self.blog_query,
                height=32,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="블로그 찾기 · 이름, 주소, 코드",
            )
        else:
            self.blog_search = tk.Entry(blog_inner, textvariable=self.blog_query, font=FONTS["body"])
        self.blog_search.pack(fill=tk.X, pady=(8, 0))
        self.blog_query.trace_add("write", self._on_blog_query_changed)

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
        self.blog_delete_btn.pack(side=tk.LEFT)

        self.blog_list = scrollable(blog_inner, height=420, bg=COLORS["card"])
        self.blog_list.pack(fill=tk.BOTH, expand=True)
        for event in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.blog_list.bind(event, lambda _e: self._hover.hide(), add="+")
        host = getattr(self.blog_list, "inner", self.blog_list)
        self._blog_list_inner = frame(host, COLORS["card"])
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
        if ctk:
            self.post_search = ctk.CTkEntry(
                right,
                textvariable=self.post_query,
                height=36,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="이 블로그 글 검색",
            )
        else:
            self.post_search = tk.Entry(right, textvariable=self.post_query, font=FONTS["body"])
        self.post_search.pack(fill=tk.X, pady=(8, 0))
        self.post_query.trace_add("write", self._on_post_query_changed)

        self.posts_list = scrollable(right, height=420, bg=COLORS["card"])
        self.posts_list.pack(fill=tk.BOTH, expand=True, pady=(8, 0))
        posts_host = getattr(self.posts_list, "inner", self.posts_list)
        self.blog_detail_wrap = frame(posts_host, COLORS["card"])
        self.blog_detail_wrap.pack(fill=tk.X)

        setup_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["만들기"] = setup_page
        setup_card = card(setup_page)
        setup_card.pack(fill=tk.BOTH, expand=True)
        setup_scroll = scrollable(setup_card, 420, COLORS["card"])
        setup_scroll.pack(fill=tk.BOTH, expand=True)
        setup_inner = setup_scroll if ctk else setup_scroll.inner
        label(setup_inner, "블로그 생성", "heading", COLORS["text"]).pack(anchor="w", padx=16, pady=(16, 0))
        label(
            setup_inner,
            "블로그를 고르지 않습니다. 제목을 한 줄에 하나씩 적으면 위에서부터 새 블로그를 만듭니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", padx=16, pady=(4, 8))
        if ctk:
            self.create_titles = ctk.CTkTextbox(
                setup_inner, height=140, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
                wrap="word",
            )
        else:
            self.create_titles = tk.Text(setup_inner, height=8, font=FONTS["body"], wrap=tk.WORD)
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
        if ctk:
            self.desc_text = ctk.CTkTextbox(
                setup_inner, height=140, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
                wrap="word",
            )
        else:
            self.desc_text = tk.Text(setup_inner, height=8, font=FONTS["body"], wrap=tk.WORD)
        self.desc_text.pack(fill=tk.X, padx=16)
        self.desc_text.configure(height=140)
        self.create_titles.configure(height=140)
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
        if ctk:
            self.blog_folder_entry = ctk.CTkEntry(
                folder_row, textvariable=self.blog_folder_var, height=40, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            self.blog_folder_entry = tk.Entry(folder_row, textvariable=self.blog_folder_var, font=FONTS["body"])
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
        if ctk:
            self.favicon_entry = ctk.CTkEntry(
                fav_row, textvariable=self.favicon_var, height=40, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            self.favicon_entry = tk.Entry(fav_row, textvariable=self.favicon_var, font=FONTS["body"])
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
            "코드를 여러 개 저장할 수 있습니다. 탭을 더블클릭하면 이름을 바꿀 수 있고, 바꾼 이름은 블로그 기록과 시트에도 반영됩니다. 선택한 코드만 네이버 최초 HTML 코드 넣기에 사용합니다.",
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
        if ctk:
            self.html_code_list = ctk.CTkScrollableFrame(
                code_bar,
                orientation="horizontal",
                height=44,
                fg_color=COLORS["card"],
                corner_radius=0,
                border_width=0,
            )
        else:
            self.html_code_list = frame(code_bar, COLORS["card"])
        self.html_code_list.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        if not isinstance(getattr(self, "_html_codes", None), list) or not self._html_codes:
            self._html_codes = [{"name": "A코드", "html": ""}]
            self._html_code_index = 0
        self._render_html_code_buttons()
        if ctk:
            self.theme_html = ctk.CTkTextbox(
                html_inner, font=FONTS["log"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
                wrap="word",
            )
        else:
            self.theme_html = tk.Text(html_inner, font=FONTS["log"], wrap=tk.WORD)
        self.theme_html.pack(fill=tk.BOTH, expand=True)
        self._load_html_editor()

        log_page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["로그"] = log_page
        log_card = card(log_page)
        log_card.pack(fill=tk.BOTH, expand=True)
        log_inner = frame(log_card, COLORS["card"])
        log_inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        label(log_inner, "로그", "heading", COLORS["text"]).pack(anchor="w", pady=(0, 8))
        if ctk:
            self.log_box = ctk.CTkTextbox(
                log_inner, font=FONTS["log"],
                fg_color=COLORS["log_bg"], text_color=COLORS["log_fg"], wrap="word",
            )
        else:
            self.log_box = tk.Text(
                log_inner, font=FONTS["log"],
                bg=COLORS["log_bg"], fg=COLORS["log_fg"], wrap=tk.WORD,
            )
        self.log_box.pack(fill=tk.BOTH, expand=True)
        if ctk:
            self.log_box.configure(state="disabled")
        else:
            self.log_box.configure(state=tk.DISABLED)
        self._build_records_page()
        self._build_index_page()
        self._show_main_tab("블로그")
        self._fit_window()
        self.root.after(350, self._warm_hidden_lists)
        self.root.bind("<Configure>", self._on_root_configured, add="+")
        self.root.after(200, self._install_drag_hook)

    def _on_root_configured(self, event) -> None:
        if getattr(event, "widget", None) is not self.root:
            return
        pos = (int(getattr(event, "x", 0)), int(getattr(event, "y", 0)))
        prev = getattr(self, "_root_pos", None)
        self._root_pos = pos
        if prev is None or prev == pos:
            return
        hover = getattr(self, "_hover", None)
        if hover is not None:
            hover.suppress(1.2)

    def _install_drag_hook(self) -> None:
        self._remove_drag_hook()

    def _remove_drag_hook(self) -> None:
        old = getattr(self, "_drag_old_proc", None)
        if not getattr(self, "_drag_hooked", False) or not old:
            self._drag_hooked = False
            return
        try:
            import ctypes

            user32 = ctypes.WinDLL("user32", use_last_error=True)
            user32.GetParent.argtypes = [ctypes.c_void_p]
            user32.GetParent.restype = ctypes.c_void_p
            client = int(self.root.winfo_id() or 0)
            frame_hwnd = int(user32.GetParent(client) or 0) or client
            set_long = getattr(user32, "SetWindowLongPtrW", None) or user32.SetWindowLongW
            set_long.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
            set_long.restype = ctypes.c_void_p
            set_long(frame_hwnd, -4, old)
        except Exception:
            pass
        self._drag_hooked = False
        self._drag_proc = None
        self._drag_old_proc = None

    def _layout_dock(self, _event=None) -> None:
        host = getattr(self, "action_host", None)
        if host is None:
            return
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
        host = getattr(self, "tab_bar", None)
        if host is None:
            return
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
        if ctk:
            self.write_count_entry = ctk.CTkEntry(
                count_row,
                textvariable=self.write_count_var,
                width=88,
                height=40,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
            )
        else:
            self.write_count_entry = tk.Entry(count_row, textvariable=self.write_count_var, font=FONTS["body"], width=8)
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
        if ctk:
            self.manuscript_entry = ctk.CTkEntry(
                manuscript_row, textvariable=self.manuscript_var, height=40, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            self.manuscript_entry = tk.Entry(manuscript_row, textvariable=self.manuscript_var, font=FONTS["body"])
        self.manuscript_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.manuscript_folder_btn = button(
            manuscript_row, "폴더 선택", variant="primary", width=120, height=40, command=self.on_pick_manuscript_folder,
        )
        self.manuscript_folder_btn.pack(side=tk.LEFT, padx=(8, 0))
        label(write_inner, "이미지 폴더", "subheading", COLORS["text"]).pack(anchor="w")
        image_row = frame(write_inner, COLORS["card"])
        image_row.pack(fill=tk.X, pady=(4, 0))
        if ctk:
            self.post_image_entry = ctk.CTkEntry(
                image_row, textvariable=self.post_image_var, height=40, font=FONTS["body"],
                fg_color=COLORS["input_bg"], border_color=COLORS["border"], text_color=COLORS["text"],
            )
        else:
            self.post_image_entry = tk.Entry(image_row, textvariable=self.post_image_var, font=FONTS["body"])
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
        if ctk:
            self.index_search = ctk.CTkEntry(
                inner,
                textvariable=self.index_query,
                height=32,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="블로그 찾기 · 이름, 주소, 색인",
            )
        else:
            self.index_search = tk.Entry(inner, textvariable=self.index_query, font=FONTS["body"])
        self.index_search.pack(fill=tk.X, pady=(8, 0))
        self.index_query.trace_add("write", self._on_index_query_changed)
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
        after_id = getattr(self, "_index_query_after", None)
        if after_id is not None:
            try:
                self.root.after_cancel(after_id)
            except Exception:
                pass
        self._index_query_after = self.root.after(120, self._apply_index_visibility)

    def _index_search_text(self, blog: BlogInfo) -> str:
        status, _tone, extra = self._index_status_view(blog)
        return " ".join((blog.name or "", blog.address or "", blog.id or "", status, extra)).casefold()

    def _index_row_matches(self, blog: BlogInfo, query: str) -> bool:
        if not query:
            return True
        text = getattr(blog, "_index_search_text", "") or self._index_search_text(blog)
        return query in text

    def _apply_index_visibility(self) -> None:
        self._index_query_after = None
        rows = getattr(self, "_index_row_frames", None) or {}
        listed = getattr(self, "_listed_index_blogs", None) or []
        if not rows or not listed:
            return
        query = (self.index_query.get() or "").strip().casefold() if hasattr(self, "index_query") else ""
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
        tones = {
            "ok": (COLORS["success"], COLORS["ok_bg"]),
            "wait": ("#b45309", COLORS["wait_bg"]),
            "off": (COLORS["text_muted"], COLORS["chip_bg"]),
        }
        fg, bg = tones.get(tone, tones["off"])
        pill_widget = getattr(row, "_status_pill", None)
        if self._widget_alive(pill_widget):
            try:
                pill_widget.configure(text=status, text_color=fg, fg_color=bg)
            except Exception:
                try:
                    pill_widget.configure(text=status, fg=fg, bg=bg)
                except Exception:
                    pass
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

    def _sync_index_row(self, blog_id: str) -> None:
        blog = next((item for item in self._dashboard_blogs() if item.id == blog_id), None)
        row = (getattr(self, "_index_row_frames", {}) or {}).get(blog_id)
        if blog is None or not self._widget_alive(row):
            self._index_fp = None
            if getattr(self, "_main_tab", "") == "색인 확인":
                self._refresh_index_tab(force=True)
            return
        self._paint_index_status(row, blog)
        blog._index_search_text = self._index_search_text(blog)
        listed = getattr(self, "_listed_index_blogs", None) or []
        self._apply_index_visibility()
        self._update_index_summary(listed)
        self._index_fp = self._index_fingerprint(self._dashboard_blogs())

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
        status_fg, status_bg = {
            "ok": (COLORS["success"], COLORS["ok_bg"]),
            "wait": ("#b45309", COLORS["wait_bg"]),
            "off": (COLORS["text_muted"], COLORS["chip_bg"]),
        }.get(tone, (COLORS["text_muted"], COLORS["chip_bg"]))
        status_pill = tk.Label(
            top, text=status, font=FONTS["small"], fg=status_fg, bg=status_bg, padx=8, pady=2,
        )
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
        self._index_busy = True
        self._index_stop = threading.Event()
        self._set_index_buttons(True)
        scope = "선택한" if selected else ("검색된" if query else "등록된")
        self._set_index_progress(f"{scope} 블로그 {len(ready)}개 확인을 시작합니다.")
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
                elif status.get("indexed") is False:
                    not_indexed += 1
                    self.log(f"미색인: {name}")
                else:
                    failed += 1
                    self.log(f"색인 확인 실패: {name} · {status.get('message') or ''}")
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

    def _build_records_page(self) -> None:
        page = frame(self.tab_body, COLORS["bg"])
        self._main_pages["기록"] = page
        card_wrap = card(page)
        card_wrap.pack(fill=tk.BOTH, expand=True)
        inner = frame(card_wrap, COLORS["card"])
        inner.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
        label(inner, "기록 시트", "heading", COLORS["text"]).pack(anchor="w")
        label(
            inner,
            "블로그마다 한 줄로 정리합니다. 구글 이메일은 로그인한 계정이 들어가고, 제목·주소·글·수집·색인 아이디도 프로그램이 채웁니다. 핵심키워드, 검색결과, 노출, 한줄 메모는 직접 입력합니다.",
            "body",
            COLORS["text_muted"],
            wraplength=980,
            justify="left",
        ).pack(anchor="w", pady=(4, 8))
        if ctk:
            self.sheet_url_entry = ctk.CTkEntry(
                inner,
                textvariable=self.sheet_url_var,
                height=36,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="구글 스프레드시트 주소",
            )
        else:
            self.sheet_url_entry = tk.Entry(inner, textvariable=self.sheet_url_var, font=FONTS["body"])
        self.sheet_url_entry.pack(fill=tk.X)
        actions = frame(inner, COLORS["card"])
        actions.pack(fill=tk.X, pady=(8, 0))
        actions_more = frame(inner, COLORS["card"])
        actions_more.pack(fill=tk.X)
        for host, items in (
            (
                actions,
                (
                    ("이 시트 사용", "primary", 110, self.on_sheet_create),
                    ("주소 저장", "ghost", 90, self.on_sheet_save_url),
                    ("시트 열기", "ghost", 90, self.on_sheet_open),
                    ("가져오기", "ghost", 90, self.on_sheet_pull),
                    ("올리기", "success", 90, self.on_sheet_push),
                ),
            ),
            (
                actions_more,
                (("선택에 메모 이메일", "ghost", 160, self.on_sheet_apply_memo_email),),
            ),
        ):
            for title, variant, width, command in items:
                button(host, title, variant=variant, width=width, height=32, command=command).pack(
                    side=tk.LEFT, padx=(0, 6), pady=(0, 4)
                )
        label(
            inner,
            "상태: " + " · ".join(STATUS_OPTIONS),
            "small",
            COLORS["text_muted"],
            wraplength=980,
            justify="left",
        ).pack(anchor="w", pady=(4, 6))
        self.records_list = light_scroll(inner, height=420, bg=COLORS["card"])
        self.records_list.pack(fill=tk.BOTH, expand=True)
        host = getattr(self.records_list, "inner", self.records_list)
        self._record_list_inner = tk.Frame(host, bg=COLORS["card"])
        self._record_list_inner.pack(fill=tk.X)

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
        job = getattr(self, "_meta_save_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        try:
            self._meta_save_job = self.root.after(400, self._save_blog_meta)
        except Exception:
            self._meta_save_job = None

    def _set_record_field(self, blog_id: str, key: str, value: str) -> None:
        if not blog_id or key not in RECORD_FIELDS:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        value = (value or "").strip()
        old = str(cur.get(key) or "").strip()
        if old == value:
            return
        if key == "sheet_status":
            cur["prev_status"] = old
            if value:
                now = datetime.now()
                stamp = f"{now.month}/{now.day}"
                piece = f"{stamp} {value}"
                flow = self._clean_status_flow(str(cur.get("status_flow") or ""))
                if not flow.endswith(piece):
                    cur["status_flow"] = f"{flow} → {piece}" if flow else piece
                else:
                    cur["status_flow"] = flow
                cur["last_check"] = stamp
        cur[key] = value
        self._schedule_meta_save()
        self._schedule_sheet_sync([blog_id], "기록 수정")

    def _flush_record_vars(self) -> None:
        if getattr(self, "_records_rendering", False):
            return
        for blog_id, fields in list(getattr(self, "_record_vars", {}).items()):
            for key, var in fields.items():
                try:
                    value = var.get()
                except Exception:
                    continue
                if key == "sheet_status" and value.strip() == "미정":
                    value = ""
                self._set_record_field(blog_id, key, value)

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
        if collected and count < 1:
            count = 1
        if count > 1:
            return "재수집요청"
        if collected:
            return "수집요청"
        if SETTINGS_DONE_KEYS <= done:
            return "설정완료"
        return "생성만"

    def _fill_program_records(self, blogs: list[BlogInfo] | None = None) -> bool:
        email = self._logged_google_email()
        targets = list(blogs) if blogs is not None else self._dashboard_blogs()
        changed = False
        for blog in targets:
            cur = self._blog_meta.setdefault(blog.id, {})
            if email and not str(cur.get("google_email") or "").strip():
                cur["google_email"] = email
                changed = True
            flow = str(cur.get("status_flow") or "").strip()
            cleaned = self._clean_status_flow(flow)
            if cleaned != flow:
                cur["status_flow"] = cleaned
                changed = True
            done = set(getattr(blog, "done", set()) or set())
            done.update(self._progress_map.get(blog.id) or [])
            if SETTINGS_DONE_KEYS <= done:
                now = datetime.now()
                piece = f"{now.month}/{now.day} 설정완료"
                flow = self._clean_status_flow(str(cur.get("status_flow") or ""))
                if piece not in [part.strip() for part in flow.split("→")]:
                    cur["status_flow"] = f"{flow} → {piece}" if flow else piece
                    cur["last_check"] = f"{now.month}/{now.day}"
                    changed = True
            status = str(cur.get("sheet_status") or "").strip()
            if status in PROGRAM_STATUSES or not status:
                derived = self._program_sheet_status(blog)
                if derived and derived != status:
                    if status:
                        cur["prev_status"] = status
                    now = datetime.now()
                    stamp = f"{now.month}/{now.day}"
                    piece = f"{stamp} {derived}"
                    flow = self._clean_status_flow(str(cur.get("status_flow") or ""))
                    if flow.endswith(piece):
                        cur["status_flow"] = flow
                    else:
                        cur["status_flow"] = f"{flow} → {piece}" if flow else piece
                    cur["last_check"] = stamp
                    cur["sheet_status"] = derived
                    changed = True
        if changed:
            self._schedule_meta_save()
        return changed

    def _sync_program_record_vars(self, blogs: list[BlogInfo]) -> None:
        self._records_rendering = True
        try:
            for blog in blogs:
                fields = (getattr(self, "_record_vars", {}) or {}).get(blog.id) or {}
                meta = self._blog_meta.get(blog.id) or {}
                email = fields.get("google_email")
                stored_email = str(meta.get("google_email") or "").strip()
                if email is not None and stored_email and not email.get().strip():
                    email.set(stored_email)
                status = fields.get("sheet_status")
                stored_status = str(meta.get("sheet_status") or "").strip()
                if status is None or not stored_status:
                    continue
                shown = status.get().strip()
                if shown in {"", "미정"} or shown in PROGRAM_STATUSES:
                    if shown != stored_status:
                        status.set(stored_status)
        finally:
            self._records_rendering = False

    def _sheet_record_dicts(self, only_ids: set[str] | None = None) -> list[dict]:
        blogs = self._dashboard_blogs()
        targets = blogs if only_ids is None else [blog for blog in blogs if blog.id in only_ids]
        self._fill_program_records(targets)
        records = []
        for blog in blogs:
            if only_ids is not None and blog.id not in only_ids:
                continue
            meta = self._blog_meta.get(blog.id) or {}
            urls = [str(post.get("url") or "").strip() for post in (blog.posts or []) if str(post.get("url") or "").strip()]
            done = set(getattr(blog, "done", set()) or set())
            done.update(self._progress_map.get(blog.id) or [])
            collect_count = self._count_value(meta.get("blog_crawl_count"))
            if collect_count < 1 and ("collect" in done or str(meta.get("last_blog_crawl") or "").strip()):
                collect_count = 1
            records.append(
                {
                    "id": blog.id,
                    "keyword": meta.get("keyword") or "",
                    "google_email": str(meta.get("google_email") or "").strip() or self._logged_google_email(),
                    "title": blog.name or "",
                    "address": blog.address or "",
                    "posts": " · ".join(urls),
                    "html_code": meta.get("html_code") or "",
                    "naver_id": meta.get("naver_id") or "",
                    "index_status": index_status_label(
                        meta.get("naver_indexed") if isinstance(meta.get("naver_indexed"), bool) else None,
                        str(meta.get("naver_index_checked_at") or ""),
                        blog.address or "",
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
                    "last_post_collect": self._sheet_day(str(meta.get("last_post_crawl") or "")),
                    "first_index_at": meta.get("first_index_at") or "",
                    "trim_started_at": meta.get("trim_started_at") or "",
                    "status_flow": meta.get("status_flow") or "",
                    "prev_status": meta.get("prev_status") or "",
                    "folder": meta.get("folder") or "",
                }
            )
        return records

    def _render_record_rows(self, force: bool = False) -> None:
        parent = getattr(self, "_record_list_inner", None)
        if parent is None or not self._widget_alive(parent):
            return
        if not force and getattr(self, "_main_tab", "") != "기록":
            return
        blogs = self._dashboard_blogs()
        self._fill_program_records(blogs)
        fp = tuple(
            (
                blog.id,
                str((self._blog_meta.get(blog.id) or {}).get("google_email") or "").strip() or self._logged_google_email(),
            )
            for blog in blogs
        )
        if fp == getattr(self, "_record_fp", None) and parent.winfo_children():
            self._record_dirty = False
            self._sync_program_record_vars(blogs)
            self._paint_record_rows()
            return
        self._flush_record_vars()
        self._records_rendering = True
        try:
            for child in list(parent.winfo_children()):
                child.destroy()
            self._record_vars = {}
            self._record_row_frames = {}
            self._record_fp = fp
            self._record_dirty = False
            if not blogs:
                label(parent, "로그인하면 블로그 기록이 여기에 나타납니다.", "body", COLORS["text_muted"]).pack(anchor="w", pady=8)
                return
            grouped: dict[str, list[BlogInfo]] = {}
            order: list[str] = []
            for blog in blogs:
                email = str((self._blog_meta.get(blog.id) or {}).get("google_email") or "").strip() or self._logged_google_email() or "이메일 없음"
                if email not in grouped:
                    grouped[email] = []
                    order.append(email)
                grouped[email].append(blog)
            palettes = ("#eef2ff", "#ecfdf5", "#fff7ed", "#f0f9ff", "#fdf4ff")
            for index, email in enumerate(order):
                items = grouped[email]
                group_bg = palettes[index % len(palettes)]
                wrap = tk.Frame(parent, bg=group_bg, highlightbackground=COLORS["card_border"], highlightthickness=1)
                wrap.pack(fill=tk.X, pady=(0, 10))
                head = tk.Frame(wrap, bg=group_bg)
                head.pack(fill=tk.X, padx=8, pady=(8, 4))
                tk.Label(
                    head,
                    text=email,
                    font=FONTS["body_bold"],
                    fg=COLORS["text"],
                    bg=group_bg,
                ).pack(side=tk.LEFT)
                tk.Label(
                    head,
                    text=f"{len(items)}개",
                    font=FONTS["small"],
                    fg=COLORS["text_muted"],
                    bg=group_bg,
                ).pack(side=tk.LEFT, padx=(8, 0))
                for blog in items:
                    self._render_record_row(wrap, blog, group_bg)
        finally:
            self._records_rendering = False
            self._paint_record_rows()

    def _paint_record_rows(self) -> None:
        selected = (self.blog_var.get() or "").strip() if hasattr(self, "blog_var") else ""
        checked = set()
        for blog_id, var in (getattr(self, "_blog_check_vars", {}) or {}).items():
            try:
                if var.get():
                    checked.add(blog_id)
            except Exception:
                pass
        for blog_id, row in list((getattr(self, "_record_row_frames", {}) or {}).items()):
            if not self._widget_alive(row):
                continue
            mark = getattr(row, "_record_mark", None)
            if blog_id == selected:
                bg, border, thick = "#c7d2fe", "#312e81", 4
                cell_bg = "#e0e7ff"
            elif blog_id in checked:
                bg, border, thick = COLORS["row_checked"], COLORS["row_checked_border"], 2
                cell_bg = "#dbeafe"
            else:
                bg = getattr(row, "_record_group_bg", COLORS["input_bg"])
                border, thick, cell_bg = COLORS["border"], 1, COLORS["input_bg"]
            try:
                row.configure(bg=bg, highlightbackground=border, highlightcolor=border, highlightthickness=thick)
            except Exception:
                pass
            bar = getattr(row, "_record_bar", None)
            if self._widget_alive(bar):
                try:
                    bar.configure(bg=border if blog_id == selected else bg)
                except Exception:
                    pass
            body = getattr(row, "_record_body", None)
            if self._widget_alive(body):
                self._set_record_bg(body, bg, cell_bg)
            if self._widget_alive(mark):
                if blog_id == selected:
                    try:
                        mark.pack(side=tk.RIGHT)
                        mark.configure(text="선택됨")
                    except Exception:
                        pass
                else:
                    try:
                        mark.pack_forget()
                    except Exception:
                        pass

    def _set_record_bg(self, widget, bg: str, cell_bg: str | None = None) -> None:
        kind = widget.winfo_class()
        try:
            if kind in {"Entry"}:
                widget.configure(bg=cell_bg or bg, highlightbackground=COLORS["accent"] if cell_bg == "#e0e7ff" else COLORS["border"])
            elif kind == "TCombobox":
                pass
            else:
                widget.configure(bg=bg)
        except Exception:
            if kind not in {"Entry", "TCombobox"}:
                return
        for child in widget.winfo_children():
            self._set_record_bg(child, bg, cell_bg)

    def _select_record_row(self, blog_id: str) -> None:
        if not blog_id:
            return
        self._select_blog(blog_id)

    def _bind_record_select(self, widget, blog_id: str) -> None:
        def on_pick(_event=None, bid=blog_id):
            self._select_record_row(bid)

        try:
            widget.bind("<Button-1>", on_pick, add="+")
            widget.bind("<FocusIn>", on_pick, add="+")
        except Exception:
            pass
        for child in widget.winfo_children():
            self._bind_record_select(child, blog_id)

    def _record_entry(self, parent, variable, width: int, placeholder: str):
        box = tk.Frame(parent, bg=COLORS["input_bg"])
        tk.Label(
            box, text=placeholder, font=FONTS["caption"], fg=COLORS["text_muted"], bg=COLORS["input_bg"],
        ).pack(anchor="w")
        tk.Entry(
            box,
            textvariable=variable,
            font=FONTS["small"],
            width=max(10, width // 9),
            bg=COLORS["input_bg"],
            fg=COLORS["text"],
            relief="flat",
            highlightthickness=1,
            highlightbackground=COLORS["border"],
            highlightcolor=COLORS["accent"],
        ).pack(anchor="w", pady=(2, 0))
        return box

    def _render_record_row(self, parent, blog: BlogInfo, group_bg: str | None = None) -> None:
        meta = self._blog_meta.get(blog.id) or {}
        bg = group_bg or COLORS["input_bg"]
        row = tk.Frame(parent, bg=bg, highlightbackground=COLORS["border"], highlightthickness=1)
        row.pack(fill=tk.X, padx=8, pady=3)
        row._record_group_bg = bg
        bar = tk.Frame(row, bg=bg, width=8)
        bar.pack(side=tk.LEFT, fill=tk.Y)
        bar.pack_propagate(False)
        row._record_bar = bar
        body = tk.Frame(row, bg=bg)
        body.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(4, 8), pady=6)
        row._record_body = body
        self._record_row_frames[blog.id] = row
        title_line = tk.Frame(body, bg=bg)
        title_line.pack(fill=tk.X)
        tk.Label(
            title_line, text=blog.name or blog.address or blog.id, font=FONTS["body_bold"],
            fg=COLORS["text"], bg=bg,
        ).pack(side=tk.LEFT)
        mark = tk.Label(
            title_line, text="선택됨", font=FONTS["caption"],
            fg="#ffffff", bg="#312e81", padx=8, pady=1,
        )
        row._record_mark = mark
        tk.Label(
            body, text=blog.address or "주소 없음", font=FONTS["small"],
            fg=COLORS["text_muted"], bg=bg,
        ).pack(anchor="w")
        auto_bits = []
        indexed = str(meta.get("naver_id") or "").strip()
        if indexed:
            auto_bits.append(f"색인 {indexed}")
        collected = self._sheet_day(str(meta.get("last_blog_crawl") or meta.get("blog_collect_at") or ""))
        if collected:
            auto_bits.append(f"수집 {collected}")
        posted = self._sheet_day(str(meta.get("last_post_crawl") or ""))
        if posted:
            auto_bits.append(f"글수집 {posted}")
        code_name = str(meta.get("html_code") or "").strip()
        if code_name:
            auto_bits.append(f"HTML {code_name}")
        if auto_bits:
            tk.Label(
                body, text=" · ".join(auto_bits), font=FONTS["small"],
                fg=COLORS["text_muted"], bg=bg,
            ).pack(anchor="w")
        fields: dict[str, tk.StringVar] = {}

        def bind(key: str, initial: str):
            shown = initial
            if key == "sheet_status":
                shown = initial or "미정"
            var = tk.StringVar(value=shown)
            var.trace_add(
                "write",
                lambda *_args, bid=blog.id, field=key, target=var: self._on_record_var(bid, field, target),
            )
            fields[key] = var
            return var

        line1 = tk.Frame(body, bg=bg)
        line1.pack(fill=tk.X, pady=(6, 0))
        keyword = bind("keyword", str(meta.get("keyword") or ""))
        email = bind("google_email", str(meta.get("google_email") or "").strip() or self._logged_google_email())
        status = bind("sheet_status", str(meta.get("sheet_status") or ""))
        self._record_entry(line1, keyword, 160, "핵심키워드").pack(side=tk.LEFT, padx=(0, 6))
        values = ["미정", *STATUS_OPTIONS]
        current = status.get()
        if current not in values:
            values.append(current)
        status_box = tk.Frame(line1, bg=bg)
        status_box.pack(side=tk.LEFT, padx=(0, 6))
        tk.Label(
            status_box, text="상태", font=FONTS["caption"], fg=COLORS["text_muted"], bg=bg,
        ).pack(anchor="w")
        menu = ttk.Combobox(status_box, textvariable=status, values=values, width=14, state="readonly")
        menu.pack(anchor="w", pady=(2, 0))
        self._record_entry(line1, email, 220, "구글 이메일").pack(side=tk.LEFT)
        line2 = tk.Frame(body, bg=bg)
        line2.pack(fill=tk.X, pady=(4, 0))
        note = bind("sheet_note", str(meta.get("sheet_note") or ""))
        search = bind("search_result", str(meta.get("search_result") or ""))
        work = bind("work", str(meta.get("work") or ""))
        exposed = bind("exposed_keyword", str(meta.get("exposed_keyword") or ""))
        self._record_entry(line2, note, 220, "한줄 메모").pack(side=tk.LEFT, padx=(0, 6))
        self._record_entry(line2, search, 140, "검색결과").pack(side=tk.LEFT, padx=(0, 6))
        self._record_entry(line2, work, 120, "현재작업").pack(side=tk.LEFT, padx=(0, 6))
        self._record_entry(line2, exposed, 140, "노출키워드").pack(side=tk.LEFT)
        self._record_vars[blog.id] = fields
        self._bind_record_select(row, blog.id)

    def _on_record_var(self, blog_id: str, key: str, var: tk.StringVar) -> None:
        if getattr(self, "_records_rendering", False):
            return
        value = var.get()
        if key == "sheet_status" and value.strip() == "미정":
            value = ""
        self._set_record_field(blog_id, key, value)

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
        self._records_rendering = True
        try:
            for blog in blogs:
                cur = self._blog_meta.setdefault(blog.id, {})
                cur["google_email"] = email
                var = (self._record_vars.get(blog.id) or {}).get("google_email")
                if var is not None:
                    var.set(email)
        finally:
            self._records_rendering = False
        self._schedule_meta_save()
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
        self._flush_record_vars()
        records = [program_row(item) for item in self._sheet_record_dicts()]
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

    def _schedule_sheet_sync(
        self,
        blog_ids,
        reason: str = "",
        *,
        new_ids=None,
        drop: bool = False,
    ) -> None:
        ids = [str(item).strip() for item in blog_ids if str(item).strip()]
        fresh = [str(item).strip() for item in (new_ids or []) if str(item).strip()]
        if not ids and not fresh:
            return
        if drop:
            self._sheet_sync_drop.update(ids)
            self._sheet_sync_ids.difference_update(ids)
            self._sheet_sync_new.difference_update(ids)
        else:
            self._sheet_sync_ids.update(ids)
            self._sheet_sync_new.update(fresh)
        if reason:
            self._sheet_sync_reason = reason
        job = getattr(self, "_sheet_sync_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        try:
            self._sheet_sync_job = self.root.after(1600, self._flush_sheet_sync)
        except Exception:
            self._sheet_sync_job = None

    def _queue_sheet_sync(self, blog_ids, reason: str, *, new_ids=None, drop: bool = False) -> None:
        ids = [str(item).strip() for item in blog_ids if str(item).strip()]
        fresh = [str(item).strip() for item in (new_ids or []) if str(item).strip()]
        self.root.after(
            0,
            lambda: self._schedule_sheet_sync(ids, reason, new_ids=fresh, drop=drop),
        )

    def _flush_sheet_sync(self) -> None:
        self._sheet_sync_job = None
        if self._sheet_busy:
            self._sheet_sync_again = True
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
        self._flush_record_vars()
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
            self._records_rendering = True
            try:
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
                    vars_for_blog = self._record_vars.get(blog.id) or {}
                    for key, var in vars_for_blog.items():
                        value = str(cur.get(key) or "")
                        if key == "sheet_status":
                            value = value or "미정"
                        var.set(value)
                    applied += 1
            finally:
                self._records_rendering = False
            self._save_blog_meta()
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
        self._ensure_tabs_stacked()
        self._place_main_page(page)
        if (
            name == getattr(self, "_main_tab", "")
            and getattr(page, "_tab_placed", False)
            and getattr(self, "_tab_raise_ready", False)
        ):
            return
        self._main_tab = name
        try:
            page.tkraise()
        except Exception:
            try:
                page.lift()
            except Exception:
                pass
        self._tab_raise_ready = True
        if getattr(self, "_tab_paint_job", None) is None:
            self._tab_paint_job = self.root.after(1, self._paint_tab_buttons_later)
        if self._tab_needs_refresh(name):
            self._schedule_tab_refresh(name)

    def _ensure_tabs_stacked(self) -> None:
        if getattr(self, "_tabs_stacked", False):
            return
        try:
            self.tab_body.grid_rowconfigure(0, weight=1)
            self.tab_body.grid_columnconfigure(0, weight=1)
        except Exception:
            pass
        for item in list(self._main_pages.values()):
            self._place_main_page(item)
        self._tabs_stacked = True

    def _paint_tab_buttons_later(self) -> None:
        self._tab_paint_job = None
        self._paint_main_tabs()

    def _tab_needs_refresh(self, name: str) -> bool:
        if name == "글쓰기":
            return True
        if name == "블로그":
            return bool(
                getattr(self, "_blog_dirty", False)
                or getattr(self, "_detail_dirty", False)
                or getattr(self, "_stale_blog_rows", None)
            )
        if name in ("기록", "색인 확인"):
            return False
        return False

    def _queue_side_lists(self) -> None:
        job = getattr(self, "_side_list_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        self._side_list_job = self.root.after(40, self._refresh_side_lists)

    def _refresh_side_lists(self) -> None:
        self._side_list_job = None
        tab = getattr(self, "_main_tab", "")
        if tab != "기록":
            self._render_record_rows(force=True)
        if tab != "색인 확인":
            self._refresh_index_tab(force=True)

    def _warm_hidden_lists(self) -> None:
        if getattr(self, "_record_fp", None) is None:
            self._render_record_rows(force=True)
        if getattr(self, "_index_fp", None) is None:
            self._refresh_index_tab(force=True)

    def _place_main_page(self, page) -> None:
        if not self._widget_alive(page) or getattr(page, "_tab_placed", False):
            return
        try:
            page.pack_forget()
        except Exception:
            pass
        try:
            page.grid(row=0, column=0, sticky="nsew")
        except Exception:
            return
        page._tab_placed = True

    def _schedule_tab_refresh(self, name: str) -> None:
        job = getattr(self, "_tab_refresh_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        self._tab_refresh_job = self.root.after(16, lambda tab=name: self._refresh_visible_tab(tab))

    def _refresh_visible_tab(self, name: str) -> None:
        self._tab_refresh_job = None
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
        job = getattr(self, "_text_save_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        try:
            self._text_save_job = self.root.after(700, self._save_local_settings)
        except Exception:
            self._text_save_job = None

    def _load_local_settings(self) -> None:
        self._load_progress()
        self._load_blog_meta()
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
                    **{key: str(item.get(key) or "") for key in RECORD_FIELDS},
                }
            self._fill_missing_post_crawls()
        except Exception:
            self._blog_meta = {}

    def _save_blog_meta(self) -> None:
        path = data_path(BLOG_META_FILE)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self._blog_meta, handle, ensure_ascii=False, indent=2)

    def _remember_blog_meta(self, blogs: list[BlogInfo]) -> None:
        changed = False
        for blog in blogs:
            cur = self._blog_meta.setdefault(blog.id, {})
            if blog.name and cur.get("name") != blog.name:
                cur["name"] = blog.name
                changed = True
            if blog.address and cur.get("address") != blog.address:
                cur["address"] = blog.address
                changed = True
            posts = normalize_posts(blog.posts)
            if posts and cur.get("posts") != posts:
                cur["posts"] = posts
                changed = True
            if cur.pop("post_url", None) is not None or cur.pop("post_title", None) is not None:
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
            saved = normalize_posts(meta.get("posts") or [])
            if not saved:
                saved = normalize_posts(
                    [{"url": meta.get("post_url"), "title": meta.get("post_title")}]
                )
            if saved and not blog.posts:
                blog.posts = saved
            elif saved and blog.posts:
                blog.posts = normalize_posts([*blog.posts, *saved])

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
        host = host.split("/")[0].strip()
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
            if address and not str(cur.get("address") or "").strip():
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
        self._refresh_dashboard()

    def _blog_folder_of(self, blog_id: str) -> str:
        meta = (self._blog_meta or {}).get(blog_id) or {}
        return str(meta.get("folder") or "").strip()

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
        job = getattr(self, "_memo_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        self._memo_job = self.root.after(180, self._apply_memo_parts)

    def _apply_memo_parts(self) -> None:
        self._memo_job = None
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
            try:
                widget.configure(text=caption, text_color=COLORS["success"] if indexed else COLORS["text_muted"])
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
            self._merge_blog_meta(self.session.state.blogs)
            self.session.detect()
            self._merge_blog_meta(self.session.state.blogs)
            self.root.after(0, lambda: self._apply_state(self.session.state))
            self.log("블로그 목록을 다시 읽고 주소·글을 인식합니다.")
            self._catalog_worker()
        except Exception as exc:
            self.log(f"블로그 다시 인식 오류: {exc}")

    def _catalog_abort(self) -> bool:
        return self._create_busy or self._settings_busy or self._post_busy or self._naver_busy

    def _catalog_worker(self):
        self._catalog_running = True
        try:
            self.session.refresh_blog_details(should_abort=self._catalog_abort)
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
        self._fill_program_records(state.blogs)
        self._schedule_dashboard()

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
        if self._dash_after is not None:
            try:
                self.root.after_cancel(self._dash_after)
            except Exception:
                pass
        self._dash_after = self.root.after(80, self._flush_dashboard)

    def _flush_dashboard(self) -> None:
        self._dash_after = None
        self._refresh_dashboard()

    def _merge_progress(self, blogs: list[BlogInfo]) -> None:
        for blog in blogs:
            blog.done.update(self._progress_map.get(blog.id, []))

    def _configure_blog_columns(self, widget) -> None:
        for index, (_title, minsize, weight) in enumerate(self._blog_col_headers):
            widget.grid_columnconfigure(index, minsize=minsize, weight=weight)

    def _on_post_query_changed(self, *_args) -> None:
        after_id = getattr(self, "_post_query_after", None)
        if after_id is not None:
            try:
                self.root.after_cancel(after_id)
            except Exception:
                pass
        self._post_query_after = self.root.after(180, self._render_blog_detail)

    def _on_blog_query_changed(self, *_args) -> None:
        if self._query_after is not None:
            try:
                self.root.after_cancel(self._query_after)
            except Exception:
                pass
        self._query_after = self.root.after(30, self._apply_blog_visibility)

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
        blogs: list[BlogInfo] = []
        for blog in self.session.state.blogs:
            meta = self._blog_meta.get(blog.id) or {}
            if not blog.name:
                blog.name = str(meta.get("name") or blog.address or blog.id[-6:])
            if not (blog.address or "").strip():
                blog.address = str(meta.get("address") or "")
            blog.done.update(self._progress_map.get(blog.id, []))
            if not blog.posts:
                blog.posts = normalize_posts(meta.get("posts") or [])
            else:
                blog.posts = normalize_posts(blog.posts)
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
        query = (self.blog_query.get() or "").strip().lower()
        out = []
        for blog in blogs:
            hay = " ".join(
                [
                    blog.name,
                    blog.address,
                    blog.id,
                    self._naver_id_of(blog.id),
                    self._html_code_of(blog.id),
                ]
            ).lower()
            if query and query not in hay:
                continue
            setup_pending = any(key not in blog.done for key in SETUP_KEYS)
            if self._blog_filter == "blog_pending" and "collect" in blog.done:
                continue
            if self._blog_filter == "post_pending" and "collect_post" in blog.done:
                continue
            if self._blog_filter == "setup_pending" and not setup_pending:
                continue
            out.append(blog)
        return out

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
            tuple(
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    tuple(str(item.get("url") or "") for item in blog.posts),
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
        self._fill_missing_post_crawls()
        blogs = self._dashboard_blogs()
        visible = self._filter_blogs(blogs)
        fp = self._dashboard_fingerprint(blogs, visible)
        if fp == self._dashboard_fp:
            if getattr(self, "_main_tab", "") == "색인 확인":
                self._refresh_index_tab()
            return
        tab = getattr(self, "_main_tab", "")
        self._blog_dirty = tab != "블로그"
        self._record_dirty = tab != "기록"
        self._index_dirty = tab != "색인 확인"
        self._queue_side_lists()
        if tab == "기록":
            self._render_record_rows()
            return
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
            self._refresh_index_tab()
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

    def _render_blogs(self, blogs: list[BlogInfo], all_blogs: list[BlogInfo] | None = None):
        self._hover.hide()
        parent = self._blog_list_inner
        for child in parent.winfo_children():
            child.destroy()
        self._blog_buttons.clear()
        self._blog_row_frames.clear()
        self._stale_blog_rows = set()
        self._index_labels = []
        source = all_blogs if all_blogs is not None else blogs
        self._shown_blog_keys = [
            (
                blog.id,
                blog.address,
                tuple(str(item.get("url") or "") for item in blog.posts),
                tuple(sorted(blog.done)),
                self._last_recrawl(blog.id),
            )
            for blog in source
        ]
        live_ids = {blog.id for blog in source}
        for blog_id in list(self._blog_check_vars):
            if blog_id not in live_ids:
                self._blog_check_vars.pop(blog_id, None)
        account_line = self._blog_heading_text(len(source))
        self.blog_heading.configure(text=account_line)
        if not blogs:
            self._listed_blogs = []
            self._vis_key = None
            empty = (
                "조건에 맞는 블로그가 없습니다."
                if source
                else "로그인한 계정의 블로그만 표시됩니다."
            )
            self.blog_empty = label(parent, empty, "body", COLORS["text_muted"])
            self.blog_empty.pack(anchor="w", pady=8)
            if not source:
                self.blog_var.set("")
            self._render_blog_detail()
            self._render_record_rows()
            return

        known = {blog.id for blog in source}
        if source and self.blog_var.get() not in known:
            selected = next((blog.id for blog in source if blog.selected), source[0].id)
            self.blog_var.set(selected)

        self._listed_blogs = list(source)
        self._vis_key = None
        for blog in source:
            blog._search_text = self._blog_search_text(blog)
            self._render_blog_row(parent, blog)
        self._update_sel_count()
        self._render_blog_detail()
        self._apply_blog_visibility()
        self._render_record_rows()
        if getattr(self, "_scroll_blog_id", ""):
            self._scroll_blog_id = ""
            self.root.after(80, self._scroll_blog_list_to_end)

    def _blog_search_text(self, blog: BlogInfo) -> str:
        return " ".join(
            (
                blog.name or "",
                blog.address or "",
                blog.id or "",
                self._naver_id_of(blog.id),
                self._html_code_of(blog.id),
            )
        ).casefold()

    def _blog_row_matches(self, blog: BlogInfo, query: str) -> bool:
        if query and query not in getattr(blog, "_search_text", ""):
            return False
        if self._blog_filter == "blog_pending" and "collect" in blog.done:
            return False
        if self._blog_filter == "post_pending" and "collect_post" in blog.done:
            return False
        if self._blog_filter == "setup_pending" and not any(key not in blog.done for key in SETUP_KEYS):
            return False
        return True

    def _apply_blog_visibility(self) -> None:
        self._query_after = None
        rows = getattr(self, "_blog_row_frames", None)
        listed = getattr(self, "_listed_blogs", None)
        if not rows or not listed:
            return
        query = (self.blog_query.get() or "").strip().casefold()
        key = (query, self._blog_filter)
        if key == getattr(self, "_vis_key", None):
            return
        self._vis_key = key
        shown = 0
        for blog in listed:
            blog._search_text = getattr(blog, "_search_text", None) or self._blog_search_text(blog)
            row = rows.get(blog.id)
            if row is None:
                continue
            if self._blog_row_matches(blog, query):
                row.pack(fill=tk.X, pady=4, padx=2)
                shown += 1
            else:
                row.pack_forget()
        empty = getattr(self, "_blog_filter_empty", None)
        if shown:
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
        if getattr(self, "_main_tab", "") == "블로그":
            self._render_blog_detail()
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
        self._paint_record_rows()
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

    def _bind_row_focus(self, widget, blog_id: str) -> None:
        widget.bind("<Button-1>", lambda e, bid=blog_id: self._on_row_click(e, bid))
        widget.bind("<Double-Button-1>", lambda _e, bid=blog_id: self._open_blog_address(bid))
        try:
            widget.configure(cursor="hand2")
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
        self.session.state.blogs = [blog for blog in self.session.state.blogs if blog.id != blog_id]
        self._blog_meta.pop(blog_id, None)
        self._progress_map.pop(blog_id, None)
        self._blog_check_vars.pop(blog_id, None)
        if self.blog_var.get() == blog_id:
            self.blog_var.set("")
        try:
            self._save_blog_meta()
            self._save_progress()
        except Exception:
            pass
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

    def _render_blog_row(self, parent, blog: BlogInfo) -> None:
        bg, border, width = self._row_look(blog.id)
        if ctk:
            row = ctk.CTkFrame(
                parent, fg_color=bg, corner_radius=10,
                border_width=width, border_color=border,
            )
        else:
            row = tk.Frame(parent, bg=bg, highlightbackground=border, highlightthickness=width)
        row.pack(fill=tk.X, pady=4, padx=2)
        self._blog_row_frames[blog.id] = row
        self._bind_row_focus(row, blog.id)

        top = frame(row, bg)
        top.pack(fill=tk.X, padx=8, pady=(8, 0))
        self._bind_row_focus(top, blog.id)
        check_var = self._ensure_check(blog.id)
        if ctk:
            btn = ctk.CTkCheckBox(
                top, text="", variable=check_var, width=24, height=24,
                fg_color=COLORS["accent"], hover_color=COLORS["accent_hover"],
                command=lambda bid=blog.id: self._on_blog_checked(bid),
            )
        else:
            btn = tk.Checkbutton(
                top, text="", variable=check_var, bg=bg,
                command=lambda bid=blog.id: self._on_blog_checked(bid),
            )
        btn.pack(side=tk.LEFT)
        btn._blog_id = blog.id
        self._mark_check_hit(btn)
        self._blog_buttons.append(btn)

        id_chip = pill(top, blog.id[-6:], "info")
        id_chip.pack(side=tk.LEFT, padx=(4, 0))
        id_chip._blog_id = blog.id
        id_chip._blog_check_hit = True
        try:
            id_chip.configure(cursor="hand2")
        except Exception:
            pass
        id_chip.bind("<Button-1>", lambda _e, bid=blog.id: self._on_id_chip_click(bid))
        self._hover.bind(id_chip, lambda b=blog: (
            (COLORS["text"], "다중 선택", "body_bold"),
            (COLORS["text_muted"], "아이디를 누르면 작업 대상에 넣거나 뺍니다.", "small"),
            (COLORS["text"], b.id, "caption"),
        ))

        setup_done = sum(1 for key in SETUP_KEYS if key in blog.done)
        setup_tone = "ok" if setup_done == len(SETUP_KEYS) else "wait" if setup_done else "off"
        setup_pill = pill(top, f"설정 {setup_done}/{len(SETUP_KEYS)}", setup_tone)
        setup_pill.pack(side=tk.RIGHT)
        self._hover.bind(setup_pill, lambda b=blog: self._setup_status_hover(b))
        self._bind_row_focus(setup_pill, blog.id)
        folder_path = self._blog_folder_of(blog.id)
        if folder_path:
            copy_btn = button(
                top,
                "폴더 복사",
                variant="primary",
                width=88,
                height=28,
                command=lambda target=folder_path: self._copy_folder_path(target),
            )
            copy_btn.pack(side=tk.RIGHT, padx=(0, 6))

        name = blog.name or blog.address or blog.id
        name_lbl = label(top, name, "body_bold")
        name_lbl.pack(side=tk.LEFT, padx=(6, 0))
        self._bind_row_focus(name_lbl, blog.id)
        code_name = self._html_code_of(blog.id)
        if code_name:
            code_pill = pill(top, code_name, "info")
            code_pill.pack(side=tk.LEFT, padx=(6, 0))
            self._bind_row_focus(code_pill, blog.id)

        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/")
        bottom = frame(row, bg)
        bottom.pack(fill=tk.X, padx=8, pady=(2, 8))
        self._bind_row_focus(bottom, blog.id)
        addr = host or "주소 없음"
        addr_lbl = label(bottom, addr, "small", COLORS["accent"] if host else COLORS["text_light"])
        addr_lbl.pack(side=tk.LEFT)
        self._bind_row_focus(addr_lbl, blog.id)
        stored = self._naver_id_of(blog.id)
        collected = "collect" in blog.done or "collect_post" in blog.done
        indexed = stored if collected and stored else ""
        caption = f"색인 {indexed}" if indexed else ""
        naver_lbl = label(bottom, caption, "small", COLORS["success"] if indexed else COLORS["text_muted"])
        naver_lbl._fallback_index = indexed
        self._bind_row_focus(naver_lbl, blog.id)
        if caption:
            naver_lbl.pack(side=tk.LEFT, padx=(8, 0))
        self._index_labels.append(naver_lbl)
        post_count = len(blog.posts)
        if "collect_post" in blog.done:
            post_text, post_tone = f"글 {post_count}", "ok"
        elif post_count:
            post_text, post_tone = f"글 {post_count}", "wait"
        else:
            post_text, post_tone = "글 없음", "off"
        post_pill = pill(bottom, post_text, post_tone)
        post_pill.pack(side=tk.RIGHT)
        self._bind_row_focus(post_pill, blog.id)
        if "collect" in blog.done:
            crawl_lbl = label(
                bottom,
                self._blog_collect_label(blog.id),
                "small",
                COLORS["text_muted"],
                wraplength=280,
                anchor="e",
                justify="right",
            )
            crawl_lbl.pack(side=tk.RIGHT, padx=(0, 8))
            self._bind_row_focus(crawl_lbl, blog.id)
        row._paint_parts = [row, top, bottom]

    def _on_id_chip_click(self, blog_id: str):
        self._toggle_blog_check(blog_id)
        return "break"

    def _select_blog(self, blog_id: str) -> None:
        prev = self.blog_var.get()
        if prev == blog_id:
            self._paint_record_rows()
            return
        self.blog_var.set(blog_id)
        self._paint_rows_for(prev)
        self._paint_rows_for(blog_id)
        self._paint_record_rows()
        if getattr(self, "_main_tab", "") == "블로그":
            self._render_blog_detail()
        else:
            self._detail_dirty = True
        self._schedule_write_count()

    def _on_blog_selected(self) -> None:
        self._paint_rows_for(self.blog_var.get())
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
                if child is getattr(row, "_status_pill", None):
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
            return
        times = self._blog_times(blog.id)
        last = self._fmt_when(self._last_recrawl(blog.id)) or "기록 없음"
        naver_id = self._naver_id_of(blog.id) or "없음"
        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/") or "주소 없음"
        posts = list(reversed(normalize_posts(blog.posts)))
        query = (self.post_query.get() or "").strip().lower()
        shown = []
        for post in posts:
            url = str(post.get("url") or "")
            title = str(post.get("title") or "")
            if query and query not in f"{title} {url}".lower():
                continue
            shown.append(post)
        self.posts_heading.configure(text=blog.name or host)
        crawl = "글 수집 완료" if "collect_post" in blog.done else "글 수집 전"
        self.posts_meta.configure(
            text=f"{host}  ·  글 {len(shown)}/{len(posts)}  ·  {crawl}  ·  네이버 {naver_id}  ·  재수집 {last}"
        )
        if not shown:
            label(
                wrap,
                "이 블로그에서 인식된 글이 없습니다." if not posts else "검색과 맞는 글이 없습니다.",
                "body",
                COLORS["text_muted"],
            ).pack(anchor="w", pady=8)
            return
        for index, post in enumerate(shown, start=1):
            url = str(post.get("url") or "")
            if not is_post_permalink(url):
                continue
            title = str(post.get("title") or "").strip() or url
            self._add_post_card(wrap, index, title, url, blog.id)

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

    def _add_post_card(self, parent, index: int, title: str, url: str, blog_id: str) -> None:
        if ctk:
            card_row = ctk.CTkFrame(
                parent, fg_color=COLORS["input_bg"], corner_radius=8,
                border_width=1, border_color=COLORS["border"],
            )
        else:
            card_row = tk.Frame(parent, bg=COLORS["input_bg"], highlightbackground=COLORS["border"], highlightthickness=1)
        card_row.pack(fill=tk.X, pady=2, padx=2)
        right = frame(card_row, COLORS["input_bg"])
        right.pack(side=tk.RIGHT, padx=(6, 8), pady=4)
        label(
            right,
            self._post_crawl_label(blog_id, url),
            "small",
            COLORS["text_muted"],
            wraplength=240,
            anchor="e",
            justify="right",
        ).pack(anchor="e")
        actions = frame(right, COLORS["input_bg"])
        actions.pack(anchor="e", pady=(2, 0))
        button(
            actions,
            "이글 수집",
            variant="primary",
            width=84,
            height=28,
            command=lambda target=url, blog=blog_id: self.on_collect_one_post(blog, target, False),
        ).pack(side=tk.LEFT, padx=(0, 4))
        button(
            actions,
            "이글 재수집",
            variant="ghost",
            width=92,
            height=28,
            command=lambda target=url, blog=blog_id: self.on_collect_one_post(blog, target, True),
        ).pack(side=tk.LEFT, padx=(0, 4))
        button(
            actions,
            "글 삭제",
            variant="danger",
            width=72,
            height=28,
            command=lambda target=url, blog=blog_id, name=title: self.on_delete_post(blog, target, name),
        ).pack(side=tk.LEFT)
        left = frame(card_row, COLORS["input_bg"])
        left.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(8, 0), pady=4)
        label(left, f"{index}. {title}", "body_bold").pack(anchor="w")

        def open_url(_event=None, target=url):
            webbrowser.open(target)

        if ctk:
            link = ctk.CTkLabel(
                left, text=url, font=FONTS["small"], text_color=COLORS["accent"],
                cursor="hand2", anchor="w",
            )
        else:
            link = tk.Label(
                left, text=url, font=FONTS["small"], fg=COLORS["accent"],
                bg=COLORS["input_bg"], cursor="hand2", anchor="w",
            )
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
            if account and count is not None:
                text = f"서치어드바이저: {account} · 사이트 {count}개"
            elif account:
                text = f"서치어드바이저: {account}"
            elif count is not None:
                text = f"서치어드바이저: 로그인됨 · 사이트 {count}개"
            self._set_naver_status(text, COLORS["success"])
        else:
            self._set_naver_status("서치어드바이저: 로그인 전", COLORS["text_muted"])
        self._dashboard_fp = None
        if hasattr(self, "_blog_list_inner"):
            self._refresh_dashboard()

    def _set_naver_login_button(self, text: str, enabled: bool):
        self.naver_login_btn.configure(text=text, state="normal" if enabled else "disabled")

    def _set_naver_status(self, text: str, color: str):
        self.naver_status_label.configure(text=text, text_color=color if ctk else None)
        if not ctk:
            self.naver_status_label.configure(fg=color)

    def _require_sessions(self, title: str, require_naver: bool = True, require_blogger: bool = True) -> bool:
        if self._naver_busy or self._settings_busy or self._create_busy:
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
        ):
            btn.configure(state=state)

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
        label(body, "블로그 목록과 기록 시트에 같은 이름으로 표시됩니다.", "small", COLORS["text_muted"]).pack(
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
        host = widget if ctk else getattr(widget, "inner", widget)
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
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"네이버 최초 HTML 코드 넣기 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
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
                except OwnershipPending as exc:
                    self.log(f"{name}: {exc}")
                    warnings.append(f"{name}: {exc}")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"네이버 최초 수집 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
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

    def _naver_post_worker(self, jobs: list[tuple[str, str, list[str]]]):
        warnings: list[str] = []
        grand = sum(len(posts) for _blog_id, _address, posts in jobs)
        offset = 0
        try:
            for index, (blog_id, address, posts) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"글페이지 수집요청 {len(posts)}개 · {address}")
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
                        f"글페이지 수집요청을 마쳤습니다. {address} · 성공 {result.get('success') or 0} · 실패 {result.get('fail') or 0}"
                    )
                    done_urls = list(result.get("urls") or [])
                    if done_urls:
                        self.root.after(
                            0,
                            lambda bid=blog_id, urls=done_urls: self._stamp_posts(bid, urls, bump_if_exists=True),
                        )
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"글페이지 수집요청 오류: {address} · {detail}")
                    warnings.append(f"{address}: {detail}")
                offset += len(posts)
            self.root.after(0, lambda: self._apply_state(self.session.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("글페이지 수집요청", m))
        except StopRequested:
            self.log("글페이지 수집요청을 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"글페이지 수집요청 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("글페이지 수집요청", m))
        finally:
            self.root.after(0, self._naver_apply_done)
            self._queue_sheet_sync([blog_id for blog_id, _address, _posts in jobs], "글 수집")

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
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"설정 적용 오류: {name} · {detail}")
                    warnings.append(f"{name}: {detail}")
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
        self._refresh_dashboard()

    def _stamp_activity(self, blog_id: str, key: str) -> None:
        now = datetime.now().isoformat(timespec="minutes")
        cur = self._blog_meta.setdefault(blog_id, {})
        cur["last_activity"] = now
        if key == "collect":
            count = self._count_value(cur.get("blog_crawl_count"))
            if str(cur.get("last_blog_crawl") or "").strip():
                count += 1
            if not str(cur.get("blog_collect_at") or "").strip():
                cur["blog_collect_at"] = str(cur.get("last_blog_crawl") or "").strip() or now
            cur["blog_crawl_count"] = count
            cur["last_blog_crawl"] = now
        elif key == "collect_post":
            cur["last_post_crawl"] = now
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
        if ctk:
            self.progress_bar.set(ratio)
        else:
            self.progress_bar["value"] = ratio * 100

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
        self._apply_state(self.session.state)
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
        if not picked:
            return
        live = {blog.id for blog in self.session.state.blogs}
        if live:
            picked = [blog_id for blog_id in picked if blog_id in live] or picked
        chosen = set(picked)
        for blog_id, var in list(self._blog_check_vars.items()):
            var.set(blog_id in chosen)
        for blog_id in picked:
            self._ensure_check(blog_id).set(True)
        self.blog_var.set(picked[-1])
        self._scroll_blog_id = picked[-1]
        self._update_sel_count()
        self._show_main_tab("블로그")
        self._dashboard_fp = None
        self._schedule_dashboard()
        self._schedule_sheet_sync(picked, "블로그 생성", new_ids=picked)

    def _scroll_blog_list_to_end(self) -> None:
        widget = getattr(self, "blog_list", None)
        canvas = getattr(widget, "_parent_canvas", None)
        if canvas is None:
            return
        try:
            canvas.update_idletasks()
            canvas.yview_moveto(1.0)
        except Exception:
            pass

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
        job = getattr(self, "_write_count_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        self._write_count_job = self.root.after(200, self._flush_write_count)

    def _flush_write_count(self) -> None:
        self._write_count_job = None
        self._refresh_write_count()

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
                moved = self._move_manuscript_to_success(path, folder)
                done += 1
                self.log(f"작성된 글 주소: {post_url}")
                self.log(f"원고를 성공 폴더로 옮겼습니다: {os.path.basename(moved)}")
                self.root.after(0, lambda: self._apply_state(self.session.state))
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
        self.status_label.configure(text=text, text_color=color if ctk else None)
        if not ctk:
            self.status_label.configure(fg=color)

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
                    tuple(str(item.get("url") or "") for item in blog.posts),
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

    def _clear_input_traces(self) -> None:
        for name in ("blog_query", "post_query", "index_query"):
            var = getattr(self, name, None)
            if var is None:
                continue
            try:
                infos = var.trace_info()
            except Exception:
                continue
            for item in infos:
                try:
                    var.trace_remove(item[0], item[1])
                except Exception:
                    pass

    def _destroy_ui(self) -> None:
        try:
            self._hover.hide()
        except Exception:
            pass
        if self._watch_id is not None:
            try:
                self.root.after_cancel(self._watch_id)
            except Exception:
                pass
            self._watch_id = None
        if self._dash_after is not None:
            try:
                self.root.after_cancel(self._dash_after)
            except Exception:
                pass
            self._dash_after = None
        self._clear_input_traces()
        self._index_row_frames = {}
        self._index_fp = None
        self._tab_stacked = False
        self._tabs_stacked = False
        self._tab_raise_ready = False
        self._painted_tab = None
        paint_job = getattr(self, "_tab_paint_job", None)
        if paint_job is not None:
            try:
                self.root.after_cancel(paint_job)
            except Exception:
                pass
            self._tab_paint_job = None
        job = getattr(self, "_sheet_sync_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
            self._sheet_sync_job = None
        job = getattr(self, "_tab_refresh_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
            self._tab_refresh_job = None
        job = getattr(self, "_write_count_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
            self._write_count_job = None
        job = getattr(self, "_side_list_job", None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
            self._side_list_job = None
        for child in list(self.root.winfo_children()):
            try:
                child.destroy()
            except Exception:
                pass
        self._blog_buttons.clear()
        self._blog_row_frames.clear()
        self._blog_filter_btns.clear()
        self._dock_buttons.clear()
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
            import sheet_sync
            import naver_index_check
            importlib.reload(sheet_sync)
            importlib.reload(naver_index_check)
            import blogger_session
            import naver_advisor_session
            import paths
            import ui_theme
            import app as app_module

            importlib.reload(paths)
            importlib.reload(ui_theme)
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
            self._code_reload_pending = True
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
            self.root.after_cancel(self._watch_id)
        if self._dash_after is not None:
            try:
                self.root.after_cancel(self._dash_after)
            except Exception:
                pass
        self.session.close(kill_chrome=False)
        self.naver.close(kill_chrome=False)
        self.root.destroy()
