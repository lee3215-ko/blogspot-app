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
from paths import APP_VERSION, data_path, get_app_dir, is_frozen
from ui_theme import COLORS, FONTS, HoverPopup, button, card, frame, label, pill, scrollable

try:
    import customtkinter as ctk
except ImportError:
    ctk = None

IMAGE_EXTS = {".ico", ".jpg", ".jpeg", ".gif", ".png", ".bmp", ".tif", ".tiff", ".webp"}
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
        self._ensure_write_folders()
        shell = frame(self.root, COLORS["bg"])
        shell.pack(fill=tk.BOTH, expand=True, padx=16, pady=12)
        self._outer = shell

        header = frame(shell, COLORS["bg"])
        header.pack(fill=tk.X, pady=(0, 8))
        title_wrap = frame(header, COLORS["bg"])
        title_wrap.pack(side=tk.LEFT, fill=tk.X, expand=True)
        label(title_wrap, "블로그스팟", "title").pack(anchor="w")
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
            button(self.action_host, "네이버 최초 HTML 코드 넣기", variant="primary", width=220, height=40, command=self.on_naver_html_insert),
            button(self.action_host, "네이버 최초 수집", variant="success", width=160, height=40, command=self.on_naver_first_setup),
            button(self.action_host, "블로그 수집요청", variant="ghost", width=150, height=40, command=self.on_naver_blog_crawl),
            button(self.action_host, "글페이지 수집요청", variant="ghost", width=160, height=40, command=self.on_naver_post_crawl),
            button(self.action_host, "글 작성", variant="success", width=120, height=40, command=self.on_write_post),
            button(self.action_host, "블로그 생성", variant="primary", width=130, height=40, command=self.on_create_blogs),
            button(self.action_host, "일시정지", variant="ghost", width=100, height=40, command=self.on_toggle_pause),
            button(self.action_host, "정지", variant="danger", width=80, height=40, command=self.on_stop_settings),
        ]
        (
            self.settings_btn,
            self.naver_html_btn,
            self.naver_first_btn,
            self.naver_blog_btn,
            self.naver_post_btn,
            self.post_btn,
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
            ("글쓰기", 100),
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
        blog_inner.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        self.blog_heading = label(blog_inner, "블로그", "heading", COLORS["text"])
        self.blog_heading.pack(anchor="w")
        self.blog_summary = frame(blog_inner, COLORS["card"])
        self.blog_summary.pack(fill=tk.X, pady=(6, 0))

        if ctk:
            self.blog_search = ctk.CTkEntry(
                blog_inner,
                textvariable=self.blog_query,
                height=36,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="이름·주소 검색",
            )
        else:
            self.blog_search = tk.Entry(blog_inner, textvariable=self.blog_query, font=FONTS["body"])
        self.blog_search.pack(fill=tk.X, pady=(8, 0))
        self.blog_query.trace_add("write", self._on_blog_query_changed)

        filter_wrap = frame(blog_inner, COLORS["card"])
        filter_wrap.pack(fill=tk.X, pady=(8, 0))
        for key, title in BLOG_FILTERS:
            btn = button(
                filter_wrap,
                title,
                variant="ghost",
                width=108,
                height=32,
                command=lambda k=key: self._set_blog_filter(k),
            )
            btn.pack(side=tk.LEFT, padx=(0, 6), pady=(0, 4))
            self._blog_filter_btns[key] = btn
        self._paint_filter_btns()

        sel_row = frame(blog_inner, COLORS["card"])
        sel_row.pack(fill=tk.X, pady=(4, 6))
        self.sel_count_label = label(sel_row, "0개 선택", "body_bold", COLORS["accent"])
        self.sel_count_label.pack(side=tk.LEFT)
        self.select_all_btn = button(
            sel_row, "전체 선택", variant="ghost", width=100, height=32,
            command=lambda: self._set_visible_checks(True),
        )
        self.select_all_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.select_none_btn = button(
            sel_row, "선택 해제", variant="ghost", width=100, height=32,
            command=lambda: self._set_visible_checks(False),
        )
        self.select_none_btn.pack(side=tk.LEFT, padx=(6, 0))
        recrawl_row = frame(blog_inner, COLORS["card"])
        recrawl_row.pack(fill=tk.X, pady=(0, 6))
        self.blog_recrawl_btn = button(
            recrawl_row,
            "블로그 재수집",
            variant="primary",
            width=130,
            height=32,
            command=self.on_naver_blog_recrawl,
        )
        self.blog_recrawl_btn.pack(side=tk.LEFT)

        self.blog_list = scrollable(blog_inner, height=280, bg=COLORS["card"])
        self.blog_list.pack(fill=tk.BOTH, expand=True)
        for event in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.blog_list.bind(event, lambda _e: self._hover.hide(), add="+")
        host = getattr(self.blog_list, "inner", self.blog_list)
        self._blog_list_inner = frame(host, COLORS["card"])
        self._blog_list_inner.pack(fill=tk.X)

        right_card = card(body)
        right_card.grid(row=0, column=1, sticky="nsew")
        right = frame(right_card, COLORS["card"])
        right.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)
        self.posts_heading = label(right, "글", "heading", COLORS["text"])
        self.posts_heading.pack(anchor="w")
        self.posts_meta = label(
            right,
            "목록을 누르면 이 블로그 글만 봅니다. 아이디나 체크박스로 고른 뒤 글쓰기 탭에서 원고를 정해 글 작성을 누릅니다.",
            "body",
            COLORS["text_muted"],
            wraplength=520,
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

        self.posts_list = scrollable(right, height=220, bg=COLORS["card"])
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
            "코드를 여러 개 저장할 수 있습니다. 선택한 코드만 네이버 최초 HTML 코드 넣기에 사용합니다. 서치어드바이저 메타 태그는 <head> 바로 아래에 넣은 뒤, 전체를 테마 편집기에 붙여 넣습니다.",
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
        self._show_main_tab("블로그")
        self._fit_window()
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
            hover.suppress(0.35)

    def _install_drag_hook(self) -> None:
        if getattr(self, "_drag_hooked", False):
            return
        try:
            import ctypes
        except Exception:
            return
        user32 = ctypes.WinDLL("user32", use_last_error=True)
        user32.GetParent.argtypes = [ctypes.c_void_p]
        user32.GetParent.restype = ctypes.c_void_p
        client = int(self.root.winfo_id() or 0)
        if not client:
            self.root.after(200, self._install_drag_hook)
            return
        frame = int(user32.GetParent(client) or 0) or client
        WM_ENTERSIZEMOVE = 0x0231
        WM_EXITSIZEMOVE = 0x0232
        WM_SETREDRAW = 0x000B
        RDW_INVALIDATE = 0x0001
        RDW_ERASE = 0x0004
        RDW_ALLCHILDREN = 0x0080
        RDW_UPDATENOW = 0x0100
        RDW_FRAME = 0x0400
        redraw_flags = RDW_INVALIDATE | RDW_ERASE | RDW_ALLCHILDREN | RDW_UPDATENOW | RDW_FRAME

        user32.CallWindowProcW.argtypes = [
            ctypes.c_void_p,
            ctypes.c_void_p,
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.c_void_p,
        ]
        user32.CallWindowProcW.restype = ctypes.c_ssize_t
        user32.SendMessageW.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_void_p, ctypes.c_void_p]
        user32.SendMessageW.restype = ctypes.c_ssize_t
        user32.RedrawWindow.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint]
        user32.RedrawWindow.restype = ctypes.c_int
        set_long = getattr(user32, "SetWindowLongPtrW", None) or user32.SetWindowLongW
        get_long = getattr(user32, "GetWindowLongPtrW", None) or user32.GetWindowLongW
        set_long.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
        set_long.restype = ctypes.c_void_p
        get_long.argtypes = [ctypes.c_void_p, ctypes.c_int]
        get_long.restype = ctypes.c_void_p

        targets = []
        for hwnd in (frame, client):
            if hwnd and hwnd not in targets:
                targets.append(hwnd)

        def set_redraw(enabled: bool) -> None:
            flag = ctypes.c_void_p(1 if enabled else 0)
            for hwnd in targets:
                user32.SendMessageW(hwnd, WM_SETREDRAW, flag, None)
            if enabled:
                for hwnd in targets:
                    user32.RedrawWindow(hwnd, None, None, redraw_flags)

        old = get_long(frame, -4)
        if not old:
            return

        def proc(hwnd, msg, wparam, lparam):
            try:
                if msg == WM_ENTERSIZEMOVE:
                    hover = getattr(self, "_hover", None)
                    if hover is not None:
                        hover.suppress(0.5)
                    set_redraw(False)
                elif msg == WM_EXITSIZEMOVE:
                    set_redraw(True)
            except Exception:
                pass
            return user32.CallWindowProcW(old, hwnd, msg, wparam, lparam)

        WNDPROC = ctypes.WINFUNCTYPE(
            ctypes.c_ssize_t,
            ctypes.c_void_p,
            ctypes.c_uint,
            ctypes.c_void_p,
            ctypes.c_void_p,
        )
        callback = WNDPROC(proc)
        previous = set_long(frame, -4, ctypes.cast(callback, ctypes.c_void_p))
        if not previous:
            return
        self._drag_proc = callback
        self._drag_old_proc = previous
        self._drag_hooked = True

    def _layout_dock(self, _event=None) -> None:
        host = getattr(self, "action_host", None)
        if host is None:
            return
        width = host.winfo_width()
        if width < 80:
            return
        if width == getattr(self, "_dock_width", None):
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
        if width == getattr(self, "_tab_width", None):
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
            "이미지는 이 폴더에서 글을 쓸 때마다 하나를 골라 본문 앞에 넣습니다. 글 작성 버튼은 아래 작업 줄에 있습니다.",
            "body",
            COLORS["text_muted"],
            wraplength=720,
            anchor="w",
            justify="left",
        ).pack(anchor="w", fill=tk.X, pady=(12, 0))
        self._refresh_write_count()

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
        self._main_tab = name
        try:
            self.tab_body.grid_rowconfigure(0, weight=1)
            self.tab_body.grid_columnconfigure(0, weight=1)
        except Exception:
            pass
        for key, item in list(self._main_pages.items()):
            if not self._widget_alive(item):
                self._main_pages.pop(key, None)
                continue
            try:
                item.pack_forget()
            except Exception:
                pass
            if key == name:
                item.grid(row=0, column=0, sticky="nsew")
                try:
                    item.lift()
                except Exception:
                    pass
            else:
                try:
                    item.grid_remove()
                except Exception:
                    pass
        self._paint_main_tabs()
        if name == "글쓰기":
            self._refresh_write_count()

    def _paint_main_tabs(self) -> None:
        for name, btn in self._main_tab_buttons.items():
            active = name == self._main_tab
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
                    "post_crawls": item.get("post_crawls") if isinstance(item.get("post_crawls"), dict) else {},
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
        if self.session.is_alive() and self.session.state.logged_in:
            self.log("이미 로그인되어 있습니다. 목록과 주소를 다시 읽습니다.")
            threading.Thread(target=self._redetect_worker, daemon=True).start()
            return
        self._login_busy = True
        self._set_login_button("로그인 대기 중...", enabled=False)
        self._set_status("Chrome 창에서 로그인해 주세요", COLORS["warning"])
        threading.Thread(target=self._login_worker, daemon=True).start()

    def _login_worker(self):
        try:
            self.session.start_browser()
            state = self.session.wait_until_logged_in()
            if not self.session.is_alive():
                self.root.after(0, self._on_browser_closed)
                return
            if not state.logged_in:
                self.root.after(0, lambda: self._login_failed("로그인을 확인하지 못했습니다."))
                return
            self._merge_blog_meta(state.blogs)
            self.root.after(0, lambda: self._on_logged_in(state))
            self._catalog_worker()
        except Exception as exc:
            self.log(f"로그인 창 오류: {exc}")
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
        self._query_after = self.root.after(200, self._refresh_dashboard)

    def _set_blog_filter(self, key: str) -> None:
        if self._blog_filter == key:
            return
        self._blog_filter = key
        self._paint_filter_btns()
        self._refresh_dashboard()

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
            return (0, -int(blog_id))
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
            hay = " ".join([blog.name, blog.address, blog.id, self._naver_id_of(blog.id)]).lower()
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

    def _naver_id_of(self, blog_id: str) -> str:
        return str((self._blog_meta.get(blog_id) or {}).get("naver_id") or "").strip()

    def _remember_naver_id(self, blog_id: str, account: str = "") -> None:
        account = (account or getattr(self.naver.state, "account", "") or "").strip()
        if not blog_id or not account:
            return
        cur = self._blog_meta.setdefault(blog_id, {})
        if str(cur.get("naver_id") or "").strip():
            return
        cur["naver_id"] = account
        try:
            self._save_blog_meta()
        except Exception:
            pass

    def _dashboard_fingerprint(self, blogs: list[BlogInfo], visible: list[BlogInfo]) -> tuple:
        return (
            self._blog_filter,
            (self.blog_query.get() or "").strip().lower(),
            tuple(
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    tuple(str(item.get("url") or "") for item in blog.posts),
                    tuple(sorted(blog.done)),
                    self._last_recrawl(blog.id),
                    self._naver_id_of(blog.id),
                    self._blog_folder_of(blog.id),
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
            return
        self._dashboard_fp = fp
        self._refreshing = True
        try:
            self._render_blog_summary(blogs)
            self._render_blogs(visible, all_blogs=blogs)
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
        self.blog_heading.configure(
            text=f"블로그 {len(source)} · 최신순" if source else "블로그"
        )
        if not blogs:
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
            return

        known = {blog.id for blog in blogs}
        if self.blog_var.get() not in known:
            selected = next((blog.id for blog in blogs if blog.selected), blogs[0].id)
            self.blog_var.set(selected)

        for blog in blogs:
            self._render_blog_row(parent, blog)
        self._paint_blog_rows()
        self._update_sel_count()
        self._render_blog_detail()

    def _ensure_check(self, blog_id: str) -> tk.BooleanVar:
        var = self._blog_check_vars.get(blog_id)
        if var is None:
            var = tk.BooleanVar(value=False)
            self._blog_check_vars[blog_id] = var
        return var

    def _set_visible_checks(self, value: bool) -> None:
        for blog in self._filter_blogs(self._dashboard_blogs()):
            self._ensure_check(blog.id).set(value)
        self._update_sel_count()
        self._paint_blog_rows()
        self._render_blog_detail()
        self._refresh_write_count()

    def _checked_count(self) -> int:
        return sum(1 for var in self._blog_check_vars.values() if var.get())

    def _update_sel_count(self) -> None:
        if not hasattr(self, "sel_count_label"):
            return
        n = self._checked_count()
        self.sel_count_label.configure(text=f"{n}개 선택")

    def _on_blog_checked(self, blog_id: str) -> None:
        self._update_sel_count()
        self._paint_blog_rows()
        self._refresh_write_count()

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
        try:
            widget.configure(cursor="hand2")
        except Exception:
            pass

    def _mark_check_hit(self, widget) -> None:
        widget._blog_check_hit = True

    def _row_look(self, blog_id: str) -> tuple[str, str, int]:
        if self._ensure_check(blog_id).get():
            return COLORS["row_checked"], COLORS["row_checked_border"], 3
        if blog_id == self.blog_var.get():
            return COLORS["row_focus"], COLORS["row_focus_border"], 3
        return COLORS["card"], COLORS["card_border"], 1

    def _paint_row_widget(self, widget, bg: str, border: str, width: int) -> None:
        try:
            widget.configure(fg_color=bg, border_color=border, border_width=width)
            return
        except Exception:
            pass
        try:
            widget.configure(fg_color=bg)
        except Exception:
            try:
                widget.configure(bg=bg, highlightbackground=border, highlightthickness=width)
            except Exception:
                try:
                    widget.configure(bg=bg)
                except Exception:
                    pass

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

        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/")
        bottom = frame(row, bg)
        bottom.pack(fill=tk.X, padx=8, pady=(2, 8))
        self._bind_row_focus(bottom, blog.id)
        addr = host or "주소 없음"
        addr_lbl = label(bottom, addr, "small", COLORS["accent"] if host else COLORS["text_light"])
        addr_lbl.pack(side=tk.LEFT)
        self._bind_row_focus(addr_lbl, blog.id)
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
        if self.blog_var.get() == blog_id:
            return
        self.blog_var.set(blog_id)
        self._paint_blog_rows()
        self._render_blog_detail()
        self._refresh_write_count()

    def _on_blog_selected(self) -> None:
        self._paint_blog_rows()
        self._render_blog_detail()

    def _paint_blog_rows(self) -> None:
        for blog_id, row in self._blog_row_frames.items():
            bg, border, width = self._row_look(blog_id)
            parts = getattr(row, "_paint_parts", None) or [row]
            for part in parts:
                self._paint_row_widget(part, bg, border, width if part is row else 0)

    def _render_blog_detail(self) -> None:
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
            if cur_w > max_w or cur_h > max_h:
                self.root.geometry(f"{min(cur_w, max_w)}x{min(cur_h, max_h)}")
        except Exception:
            pass

    def _restore_naver_if_open(self):
        if self._naver_login_busy or not self.naver.chrome_running():
            return
        threading.Thread(target=self._naver_restore_worker, daemon=True).start()

    def _naver_restore_worker(self):
        try:
            if self.naver.reattach() and self.naver.state.logged_in:
                try:
                    self.naver.count_sites()
                except Exception:
                    pass
                self.root.after(0, lambda: self._on_naver_logged_in(self.naver.state))
        except Exception as exc:
            self.log(f"서치어드바이저 자동 재연결 실패: {exc}")

    def on_naver_login(self):
        if self._naver_login_busy:
            return
        if self.naver.is_alive() and self.naver.state.logged_in:
            self.log("서치어드바이저가 이미 로그인되어 있습니다. 사이트 수를 다시 읽습니다.")
            threading.Thread(target=self._naver_count_worker, daemon=True).start()
            return
        self._naver_login_busy = True
        self._set_naver_login_button("로그인 대기 중...", enabled=False)
        self._set_naver_status("서치어드바이저 창에서 로그인해 주세요", COLORS["warning"])
        threading.Thread(target=self._naver_login_worker, daemon=True).start()

    def _naver_login_worker(self):
        try:
            self.naver.start_login()
            state = self.naver.wait_until_logged_in()
            if not self.naver.is_alive():
                self.root.after(0, self._on_naver_closed)
                return
            if not state.logged_in:
                self.root.after(0, lambda: self._naver_login_failed("서치어드바이저 로그인을 확인하지 못했습니다."))
                return
            self.root.after(0, lambda: self._on_naver_logged_in(state))
        except Exception as exc:
            self.log(f"서치어드바이저 로그인 오류: {exc}")
            self.root.after(0, lambda: self._naver_login_failed(str(exc)))

    def _naver_count_worker(self):
        try:
            self.naver.count_sites(force_reload=True)
            self.root.after(0, lambda: self._on_naver_logged_in(self.naver.state))
        except Exception as exc:
            self.log(f"사이트 수 인식 오류: {exc}")

    def _on_naver_logged_in(self, state):
        self._naver_login_busy = False
        self._set_naver_login_button("사이트 수 다시 읽기", enabled=True)
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
            self.naver_blog_btn,
            self.naver_post_btn,
            self.select_all_btn,
            self.select_none_btn,
            self.blog_recrawl_btn,
            self.create_blogs_btn,
            self.create_side_btn,
        ):
            btn.configure(state=state)

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
            button(
                host,
                str(item.get("name") or f"{index + 1}코드"),
                variant="primary" if index == current else "ghost",
                width=88,
                height=32,
                command=lambda pick=index: self.on_select_html_code(pick),
            ).pack(side=tk.LEFT, padx=(0, 6), pady=4)

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
        name = self._next_html_code_name()
        self._html_codes.append({"name": name, "html": ""})
        self._html_code_index = len(self._html_codes) - 1
        self._render_html_code_buttons()
        self._load_html_editor()
        self.log(f"HTML 코드를 추가했습니다: {name}")
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

    def _naver_html_worker(self, jobs: list[tuple[str, str]], template: str):
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
                self._remember_naver_id(blog_id)
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
                    self.log(f"편집 코드 전체를 테마에 붙여 넣었습니다: {name}")
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
        if key in {"theme_head", "naver_verify", "collect", "collect_post", "crawl_fast"}:
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
                warnings.append(f"{name}: 생성 결과를 확인하지 못했습니다.")
                self.log(f"블로그 생성 확인 실패: {name}")
            self.root.after(0, lambda: self._apply_state(self.session.state))
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

    def _refresh_write_count(self) -> None:
        widget = getattr(self, "write_count_label", None)
        if not self._widget_alive(widget):
            return
        blogs = self._checked_blogs() if hasattr(self, "blog_var") else []
        folder = self.manuscript_var.get().strip() if hasattr(self, "manuscript_var") else ""
        files: list[str] = []
        if folder and os.path.isdir(folder):
            try:
                files = self._manuscript_files(folder)
            except Exception:
                files = []
        blog_count = len(blogs)
        file_count = len(files)
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
        manuscript_folder = self.manuscript_var.get().strip()
        image_folder = self.post_image_var.get().strip()
        if not manuscript_folder or not os.path.isdir(manuscript_folder):
            messagebox.showwarning("글 작성", "글쓰기 탭에서 원고 폴더를 선택해 주세요.")
            self._show_main_tab("글쓰기")
            return
        if not image_folder or not os.path.isdir(image_folder):
            messagebox.showwarning("글 작성", "글쓰기 탭에서 이미지 폴더를 선택해 주세요.")
            self._show_main_tab("글쓰기")
            return
        files = self._manuscript_files(manuscript_folder)
        if not files:
            messagebox.showwarning("글 작성", "원고 폴더에 txt 파일이 없습니다. 성공 폴더 안의 파일은 다시 쓰지 않습니다.")
            return
        raw_count = self.write_count_var.get().strip() if hasattr(self, "write_count_var") else ""
        if not raw_count.isdigit() or int(raw_count) < 1:
            messagebox.showwarning("글 작성", "글쓰기 탭에서 작성할 글 개수를 1 이상으로 적어 주세요.")
            self._show_main_tab("글쓰기")
            return
        count = int(raw_count)
        if len(files) < count:
            messagebox.showwarning(
                "글 작성",
                f"원고가 {len(files)}개인데 {count}개를 쓰려고 합니다. 원고를 더 넣거나 개수를 줄여 주세요.",
            )
            self._show_main_tab("글쓰기")
            return
        try:
            self._pick_random_image(image_folder)
        except RuntimeError as exc:
            messagebox.showwarning("글 작성", str(exc))
            return
        self._save_local_settings()
        chosen_blogs = [blogs[index % len(blogs)] for index in range(count)]
        jobs = list(zip(chosen_blogs, files[:count]))
        self.log(f"작성할 글 {len(jobs)}개")
        self._post_busy = True
        self._paused = False
        self._run_control.reset()
        self.post_btn.configure(state="disabled")
        self.settings_btn.configure(state="disabled")
        self._set_naver_buttons(False)
        self._set_run_controls(True)
        self._set_progress(0, len(jobs), f"작성할 글 {len(jobs)}개")
        threading.Thread(target=self._write_worker, args=(jobs, manuscript_folder, image_folder), daemon=True).start()

    def _write_worker(self, jobs: list, manuscript_folder: str, image_folder: str):
        done = 0
        total = len(jobs)
        try:
            self.session.control = self._run_control
            for index, (blog, path) in enumerate(jobs, start=1):
                self._run_control.checkpoint()
                title = os.path.splitext(os.path.basename(path))[0].strip() or "제목 없음"
                body = self._manuscript_html(self._read_manuscript(path))
                image_path = self._pick_random_image(image_folder)
                name = blog.name or blog.id
                self.root.after(0, lambda i=index, t=total, n=name: self._set_progress(i - 1, t, f"글 작성: {n}"))
                self.log(f"글 작성 {index}/{total}: [{name}] {title} · 이미지 {os.path.basename(image_path)}")
                post_url = self.session.publish_manuscript(blog.id, title, body, image_path)
                if not post_url:
                    raise RuntimeError(f"{name}: 게시는 시도했지만 글 주소를 찾지 못했습니다. 원고는 그대로 둡니다.")
                moved = self._move_manuscript_to_success(path, manuscript_folder)
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
        busy = self._any_busy()
        if not busy:
            if self.session.driver is not None and not self.session.chrome_running():
                self._on_browser_closed()
            naver_dead = self.naver.driver is not None and not self.naver.chrome_running()
            naver_missing = self.naver.driver is None and self.naver.chrome_running()
            if naver_dead or naver_missing:
                if self.naver.chrome_running() and self.naver.reattach():
                    self._apply_naver_state(self.naver.state)
                elif not self.naver.chrome_running():
                    self._on_naver_closed()
            if (
                self.session.driver is not None
                and self.session.chrome_running()
                and not self._watch_detect_running
                and not self._catalog_running
            ):
                self._watch_detect_running = True
                threading.Thread(target=self._watch_detect_worker, daemon=True).start()
        self._watch_id = self.root.after(3000, self._watch)

    def _watch_detect_worker(self):
        try:
            if self._any_busy() or self._catalog_running or self.session.driver is None:
                return
            state = self.session.detect()
            if not state.logged_in:
                return
            current = [
                (
                    blog.id,
                    blog.address,
                    tuple(str(item.get("url") or "") for item in blog.posts),
                    tuple(sorted(blog.done)),
                )
                for blog in state.blogs
            ]
            if current and current != self._shown_session_keys:
                self._shown_session_keys = current
                self.root.after(0, lambda: self._apply_state(state))
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
        if self.naver.chrome_running():
            self.log("서치어드바이저 Chrome이 아직 열려 있어 연결을 유지합니다.")
            return
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
        if self._login_busy or not self.session.chrome_running():
            return
        threading.Thread(target=self._blogger_restore_worker, daemon=True).start()

    def _blogger_restore_worker(self):
        try:
            if not self.session.reattach():
                return
            self._merge_blog_meta(self.session.state.blogs)
            state = self.session.state
            self.root.after(0, lambda: self._on_logged_in(state))
            self._catalog_worker()
        except Exception as exc:
            self.log(f"블로그스팟 자동 재연결 실패: {exc}")

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
        for name in ("blog_query", "post_query"):
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
            if self.session.state.logged_in:
                self._set_login_button("다시 인식", enabled=True)
                self._apply_state(self.session.state)
                self._start_watch()
            if getattr(self.naver.state, "logged_in", False):
                self._set_naver_login_button("사이트 수 다시 읽기", enabled=True)
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
