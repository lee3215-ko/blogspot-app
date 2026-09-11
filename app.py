"""블로그스팟 글 작성 프로그램."""
from __future__ import annotations

import json
import os
import random
import re
import threading
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
    normalize_posts,
)
from naver_advisor_session import NaverAdvisorSession, OwnershipPending
from paths import APP_VERSION, data_path
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
        self.root.geometry("1220x980")
        self.root.minsize(1040, 740)
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
        self._watch_id = None
        self.blog_var = tk.StringVar(value="")
        self.publish_var = tk.BooleanVar(value=True)
        self.favicon_var = tk.StringVar(value="")
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
        self._hover = HoverPopup(self.root)

        self._build()
        self._load_local_settings()
        self._refresh_dashboard()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.after(80, self._fit_window)
        self.root.after(400, self._restore_naver_if_open)

    def _build(self):
        if ctk:
            outer = ctk.CTkScrollableFrame(self.root, fg_color=COLORS["bg"])
        else:
            outer = frame(self.root, COLORS["bg"])
        self._outer = outer
        outer.pack(fill=tk.BOTH, expand=True, padx=24, pady=20)

        header = frame(outer, COLORS["bg"])
        header.pack(fill=tk.X, pady=(0, 16))
        title_wrap = frame(header, COLORS["bg"])
        title_wrap.pack(side=tk.LEFT, fill=tk.X, expand=True)
        label(title_wrap, "블로그스팟", "title").pack(anchor="w")
        label(
            title_wrap,
            "Chrome 창에서 로그인한 뒤, 인식된 블로그 설정과 원고를 적용합니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", pady=(4, 0))

        login_wrap = frame(header, COLORS["bg"])
        login_wrap.pack(side=tk.RIGHT, padx=(12, 0))
        self.naver_login_btn = button(
            login_wrap,
            "서치어드바이저 로그인",
            variant="ghost",
            width=180,
            command=self.on_naver_login,
        )
        self.naver_login_btn.pack(side=tk.RIGHT)
        self.login_btn = button(
            login_wrap,
            "블로그스팟 로그인",
            variant="primary",
            width=180,
            command=self.on_login,
        )
        self.login_btn.pack(side=tk.RIGHT, padx=(0, 8))

        status_card = card(outer)
        status_card.pack(fill=tk.X, pady=(0, 12))
        status_inner = frame(status_card, COLORS["card"])
        status_inner.pack(fill=tk.X, padx=18, pady=14)
        label(status_inner, "연결 상태", "heading", COLORS["text"]).pack(anchor="w")
        status_grid = frame(status_inner, COLORS["card"])
        status_grid.pack(fill=tk.X, pady=(6, 0))
        status_grid.grid_columnconfigure(0, weight=1)
        status_grid.grid_columnconfigure(1, weight=1)
        status_left = frame(status_grid, COLORS["card"])
        status_left.grid(row=0, column=0, sticky="w")
        status_right = frame(status_grid, COLORS["card"])
        status_right.grid(row=0, column=1, sticky="e")
        self.status_label = label(status_left, "로그인 전", "heading")
        self.status_label.pack(anchor="w")
        self.account_label = label(status_left, "계정: -", "body", COLORS["text_muted"])
        self.account_label.pack(anchor="w", pady=(2, 0))
        self.naver_status_label = label(
            status_right, "서치어드바이저: 로그인 전", "body", COLORS["text_muted"]
        )
        self.naver_status_label.pack(anchor="e")

        blog_card = card(outer)
        blog_card.pack(fill=tk.X, pady=(0, 12))
        blog_inner = frame(blog_card, COLORS["card"])
        blog_inner.pack(fill=tk.X, padx=18, pady=14)
        self.blog_heading = label(blog_inner, "블로그 현황", "heading", COLORS["text"])
        self.blog_heading.pack(anchor="w")
        self.blog_summary = frame(blog_inner, COLORS["card"])
        self.blog_summary.pack(fill=tk.X, pady=(8, 0))

        tool_row = frame(blog_inner, COLORS["card"])
        tool_row.pack(fill=tk.X, pady=(8, 0))
        if ctk:
            self.blog_search = ctk.CTkEntry(
                tool_row,
                textvariable=self.blog_query,
                height=32,
                width=220,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                placeholder_text="이름·주소 검색",
            )
        else:
            self.blog_search = tk.Entry(
                tool_row, textvariable=self.blog_query, font=FONTS["body"]
            )
        self.blog_search.pack(side=tk.LEFT)
        self.blog_query.trace_add("write", self._on_blog_query_changed)
        filter_wrap = frame(tool_row, COLORS["card"])
        filter_wrap.pack(side=tk.LEFT, padx=(10, 0))
        for key, title in BLOG_FILTERS:
            btn = button(
                filter_wrap,
                title,
                variant="ghost",
                width=118,
                height=32,
                command=lambda k=key: self._set_blog_filter(k),
            )
            btn.pack(side=tk.LEFT, padx=(0, 6))
            self._blog_filter_btns[key] = btn
        self._paint_filter_btns()

        sel_row = frame(blog_inner, COLORS["card"])
        sel_row.pack(fill=tk.X, pady=(10, 0))
        self.sel_count_label = label(sel_row, "0개 선택", "body_bold", COLORS["accent"])
        self.sel_count_label.pack(side=tk.LEFT)
        self.select_all_btn = button(
            sel_row,
            "보이는 항목 전체 선택",
            variant="ghost",
            width=170,
            height=32,
            command=lambda: self._set_visible_checks(True),
        )
        self.select_all_btn.pack(side=tk.LEFT, padx=(12, 0))
        self.select_none_btn = button(
            sel_row,
            "선택 해제",
            variant="ghost",
            width=110,
            height=32,
            command=lambda: self._set_visible_checks(False),
        )
        self.select_none_btn.pack(side=tk.LEFT, padx=(8, 0))
        label(
            sel_row,
            "체크한 블로그에 작업을 적용합니다. 이름을 누르면 상세가 바뀝니다.",
            "caption",
            COLORS["text_light"],
        ).pack(side=tk.LEFT, padx=(12, 0))

        cols = frame(blog_inner, COLORS["input_bg"])
        cols.pack(fill=tk.X, pady=(10, 0))
        self._blog_col_headers = (
            ("선택", 40, 0),
            ("블로그", 0, 1),
            ("주소", 150, 0),
            ("네이버 아이디", 120, 0),
            ("설정", 54, 0),
            ("블로그 수집", 124, 0),
            ("글 수집", 132, 0),
            ("마지막 재수집", 108, 0),
        )
        self._configure_blog_columns(cols)
        for index, (title, _minsize, _weight) in enumerate(self._blog_col_headers):
            head = label(cols, title, "caption", COLORS["text_muted"])
            head.grid(
                row=0, column=index, sticky="w", padx=(6 if index else 4, 4), pady=6
            )
            if title == "설정":
                self._hover.bind(head, self._setup_header_hover)

        self.blog_list = scrollable(blog_inner, height=360, bg=COLORS["card"])
        self.blog_list.pack(fill=tk.X, pady=(2, 0))
        for event in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.blog_list.bind(event, lambda _e: self._hover.hide(), add="+")
        host = getattr(self.blog_list, "inner", self.blog_list)
        self._blog_list_inner = frame(host, COLORS["card"])
        self._blog_list_inner.pack(fill=tk.X)
        self.blog_empty = label(
            self._blog_list_inner,
            "로그인하면 블로그가 여기에 표시됩니다.",
            "body",
            COLORS["text_muted"],
        )
        self.blog_empty.pack(anchor="w")
        self.blog_detail_wrap = frame(blog_inner, COLORS["card"])
        self.blog_detail_wrap.pack(fill=tk.X, pady=(10, 0))

        action_card = card(outer)
        action_card.pack(fill=tk.X, pady=(0, 12))
        action_inner = frame(action_card, COLORS["card"])
        action_inner.pack(fill=tk.X, padx=18, pady=14)
        label(action_inner, "작업", "heading", COLORS["text"]).pack(anchor="w")
        label(
            action_inner,
            "체크한 블로그에 순서대로 적용합니다. 체크가 없으면 포커스된 블로그만 적용합니다.",
            "body",
            COLORS["text_muted"],
        ).pack(anchor="w", pady=(4, 10))
        action_row1 = frame(action_inner, COLORS["card"])
        action_row1.pack(fill=tk.X)
        self.settings_btn = button(
            action_row1,
            "설정 적용",
            variant="warning",
            width=150,
            height=42,
            command=self.on_apply_settings,
        )
        self.settings_btn.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 8))
        self.naver_html_btn = button(
            action_row1,
            "네이버 최초 HTML 코드 넣기",
            variant="primary",
            width=230,
            height=42,
            command=self.on_naver_html_insert,
        )
        self.naver_html_btn.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 8))
        self.naver_first_btn = button(
            action_row1,
            "네이버 최초 수집",
            variant="success",
            width=170,
            height=42,
            command=self.on_naver_first_setup,
        )
        self.naver_first_btn.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 8))
        action_row2 = frame(action_inner, COLORS["card"])
        action_row2.pack(fill=tk.X)
        self.naver_blog_btn = button(
            action_row2,
            "블로그 수집요청",
            variant="ghost",
            width=170,
            height=42,
            command=self.on_naver_blog_crawl,
        )
        self.naver_blog_btn.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 8))
        self.naver_post_btn = button(
            action_row2,
            "글페이지 수집요청",
            variant="ghost",
            width=180,
            height=42,
            command=self.on_naver_post_crawl,
        )
        self.naver_post_btn.pack(side=tk.LEFT, padx=(0, 8), pady=(0, 8))

        progress_wrap = frame(action_inner, COLORS["card"])
        progress_wrap.pack(fill=tk.X, pady=(8, 0))
        label(progress_wrap, "진행", "subheading", COLORS["text"]).pack(anchor="w")
        self.progress_label = label(
            progress_wrap, "대기 중", "body", COLORS["text_muted"]
        )
        self.progress_label.pack(anchor="w", pady=(6, 6))
        if ctk:
            self.progress_bar = ctk.CTkProgressBar(
                progress_wrap,
                height=14,
                progress_color=COLORS["accent"],
                fg_color=COLORS["border"],
            )
            self.progress_bar.set(0)
        else:
            self.progress_bar = ttk.Progressbar(progress_wrap, maximum=100, mode="determinate")
        self.progress_bar.pack(fill=tk.X)
        ctrl_row = frame(progress_wrap, COLORS["card"])
        ctrl_row.pack(fill=tk.X, pady=(10, 0))
        self.pause_btn = button(
            ctrl_row, "일시정지", variant="ghost", width=110, command=self.on_toggle_pause
        )
        self.pause_btn.pack(side=tk.LEFT)
        self.stop_btn = button(
            ctrl_row, "정지", variant="danger", width=90, command=self.on_stop_settings
        )
        self.stop_btn.pack(side=tk.LEFT, padx=(8, 0))
        self._set_run_controls(False)

        setup_card = card(outer)
        setup_card.pack(fill=tk.X, pady=(0, 12))
        setup_inner = frame(setup_card, COLORS["card"])
        setup_inner.pack(fill=tk.X, padx=18, pady=14)
        setup_inner.grid_columnconfigure(0, weight=1)
        setup_inner.grid_columnconfigure(1, weight=1)

        desc_wrap = frame(setup_inner, COLORS["card"])
        desc_wrap.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        label(desc_wrap, "구글,네이버 디스크립션", "heading", COLORS["text"]).pack(anchor="w")
        label(
            desc_wrap,
            "한 줄에 하나씩 적으면 그중 하나를 랜덤으로 설명/검색 설명에 넣습니다.",
            "caption",
            COLORS["text_muted"],
        ).pack(anchor="w", pady=(2, 6))
        if ctk:
            self.desc_text = ctk.CTkTextbox(
                desc_wrap,
                height=110,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                wrap="word",
            )
        else:
            self.desc_text = tk.Text(desc_wrap, font=FONTS["body"], wrap=tk.WORD, height=6)
        self.desc_text.pack(fill=tk.BOTH, expand=True)

        fav_wrap = frame(setup_inner, COLORS["card"])
        fav_wrap.grid(row=0, column=1, sticky="nsew", padx=(10, 0))
        label(fav_wrap, "파비콘", "heading", COLORS["text"]).pack(anchor="w")
        label(
            fav_wrap,
            "폴더를 지정하면 이미지를 랜덤으로 올립니다.",
            "caption",
            COLORS["text_muted"],
        ).pack(anchor="w", pady=(2, 6))
        fav_row = frame(fav_wrap, COLORS["card"])
        fav_row.pack(fill=tk.X)
        if ctk:
            self.favicon_entry = ctk.CTkEntry(
                fav_row,
                textvariable=self.favicon_var,
                height=36,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
            )
        else:
            self.favicon_entry = tk.Entry(
                fav_row, textvariable=self.favicon_var, font=FONTS["body"]
            )
        self.favicon_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.folder_btn = button(
            fav_row, "폴더", variant="ghost", width=80, height=36, command=self.on_pick_folder
        )
        self.folder_btn.pack(side=tk.LEFT, padx=(8, 0))

        post_card = card(outer)
        post_card.pack(fill=tk.BOTH, expand=True, pady=(0, 12))
        post_inner = frame(post_card, COLORS["card"])
        post_inner.pack(fill=tk.BOTH, expand=True, padx=18, pady=14)
        label(post_inner, "원고", "heading", COLORS["text"]).pack(anchor="w")

        label(post_inner, "제목", "body", COLORS["text_muted"]).pack(anchor="w", pady=(10, 4))
        if ctk:
            self.title_entry = ctk.CTkEntry(
                post_inner,
                height=38,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
            )
        else:
            self.title_entry = tk.Entry(post_inner, font=FONTS["body"])
        self.title_entry.pack(fill=tk.X)

        label(post_inner, "본문", "body", COLORS["text_muted"]).pack(anchor="w", pady=(12, 4))
        if ctk:
            self.body_text = ctk.CTkTextbox(
                post_inner,
                height=140,
                font=FONTS["body"],
                fg_color=COLORS["input_bg"],
                border_color=COLORS["border"],
                text_color=COLORS["text"],
                wrap="word",
            )
        else:
            self.body_text = tk.Text(post_inner, font=FONTS["body"], wrap=tk.WORD, height=8)
        self.body_text.pack(fill=tk.BOTH, expand=True)

        actions = frame(post_inner, COLORS["card"])
        actions.pack(fill=tk.X, pady=(12, 0))
        if ctk:
            self.publish_check = ctk.CTkCheckBox(
                actions,
                text="바로 게시",
                variable=self.publish_var,
                font=FONTS["body"],
                text_color=COLORS["text"],
                fg_color=COLORS["accent"],
                hover_color=COLORS["accent_hover"],
            )
        else:
            self.publish_check = tk.Checkbutton(
                actions,
                text="바로 게시",
                variable=self.publish_var,
                bg=COLORS["card"],
                font=FONTS["body"],
            )
        self.publish_check.pack(side=tk.LEFT)
        self.post_btn = button(
            actions,
            "글 작성",
            variant="success",
            width=140,
            command=self.on_write_post,
        )
        self.post_btn.pack(side=tk.RIGHT)

        log_card = card(outer)
        log_card.pack(fill=tk.BOTH, expand=False)
        log_inner = frame(log_card, COLORS["card"])
        log_inner.pack(fill=tk.BOTH, expand=True, padx=18, pady=14)
        label(log_inner, "실행 로그", "subheading", COLORS["text_muted"]).pack(anchor="w")
        if ctk:
            self.log_box = ctk.CTkTextbox(
                log_inner,
                height=140,
                font=FONTS["log"],
                fg_color=COLORS["log_bg"],
                text_color=COLORS["log_fg"],
                wrap="word",
            )
        else:
            self.log_box = tk.Text(
                log_inner,
                height=8,
                font=FONTS["log"],
                bg=COLORS["log_bg"],
                fg=COLORS["log_fg"],
                wrap=tk.WORD,
            )
        self.log_box.pack(fill=tk.X, pady=(8, 0))
        if ctk:
            self.log_box.configure(state="disabled")
        else:
            self.log_box.configure(state=tk.DISABLED)
        self._fit_window()

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
            if ctk:
                self.log_box.configure(state="normal")
                self.log_box.insert("end", line)
                self.log_box.see("end")
                self.log_box.configure(state="disabled")
            else:
                self.log_box.configure(state=tk.NORMAL)
                self.log_box.insert(tk.END, line)
                self.log_box.see(tk.END)
                self.log_box.configure(state=tk.DISABLED)

        if threading.current_thread() is threading.main_thread():
            _append()
        else:
            self.root.after(0, _append)

    def _textbox_get(self, widget) -> str:
        if ctk:
            return widget.get("1.0", "end-1c")
        return widget.get("1.0", "end-1c")

    def _textbox_set(self, widget, text: str) -> None:
        if ctk:
            widget.delete("1.0", "end")
            widget.insert("1.0", text)
        else:
            widget.delete("1.0", tk.END)
            widget.insert("1.0", text)

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
        self.favicon_var.set(str(data.get("favicon_folder") or ""))

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
                    "last_post_crawl": str(item.get("last_post_crawl") or ""),
                    "last_activity": str(item.get("last_activity") or ""),
                }
        except Exception:
            self._blog_meta = {}

    def _save_blog_meta(self) -> None:
        path = data_path(BLOG_META_FILE)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self._blog_meta, handle, ensure_ascii=False, indent=2)

    def _remember_blog_meta(self, blogs: list[BlogInfo]) -> None:
        for blog in blogs:
            cur = self._blog_meta.setdefault(blog.id, {})
            if blog.name:
                cur["name"] = blog.name
            if blog.address:
                cur["address"] = blog.address
            cur["posts"] = normalize_posts(blog.posts)
            cur.pop("post_url", None)
            cur.pop("post_title", None)
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
            "google_descriptions": self._textbox_get(self.desc_text),
            "favicon_folder": self.favicon_var.get().strip(),
        }
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(data, handle, ensure_ascii=False, indent=2)

    def _description_lines(self) -> list[str]:
        return [line.strip() for line in self._textbox_get(self.desc_text).splitlines() if line.strip()]

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

    def on_login(self):
        if self._login_busy:
            return
        if self.session.is_alive() and self.session.state.logged_in:
            self.log("이미 로그인되어 있습니다. 블로그 정보를 다시 읽습니다.")
            self._apply_state(self.session.detect())
            threading.Thread(target=self._address_worker, daemon=True).start()
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
            self.session.fetch_blog_addresses()
            self.root.after(0, lambda: self._apply_state(self.session.state))
        except Exception as exc:
            self.log(f"로그인 창 오류: {exc}")
            self.root.after(0, lambda: self._login_failed(str(exc)))

    def _address_worker(self):
        try:
            self._merge_blog_meta(self.session.state.blogs)
            self.session.fetch_blog_addresses()
            self.root.after(0, lambda: self._apply_state(self.session.state))
        except Exception as exc:
            self.log(f"블로그 주소 인식 오류: {exc}")

    def _on_logged_in(self, state: SessionState):
        self._login_busy = False
        self._set_login_button("다시 인식", enabled=True)
        self._apply_state(state)
        names = ", ".join(blog.name or blog.id for blog in state.blogs) or "(없음)"
        self.log(f"로그인 확인. 계정={state.account or '-'} / 블로그={names}")
        self._start_watch()

    def _login_failed(self, reason: str):
        self._login_busy = False
        self._set_login_button("블로그스팟 로그인", enabled=True)
        self._set_status("로그인 실패", COLORS["danger"])
        messagebox.showerror("로그인", reason)

    def _apply_state(self, state: SessionState):
        account = state.account or "-"
        self.account_label.configure(text=f"계정: {account}")
        if state.logged_in:
            count = len(state.blogs)
            self._set_status(f"로그인됨 · 블로그 {count}개 인식", COLORS["success"])
        else:
            self._set_status("로그인 전", COLORS["text"])
        self._merge_progress(state.blogs)
        self._merge_blog_meta(state.blogs)
        self._remember_blog_meta(state.blogs)
        self._refresh_dashboard()

    def _merge_progress(self, blogs: list[BlogInfo]) -> None:
        for blog in blogs:
            blog.done.update(self._progress_map.get(blog.id, []))

    def _configure_blog_columns(self, widget) -> None:
        for index, (_title, minsize, weight) in enumerate(self._blog_col_headers):
            widget.grid_columnconfigure(index, minsize=minsize, weight=weight)

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
        live = {blog.id: blog for blog in self.session.state.blogs}
        ids = list(dict.fromkeys([*live.keys(), *self._blog_meta.keys()]))
        blogs: list[BlogInfo] = []
        for blog_id in ids:
            blog = live.get(blog_id)
            meta = self._blog_meta.get(blog_id) or {}
            if blog is None:
                blog = BlogInfo(
                    id=blog_id,
                    name=str(meta.get("name") or meta.get("address") or blog_id[-6:]),
                    address=str(meta.get("address") or ""),
                    posts=normalize_posts(meta.get("posts") or []),
                    done=set(self._progress_map.get(blog_id, [])),
                )
            else:
                if not blog.name:
                    blog.name = str(meta.get("name") or blog.address or blog_id[-6:])
                blog.done.update(self._progress_map.get(blog_id, []))
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
            self.blog_var.get(),
            tuple(
                (
                    blog.id,
                    blog.name,
                    blog.address,
                    tuple(str(item.get("url") or "") for item in blog.posts),
                    tuple(sorted(blog.done)),
                    self._last_recrawl(blog.id),
                    self._naver_id_of(blog.id),
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
        self.blog_heading.configure(
            text=f"블로그 현황 · {len(source)}개 · 최신 생성순" if source else "블로그 현황"
        )
        if not blogs:
            empty = (
                "조건에 맞는 블로그가 없습니다."
                if source
                else "로그인하거나 이전에 인식한 블로그가 여기에 표시됩니다."
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

    def _checked_count(self) -> int:
        return sum(1 for var in self._blog_check_vars.values() if var.get())

    def _update_sel_count(self) -> None:
        if not hasattr(self, "sel_count_label"):
            return
        n = self._checked_count()
        self.sel_count_label.configure(text=f"{n}개 선택")

    def _on_blog_checked(self, blog_id: str) -> None:
        if self._ensure_check(blog_id).get() and not self.blog_var.get():
            self.blog_var.set(blog_id)
        self._update_sel_count()
        self._paint_blog_rows()
        self._render_blog_detail()

    def _render_blog_row(self, parent, blog: BlogInfo) -> None:
        checked = self._ensure_check(blog.id).get()
        focused = blog.id == self.blog_var.get()
        if checked:
            bg = COLORS["row_checked"]
        elif focused:
            bg = COLORS["row_focus"]
        else:
            bg = COLORS["card"]
        row = frame(parent, bg)
        row.pack(fill=tk.X, pady=1)
        self._configure_blog_columns(row)
        self._blog_row_frames[blog.id] = row

        check_var = self._ensure_check(blog.id)
        if ctk:
            btn = ctk.CTkCheckBox(
                row,
                text="",
                variable=check_var,
                width=24,
                height=24,
                font=FONTS["body"],
                text_color=COLORS["text"],
                fg_color=COLORS["accent"],
                hover_color=COLORS["accent_hover"],
                command=lambda bid=blog.id: self._on_blog_checked(bid),
            )
        else:
            btn = tk.Checkbutton(
                row,
                text="",
                variable=check_var,
                bg=bg,
                command=lambda bid=blog.id: self._on_blog_checked(bid),
            )
        btn.grid(row=0, column=0, padx=(6, 0), pady=6, sticky="w")
        self._blog_buttons.append(btn)

        name = blog.name or blog.address or blog.id
        if len(name) > 24:
            name = name[:23] + "…"
        name_lbl = label(row, name, "body_bold")
        name_lbl.grid(row=0, column=1, sticky="w", padx=6)
        name_lbl.bind("<Button-1>", lambda _e, bid=blog.id: self._select_blog(bid))

        host = re.sub(r"^https?://", "", blog.address or "", flags=re.I).rstrip("/")
        addr = host or "-"
        if len(addr) > 22:
            addr = addr[:21] + "…"
        addr_color = COLORS["accent"] if host else COLORS["text_light"]
        addr_lbl = label(row, addr, "caption", addr_color)
        addr_lbl.grid(row=0, column=2, sticky="w", padx=6)
        if host:
            url = blog.address if str(blog.address).startswith("http") else f"https://{host}"
            try:
                addr_lbl.configure(cursor="hand2")
            except Exception:
                pass
            addr_lbl.bind("<Button-1>", lambda _e, target=url: webbrowser.open(target))

        naver_id = self._naver_id_of(blog.id)
        shown_id = naver_id if naver_id else "-"
        if len(shown_id) > 16:
            shown_id = shown_id[:15] + "…"
        pill(row, shown_id, "info" if naver_id else "off").grid(row=0, column=3, padx=4, sticky="w")

        setup_done = sum(1 for key in SETUP_KEYS if key in blog.done)
        setup_tone = "ok" if setup_done == len(SETUP_KEYS) else "wait" if setup_done else "off"
        setup_pill = pill(row, f"{setup_done}/{len(SETUP_KEYS)}", setup_tone)
        setup_pill.grid(row=0, column=4, padx=4, sticky="w")
        self._hover.bind(setup_pill, lambda b=blog: self._setup_status_hover(b))

        times = self._blog_times(blog.id)
        if "collect" in blog.done:
            when = self._fmt_when(times["blog"])
            blog_text = f"완료 {when}".strip() if when else "완료"
            blog_tone = "ok"
        else:
            blog_text, blog_tone = "미수집", "wait"
        pill(row, blog_text, blog_tone).grid(row=0, column=5, padx=4, sticky="w")

        post_count = len(blog.posts)
        if "collect_post" in blog.done:
            when = self._fmt_when(times["post"])
            extra = f" {when}" if when else ""
            post_text, post_tone = f"완료 {post_count}편{extra}".strip(), "ok"
        elif post_count:
            post_text, post_tone = f"미수집 {post_count}편", "wait"
        else:
            post_text, post_tone = "글 없음", "off"
        pill(row, post_text, post_tone).grid(row=0, column=6, padx=4, sticky="w")

        last = self._fmt_when(self._last_recrawl(blog.id)) or "없음"
        last_tone = "info" if last != "없음" else "off"
        pill(row, last, last_tone).grid(row=0, column=7, padx=(4, 8), sticky="w")

    def _select_blog(self, blog_id: str) -> None:
        self.blog_var.set(blog_id)
        self._on_blog_selected()

    def _on_blog_selected(self) -> None:
        self._paint_blog_rows()
        self._render_blog_detail()

    def _paint_blog_rows(self) -> None:
        focus = self.blog_var.get()
        for blog_id, row in self._blog_row_frames.items():
            if self._ensure_check(blog_id).get():
                color = COLORS["row_checked"]
            elif blog_id == focus:
                color = COLORS["row_focus"]
            else:
                color = COLORS["card"]
            try:
                row.configure(fg_color=color)
            except Exception:
                try:
                    row.configure(bg=color)
                except Exception:
                    pass

    def _render_blog_detail(self) -> None:
        wrap = self.blog_detail_wrap
        for child in wrap.winfo_children():
            child.destroy()
        blog = next((item for item in self._dashboard_blogs() if item.id == self.blog_var.get()), None)
        if blog is None:
            return
        times = self._blog_times(blog.id)
        last = self._fmt_when(self._last_recrawl(blog.id)) or "기록 없음"
        naver_id = self._naver_id_of(blog.id) or "기록 없음"
        checked = self._checked_count()
        label(
            wrap,
            f"포커스: {blog.name or blog.address}  ·  체크 {checked}개  ·  최초수집 아이디 {naver_id}  ·  마지막 재수집 {last}",
            "caption",
            COLORS["text_muted"],
        ).pack(anchor="w")
        posts = normalize_posts(blog.posts)
        if not posts:
            label(wrap, "인식된 글이 없습니다. 글 목록을 다시 인식하면 여기에 나타납니다.", "caption", COLORS["text_light"]).pack(
                anchor="w", pady=(4, 0)
            )
            return
        host = wrap
        if len(posts) > 3:
            scroller = scrollable(wrap, height=84, bg=COLORS["card"])
            scroller.pack(fill=tk.X, pady=(4, 0))
            inner_host = getattr(scroller, "inner", scroller)
            host = frame(inner_host, COLORS["card"])
            host.pack(fill=tk.X)
        for index, post in enumerate(posts, start=1):
            url = str(post.get("url") or "")
            if not is_post_permalink(url):
                continue
            title = str(post.get("title") or "").strip() or url
            crawled = "collect_post" in blog.done
            prefix = f"글 {index}" + (" · 수집됨" if crawled else " · 미수집")
            self._add_post_link(host, url, title, prefix, padx=(0, 0))

    def _add_post_links(self, parent, posts: list[dict]) -> None:
        posts = normalize_posts(posts)
        if not posts:
            return
        for index, post in enumerate(posts, start=1):
            url = str(post.get("url") or "")
            if not is_post_permalink(url):
                continue
            title = str(post.get("title") or "").strip()
            self._add_post_link(parent, url, title or url, f"글 {index}", padx=(0, 0))

    def _add_post_link(self, parent, url: str, text: str = "", prefix: str = "글", padx=(28, 0)) -> None:
        def open_url(_event=None, target=url):
            webbrowser.open(target)

        wrap = frame(parent, COLORS["card"])
        wrap.pack(fill=tk.X, padx=padx)
        label(wrap, prefix, "caption", COLORS["text_muted"]).pack(side=tk.LEFT)
        shown = text or url
        if ctk:
            link = ctk.CTkLabel(
                wrap,
                text=shown,
                font=FONTS["caption"],
                text_color=COLORS["accent"],
                cursor="hand2",
                anchor="w",
            )
        else:
            link = tk.Label(
                wrap,
                text=shown,
                font=FONTS["caption"],
                fg=COLORS["accent"],
                bg=COLORS["card"],
                cursor="hand2",
                anchor="w",
            )
        link.pack(side=tk.LEFT, padx=(6, 0))
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
            self.root.minsize(min(1040, max_w), min(740, max_h))
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
        if self._naver_busy or self._settings_busy:
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
            messagebox.showwarning(title, "적용할 블로그를 선택해 주세요. 왼쪽 체크박스로 여러 개를 고를 수 있습니다.")
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
        ):
            btn.configure(state=state)

    def on_naver_html_insert(self):
        blogs = self._selected_blogs("네이버 최초 HTML 코드 넣기")
        if not blogs:
            return
        jobs = [(blog.id, blog.address) for blog in blogs]
        self._start_naver_job(2 * len(jobs), "네이버 최초 HTML 코드 넣기", self._naver_html_worker, jobs)

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
        blogs = self._selected_blogs("블로그 수집요청")
        if not blogs:
            return
        jobs = [(blog.id, blog.address) for blog in blogs]
        self._start_naver_job(len(jobs), "블로그 수집요청", self._naver_blog_worker, jobs)

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

    def _naver_html_worker(self, jobs: list[tuple[str, str]]):
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

                def inject_theme(snippet: str, target=blog_id):
                    self.session.inject_theme_head(target, snippet)

                try:
                    self.naver.insert_verify_html(
                        address,
                        inject_theme,
                        blog_id=blog_id,
                        control=self._run_control,
                        on_progress=self._offset_progress((index - 1) * 2, grand, prefix),
                        on_item_done=self._on_item_done,
                    )
                    self.log(f"테마에 HTML 코드를 넣었습니다: {name}")
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

    def _naver_blog_worker(self, jobs: list[tuple[str, str]]):
        warnings: list[str] = []
        try:
            for index, (blog_id, address) in enumerate(jobs, 1):
                self._run_control.checkpoint()
                prefix = f"{index}/{len(jobs)} · " if len(jobs) > 1 else ""
                self.log(f"블로그 수집요청: {address}")
                self.naver.read_account()
                self._remember_naver_id(blog_id)
                self.naver.control = self._run_control
                self.naver._on_progress = self._offset_progress(index - 1, len(jobs), prefix)
                self.naver._on_item_done = self._on_item_done
                try:
                    self.naver.request_blog_crawl(address, blog_id=blog_id)
                    self._on_settings_progress(index, len(jobs), f"{prefix}블로그 수집")
                except StopRequested:
                    raise
                except Exception as exc:
                    detail = _exc_text(exc)
                    self.log(f"블로그 수집요청 오류: {address} · {detail}")
                    warnings.append(f"{address}: {detail}")
            self.log("블로그 수집요청을 마쳤습니다.")
            self.root.after(0, lambda: self._apply_state(self.session.state))
            if warnings:
                text = "\n".join(warnings[:8])
                self.root.after(0, lambda m=text: messagebox.showwarning("블로그 수집요청", m))
        except StopRequested:
            self.log("블로그 수집요청을 중지했습니다.")
        except Exception as exc:
            detail = _exc_text(exc)
            self.log(f"블로그 수집요청 오류: {detail}")
            self.root.after(0, lambda m=detail: messagebox.showerror("블로그 수집요청", m))
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
        if not self._settings_busy and not self._naver_busy:
            return
        if self._paused:
            self._paused = False
            self._run_control.request_resume()
            self.pause_btn.configure(text="일시정지")
            self.log("설정을 계속합니다.")
        else:
            self._paused = True
            self._run_control.request_pause()
            self.pause_btn.configure(text="계속")
            self.log("설정을 일시정지했습니다.")

    def on_stop_settings(self):
        if not self._settings_busy and not self._naver_busy:
            return
        self._run_control.request_stop()
        self._paused = False
        self.pause_btn.configure(text="일시정지")
        self.log("설정 중지를 요청했습니다.")

    def _settings_done(self):
        self._settings_busy = False
        self._paused = False
        self.settings_btn.configure(state="normal")
        self._set_naver_buttons(True)
        self._set_run_controls(False)

    def on_write_post(self):
        if self._post_busy:
            return
        if not self.session.is_alive() or not self.session.state.logged_in:
            messagebox.showwarning("글 작성", "먼저 블로그스팟에 로그인해 주세요.")
            return
        blog_id = self.blog_var.get().strip()
        if not blog_id:
            messagebox.showwarning("글 작성", "작성할 블로그 이름을 눌러 포커스해 주세요.")
            return
        title = self._get_title().strip()
        body = self._get_body().strip()
        if not title or not body:
            messagebox.showwarning("글 작성", "제목과 본문을 모두 입력해 주세요.")
            return
        self._post_busy = True
        self.post_btn.configure(state="disabled")
        publish = bool(self.publish_var.get())
        threading.Thread(
            target=self._write_worker,
            args=(blog_id, title, body, publish),
            daemon=True,
        ).start()

    def _write_worker(self, blog_id: str, title: str, body: str, publish: bool):
        try:
            blog = next((item for item in self.session.state.blogs if item.id == blog_id), None)
            name = blog.name if blog else blog_id
            self.log(f"글 작성 시작: [{name}] {title}")
            self.session.open_blog_posts(blog_id)
            self.session.click_new_post()
            ok = self.session.fill_post(title, body, publish=publish)
            if ok and publish:
                post_url = self.session.wait_and_read_post_url(blog_id)
                if post_url:
                    count = 0
                    if blog:
                        count = len(blog.posts)
                    extra = f" · 글 {count}개" if count else ""
                    self.log(f"글 주소 인식: {post_url}{extra}")
                    self.root.after(0, lambda: self._apply_state(self.session.state))
                else:
                    self.log("게시는 했지만 글 주소를 아직 찾지 못했습니다. 글 목록에서 다시 인식합니다.")
            if ok:
                self.log("글 작성을 마쳤습니다.")
            else:
                self.log("편집기 입력을 완료하지 못했습니다. 브라우저에서 이어서 작성해 주세요.")
        except Exception as exc:
            self.log(f"글 작성 오류: {exc}")
            self.root.after(0, lambda: messagebox.showerror("글 작성", str(exc)))
        finally:
            self.root.after(0, self._write_done)

    def _write_done(self):
        self._post_busy = False
        self.post_btn.configure(state="normal")

    def _get_title(self) -> str:
        return self.title_entry.get()

    def _get_body(self) -> str:
        return self._textbox_get(self.body_text)

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
        busy = (
            self._settings_busy
            or self._post_busy
            or self._naver_busy
            or self._naver_login_busy
            or self._login_busy
        )
        if not busy:
            if self.session.driver is not None and not self.session.is_alive():
                self._on_browser_closed()
            naver_dead = self.naver.driver is not None and not self.naver.is_alive()
            naver_missing = self.naver.driver is None and self.naver.chrome_running()
            if naver_dead or naver_missing:
                if self.naver.chrome_running() and self.naver.reattach():
                    self._apply_naver_state(self.naver.state)
                elif not self.naver.chrome_running():
                    self._on_naver_closed()
        if (
            not busy
            and self.session.is_alive()
        ):
            try:
                state = self.session.detect()
                if state.logged_in:
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
                        self._apply_state(state)
            except Exception:
                pass
        self._watch_id = self.root.after(2000, self._watch)

    def _on_browser_closed(self):
        self._login_busy = False
        self._settings_busy = False
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

    def _on_close(self):
        try:
            self._save_local_settings()
        except Exception:
            pass
        if self._watch_id is not None:
            self.root.after_cancel(self._watch_id)
        self.session.close()
        self.naver.close(kill_chrome=True)
        self.root.destroy()
