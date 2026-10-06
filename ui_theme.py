"""UI 토큰과 공통 위젯."""
import time
import tkinter as tk

try:
    import customtkinter as ctk
except ImportError:
    ctk = None

COLORS = {
    "bg": "#e8eef6",
    "card": "#ffffff",
    "card_border": "#c5d0de",
    "text": "#0b1220",
    "text_muted": "#334155",
    "text_light": "#64748b",
    "accent": "#4f46e5",
    "accent_hover": "#4338ca",
    "accent_light": "#eef2ff",
    "danger": "#ef4444",
    "danger_hover": "#dc2626",
    "success": "#059669",
    "success_hover": "#047857",
    "warning": "#d97706",
    "warning_hover": "#b45309",
    "border": "#cbd5e1",
    "input_bg": "#f8fafc",
    "log_bg": "#0f172a",
    "log_fg": "#e2e8f0",
    "ok_bg": "#d1fae5",
    "wait_bg": "#fde68a",
    "chip_bg": "#e2e8f0",
    "row_selected": "#c7d2fe",
    "row_checked": "#93c5fd",
    "row_checked_border": "#1d4ed8",
    "row_focus": "#a5b4fc",
    "row_focus_border": "#3730a3",
}

FONT_FAMILY = "맑은 고딕"
FONTS = {
    "title": (FONT_FAMILY, 22, "bold"),
    "heading": (FONT_FAMILY, 15, "bold"),
    "subheading": (FONT_FAMILY, 12, "bold"),
    "body": (FONT_FAMILY, 13),
    "body_bold": (FONT_FAMILY, 13, "bold"),
    "small": (FONT_FAMILY, 11),
    "small_bold": (FONT_FAMILY, 11, "bold"),
    "caption": (FONT_FAMILY, 10),
    "log": ("Consolas", 11),
}

PILL_TONES = {
    "ok": ("#047857", "#d1fae5"),
    "wait": ("#b45309", "#fde68a"),
    "off": ("#334155", "#e2e8f0"),
    "info": ("#4f46e5", "#eef2ff"),
    "danger": ("#b91c1c", "#fee2e2"),
}

BUTTON_STYLES = {
    "primary": ("#4f46e5", "#4338ca", "#ffffff"),
    "danger": ("#ef4444", "#dc2626", "#ffffff"),
    "success": ("#059669", "#047857", "#ffffff"),
    "warning": ("#d97706", "#b45309", "#ffffff"),
    "ghost": ("#e2e8f0", "#cbd5e1", "#0f172a"),
}


def frame(parent, bg=None, **kwargs):
    bg = bg or COLORS["bg"]
    if ctk:
        return ctk.CTkFrame(parent, fg_color=bg, corner_radius=0, **kwargs)
    return tk.Frame(parent, bg=bg)


class ScrollFrame(tk.Frame):
    """스크롤 영역. 자식은 `.inner`에 넣는다.

    휠 이벤트는 위젯마다 받지 않고 `install_wheel_dispatch`가 창 전체에서 한 번만 받아
    마우스 아래의 ScrollFrame으로 넘긴다. 그래서 목록을 아무리 다시 만들어도 핸들러가 쌓이지 않는다.
    """

    def __init__(self, parent, height: int = 200, bg=None, orientation: str = "vertical"):
        bg = bg or COLORS["card"]
        super().__init__(parent, bg=bg)
        self.orientation = orientation
        self.canvas = tk.Canvas(
            self, bg=bg, highlightthickness=0, borderwidth=0, height=height,
            yscrollincrement=30, xscrollincrement=30,
        )
        self.inner = tk.Frame(self.canvas, bg=bg)
        self._window = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        if orientation == "horizontal":
            self.bar = tk.Scrollbar(self, orient="horizontal", command=self.canvas.xview)
            self.canvas.configure(xscrollcommand=self.bar.set)
            self.canvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
            self.bar.pack(side=tk.BOTTOM, fill=tk.X)
        else:
            self.bar = tk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
            self.canvas.configure(yscrollcommand=self.bar.set)
            self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            self.bar.pack(side=tk.RIGHT, fill=tk.Y)
        self.inner.bind("<Configure>", self._on_inner_resize)
        self.canvas.bind("<Configure>", self._on_canvas_resize)
        # 휠 디스패처가 위로 올라오며 찾는 표식
        self._scroll_target = self
        self.canvas._scroll_target = self
        self.inner._scroll_target = self

    def _on_inner_resize(self, _event=None) -> None:
        bbox = self.canvas.bbox("all")
        if bbox:
            self.canvas.configure(scrollregion=bbox)

    def _on_canvas_resize(self, event) -> None:
        if self.orientation == "horizontal":
            self.canvas.itemconfigure(self._window, height=max(1, event.height))
        else:
            self.canvas.itemconfigure(self._window, width=max(1, event.width))

    def scroll(self, units: int, horizontal: bool = False) -> None:
        if not units:
            return
        try:
            if horizontal or self.orientation == "horizontal":
                self.canvas.xview_scroll(units * 3, "units")
            else:
                self.canvas.yview_scroll(units * 3, "units")
        except tk.TclError:
            pass

    def scroll_to_end(self) -> None:
        try:
            if self.orientation == "horizontal":
                self.canvas.xview_moveto(1.0)
            else:
                self.canvas.yview_moveto(1.0)
        except tk.TclError:
            pass

    def scroll_to_widget(self, widget) -> None:
        if widget is None:
            return
        try:
            self.update_idletasks()
            bbox = self.canvas.bbox("all")
            if bbox:
                self.canvas.configure(scrollregion=bbox)
            else:
                bbox = (0, 0, 0, max(1, int(self.inner.winfo_reqheight() or 1)))
            scroll_h = max(1, int(bbox[3] - bbox[1]))
            view_h = max(1, int(self.canvas.winfo_height()))
            if scroll_h <= view_h:
                self.canvas.yview_moveto(0)
                return
            top = int(widget.winfo_rooty()) - int(self.inner.winfo_rooty())
            row_h = max(1, int(widget.winfo_height()))
            y = top + (row_h / 2) - (view_h / 2)
            y = max(0.0, min(float(scroll_h - view_h), y))
            self.canvas.yview_moveto(y / float(scroll_h))
        except Exception:
            pass


# 자기 휠을 직접 처리하는 위젯. 이 위에서는 디스패처가 손대지 않는다.
_NATIVE_WHEEL_CLASSES = {"Treeview", "Text", "Listbox", "TCombobox", "Spinbox", "TSpinbox"}


def install_wheel_dispatch(root, on_wheel=None) -> None:
    """창 전체 휠 핸들러를 하나만 설치한다. 다시 불러도 이전 것은 지우고 새로 하나만 둔다."""
    for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        try:
            root.unbind_all(sequence)
        except tk.TclError:
            pass
    for funcid in getattr(root, "_wheel_funcids", None) or []:
        try:
            root.deletecommand(funcid)
        except Exception:
            pass

    def _dispatch(event):
        try:
            node = root.winfo_containing(event.x_root, event.y_root)
        except Exception:
            # 파이썬이 모르는 Tk 창(콤보박스 펼침 목록 등) 위에서는 손대지 않는다.
            return
        if on_wheel is not None:
            try:
                on_wheel()
            except Exception:
                pass
        if getattr(event, "num", 0) == 4:
            units = -1
        elif getattr(event, "num", 0) == 5:
            units = 1
        else:
            delta = int(getattr(event, "delta", 0) or 0)
            if not delta:
                return
            units = -1 if delta > 0 else 1
        horizontal = bool(int(getattr(event, "state", 0) or 0) & 0x0001)
        depth = 0
        while node is not None and depth < 40:
            target = getattr(node, "_scroll_target", None)
            if target is not None:
                target.scroll(units, horizontal)
                return
            try:
                if node.winfo_class() in _NATIVE_WHEEL_CLASSES:
                    return
            except Exception:
                return
            node = getattr(node, "master", None)
            depth += 1

    ids = []
    for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        try:
            ids.append(root.bind_all(sequence, _dispatch))
        except tk.TclError:
            pass
    root._wheel_funcids = ids


def sheet_scroll(parent, height: int, bg=None):
    return ScrollFrame(parent, height=height, bg=bg)


def light_scroll(parent, height: int, bg=None):
    return ScrollFrame(parent, height=height, bg=bg)


def scrollable(parent, height: int, bg=None, orientation: str = "vertical"):
    return ScrollFrame(parent, height=height, bg=bg, orientation=orientation)


def card(parent):
    if ctk:
        return ctk.CTkFrame(
            parent,
            fg_color=COLORS["card"],
            corner_radius=14,
            border_width=1,
            border_color=COLORS["card_border"],
        )
    return tk.Frame(
        parent,
        bg=COLORS["card"],
        highlightbackground=COLORS["card_border"],
        highlightthickness=1,
    )


def _parent_bg(parent):
    if ctk and isinstance(parent, ctk.CTkFrame):
        return parent.cget("fg_color")
    try:
        return parent.cget("bg")
    except tk.TclError:
        return COLORS["card"]


def label(parent, text, font_key="body", color=None, **kwargs):
    color = color or COLORS["text"]
    if ctk:
        return ctk.CTkLabel(
            parent, text=text, font=FONTS[font_key], text_color=color, **kwargs
        )
    return tk.Label(
        parent,
        text=text,
        font=FONTS[font_key],
        bg=_parent_bg(parent),
        fg=color,
        **kwargs,
    )


def tk_pill(parent, text, tone="off", **kwargs):
    """가벼운 알약 라벨. 목록 줄처럼 많이 그리는 곳에서 쓴다. 줄 색을 칠할 때 바탕색을 건드리지 않는다."""
    fg, bg = PILL_TONES.get(tone, PILL_TONES["off"])
    kwargs.setdefault("padx", 8)
    kwargs.setdefault("pady", 2)
    widget = tk.Label(parent, text=text, font=FONTS["small"], fg=fg, bg=bg, **kwargs)
    widget._keep_bg = True
    widget._pill_tone = tone
    return widget


def set_pill_tone(widget, text=None, tone=None) -> None:
    try:
        if tone is not None:
            fg, bg = PILL_TONES.get(tone, PILL_TONES["off"])
            widget.configure(fg=fg, bg=bg)
            widget._pill_tone = tone
        if text is not None:
            widget.configure(text=text)
    except tk.TclError:
        pass


def flat_button(parent, text, variant="ghost", command=None, font_key="small_bold", padx=10, pady=4, **kwargs):
    """캔버스 없는 가벼운 버튼. 목록 줄마다 넣어도 스크롤이 무거워지지 않는다."""
    base, hover, fg = BUTTON_STYLES.get(variant, BUTTON_STYLES["ghost"])
    widget = tk.Label(
        parent, text=text, font=FONTS.get(font_key, FONTS["small_bold"]), fg=fg, bg=base,
        padx=padx, pady=pady, cursor="hand2", **kwargs,
    )
    widget._keep_bg = True
    widget._base_bg = base
    widget._hover_bg = hover

    def _enter(_event=None):
        if str(widget.cget("state")) != "disabled":
            widget.configure(bg=hover)

    def _leave(_event=None):
        widget.configure(bg=base)

    def _click(_event=None):
        if str(widget.cget("state")) == "disabled":
            return "break"
        if command is not None:
            command()
        return "break"

    widget.bind("<Enter>", _enter)
    widget.bind("<Leave>", _leave)
    widget.bind("<Button-1>", _click)
    return widget


def pill(parent, text, tone="off", **kwargs):
    tones = {
        "ok": (COLORS["success"], COLORS["ok_bg"]),
        "wait": ("#b45309", COLORS["wait_bg"]),
        "off": (COLORS["text_muted"], COLORS["chip_bg"]),
        "info": (COLORS["accent"], COLORS["accent_light"]),
    }
    fg, bg = tones.get(tone, tones["off"])
    if ctk:
        return ctk.CTkLabel(
            parent,
            text=text,
            font=FONTS["small"],
            text_color=fg,
            fg_color=bg,
            corner_radius=8,
            height=24,
            **kwargs,
        )
    return tk.Label(
        parent,
        text=text,
        font=FONTS["small"],
        fg=fg,
        bg=bg,
        padx=8,
        pady=3,
        **kwargs,
    )


class HoverPopup:
    def __init__(self, root):
        self.root = root
        self._win = None
        self._after = None
        self._widget = None
        self._blocked_until = 0.0

    def bind(self, widget, lines):
        widget.bind("<Enter>", lambda _e, w=widget, rows=lines: self._on_enter(w, rows), add="+")
        widget.bind("<Leave>", lambda _e: self.hide(), add="+")
        widget.bind("<Destroy>", lambda _e: self.hide(), add="+")
        try:
            widget.configure(cursor="hand2")
        except Exception:
            pass

    def hide(self) -> None:
        if self._after is not None and self._widget is not None:
            try:
                self._widget.after_cancel(self._after)
            except Exception:
                pass
        self._after = None
        self._widget = None
        if self._win is not None:
            try:
                self._win.destroy()
            except Exception:
                pass
            self._win = None

    def suppress(self, seconds: float = 0.4) -> None:
        self.hide()
        self._blocked_until = time.time() + max(0.0, seconds)

    def _on_enter(self, widget, lines) -> None:
        if time.time() < getattr(self, "_blocked_until", 0):
            return
        self.hide()
        self._widget = widget
        self._after = widget.after(180, lambda: self._show(widget, lines))

    def _show(self, widget, lines) -> None:
        self._after = None
        try:
            if not widget.winfo_exists():
                return
        except Exception:
            return
        rows = lines() if callable(lines) else lines
        if not rows:
            return
        if time.time() < getattr(self, "_blocked_until", 0):
            return
        win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        try:
            win.attributes("-topmost", True)
        except Exception:
            pass
        outer = tk.Frame(win, bg=COLORS["card_border"], padx=1, pady=1)
        outer.pack()
        box = tk.Frame(outer, bg=COLORS["card"], padx=12, pady=10)
        box.pack()
        for color, text, font_key in rows:
            tk.Label(
                box,
                text=text,
                font=FONTS.get(font_key, FONTS["body"]),
                fg=color,
                bg=COLORS["card"],
                anchor="w",
                justify="left",
            ).pack(anchor="w")
        win.update_idletasks()
        x = widget.winfo_rootx()
        y = widget.winfo_rooty() + widget.winfo_height() + 8
        ww = win.winfo_reqwidth()
        hh = win.winfo_reqheight()
        screen_w = widget.winfo_screenwidth()
        screen_h = widget.winfo_screenheight()
        if x + ww > screen_w - 16:
            x = max(8, screen_w - ww - 16)
        if y + hh > screen_h - 48:
            y = widget.winfo_rooty() - hh - 8
        win.geometry(f"+{x}+{y}")
        win.deiconify()
        self._win = win


def button(parent, text, variant="primary", width=None, height=40, command=None):
    fg, hover, tc = BUTTON_STYLES.get(variant, BUTTON_STYLES["primary"])
    if ctk:
        kw = {
            "text": text,
            "height": height,
            "font": FONTS["body_bold"],
            "fg_color": fg,
            "hover_color": hover,
            "text_color": tc,
            "corner_radius": 10,
            "command": command,
        }
        if width:
            kw["width"] = width
        return ctk.CTkButton(parent, **kw)
    return tk.Button(
        parent,
        text=text,
        bg=fg,
        fg=tc,
        activebackground=hover,
        font=FONTS["body_bold"],
        relief=tk.FLAT,
        command=command,
    )
