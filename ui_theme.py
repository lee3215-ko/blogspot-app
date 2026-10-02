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
    "caption": (FONT_FAMILY, 10),
    "log": ("Consolas", 11),
}


def frame(parent, bg=None, **kwargs):
    bg = bg or COLORS["bg"]
    if ctk:
        return ctk.CTkFrame(parent, fg_color=bg, corner_radius=0, **kwargs)
    return tk.Frame(parent, bg=bg)


def light_scroll(parent, height: int, bg=None):
    bg = bg or COLORS["card"]
    wrap = tk.Frame(parent, bg=bg)
    canvas = tk.Canvas(wrap, bg=bg, highlightthickness=0, height=height, borderwidth=0)
    bar = tk.Scrollbar(wrap, orient="vertical", command=canvas.yview)
    inner = tk.Frame(canvas, bg=bg)
    inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
    window = canvas.create_window((0, 0), window=inner, anchor="nw")

    def _fit(event):
        canvas.itemconfigure(window, width=max(1, event.width))

    canvas.bind("<Configure>", _fit)
    canvas.configure(yscrollcommand=bar.set)
    canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    bar.pack(side=tk.RIGHT, fill=tk.Y)

    def _wheel(event, target=wrap, view=canvas):
        node = target.winfo_containing(event.x_root, event.y_root)
        while node is not None:
            if node is target:
                view.yview_scroll(int(-event.delta / 120), "units")
                return
            node = getattr(node, "master", None)

    wrap.bind_all("<MouseWheel>", _wheel, add="+")
    wrap.inner = inner
    return wrap


def scrollable(parent, height: int, bg=None):
    bg = bg or COLORS["card"]
    if ctk:
        return ctk.CTkScrollableFrame(
            parent,
            fg_color=bg,
            height=height,
            corner_radius=0,
            border_width=0,
        )
    wrap = tk.Frame(parent, bg=bg)
    canvas = tk.Canvas(wrap, bg=bg, highlightthickness=0, height=height)
    bar = tk.Scrollbar(wrap, orient="vertical", command=canvas.yview)
    inner = tk.Frame(canvas, bg=bg)
    inner.bind(
        "<Configure>",
        lambda _e: canvas.configure(scrollregion=canvas.bbox("all")),
    )
    canvas.create_window((0, 0), window=inner, anchor="nw")
    canvas.configure(yscrollcommand=bar.set)
    canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    bar.pack(side=tk.RIGHT, fill=tk.Y)
    wrap.inner = inner
    return wrap


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
    styles = {
        "primary": (COLORS["accent"], COLORS["accent_hover"], "#ffffff"),
        "danger": (COLORS["danger"], COLORS["danger_hover"], "#ffffff"),
        "success": (COLORS["success"], COLORS["success_hover"], "#ffffff"),
        "warning": (COLORS["warning"], COLORS["warning_hover"], "#ffffff"),
        "ghost": ("#e2e8f0", "#cbd5e1", "#0f172a"),
    }
    fg, hover, tc = styles.get(variant, styles["primary"])
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
