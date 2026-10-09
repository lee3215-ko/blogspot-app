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


RESIZE_FROZEN = False


def set_resize_frozen(value: bool) -> None:
    global RESIZE_FROZEN
    RESIZE_FROZEN = bool(value)


def frame(parent, bg=None, **kwargs):
    bg = bg or COLORS["bg"]
    kwargs.pop("fg_color", None)
    kwargs.pop("corner_radius", None)
    return tk.Frame(parent, bg=bg, **kwargs)


class ScrollFrame(tk.Frame):
    """스크롤 영역. 자식은 `.inner`에 넣는다.

    창 크기가 바뀌는 동안에는 안쪽 너비를 바로 맞추지 않는다.
    손 뗀 뒤에 한 번만 재서 맞추면, 줄마다 Configure가 이어지지 않는다.
    """

    def __init__(self, parent, height: int = 200, bg=None, orientation: str = "vertical"):
        bg = bg or COLORS["card"]
        super().__init__(parent, bg=bg, height=height)
        self.orientation = orientation
        self._offset = 0.0
        self._applying = False
        self._content = 1
        self._view = 1
        self._span = 1
        self._resize_after = None
        self._measure_after = None
        self._span_ready = False
        self._host = tk.Frame(self, bg=bg, highlightthickness=0, bd=0)
        if orientation == "horizontal":
            self.bar = tk.Scrollbar(self, orient="horizontal", command=self._on_bar)
            self._host.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
            self.bar.pack(side=tk.BOTTOM, fill=tk.X)
        else:
            self.bar = tk.Scrollbar(self, orient="vertical", command=self._on_bar)
            self._host.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            self.bar.pack(side=tk.RIGHT, fill=tk.Y)
        self.inner = tk.Frame(self._host, bg=bg)
        self.inner.place(x=0, y=0)
        try:
            self.pack_propagate(False)
        except Exception:
            pass
        try:
            self._host.pack_propagate(False)
        except Exception:
            pass
        self.inner.bind("<Configure>", self._on_inner_configure)
        self._host.bind("<Configure>", self._on_host_configure)
        self._scroll_target = self
        self._host._scroll_target = self
        self.inner._scroll_target = self
        self.after(1, self._commit_span)

    def _cancel_after(self, name: str) -> None:
        job = getattr(self, name, None)
        if job is None:
            return
        setattr(self, name, None)
        try:
            self.after_cancel(job)
        except Exception:
            pass

    def _measure_content(self) -> int:
        try:
            if self.orientation == "horizontal":
                value = max(1, int(self.inner.winfo_reqwidth() or 1))
            else:
                value = max(1, int(self.inner.winfo_reqheight() or 1))
        except tk.TclError:
            value = self._content
        self._content = value
        return value

    def _place_offset(self) -> None:
        try:
            if self.orientation == "horizontal":
                self.inner.place_configure(x=int(-self._offset))
            else:
                self.inner.place_configure(y=int(-self._offset))
        except tk.TclError:
            pass

    def _sync_bar(self) -> None:
        content = max(1, int(self._content))
        view = max(1, int(self._view))
        try:
            if content <= view:
                self.bar.set(0, 1)
            else:
                self.bar.set(self._offset / content, (self._offset + view) / content)
        except tk.TclError:
            pass

    def _apply_offset(self) -> None:
        if self._applying:
            return
        self._applying = True
        try:
            content = max(1, int(self._content))
            view = max(1, int(self._view))
            max_off = max(0, content - view)
            self._offset = min(max(0.0, float(self._offset)), float(max_off))
            self._place_offset()
            self._sync_bar()
        finally:
            self._applying = False

    def _commit_span(self) -> None:
        self._resize_after = None
        try:
            if self.orientation == "horizontal":
                span = max(1, int(self._host.winfo_height() or 1))
                view = max(1, int(self._host.winfo_width() or 1))
                self.inner.place_configure(height=span)
            else:
                span = max(1, int(self._host.winfo_width() or 1))
                view = max(1, int(self._host.winfo_height() or 1))
                self.inner.place_configure(width=span)
        except tk.TclError:
            return
        self._span = span
        self._view = view
        self._span_ready = True
        self._measure_content()
        self._apply_offset()

    def _on_host_configure(self, event=None) -> None:
        if RESIZE_FROZEN:
            return
        try:
            if not self.winfo_ismapped():
                return
        except tk.TclError:
            return
        if self.orientation == "horizontal":
            view = max(1, int(getattr(event, "width", 0) or self._host.winfo_width() or 1))
            span = max(1, int(getattr(event, "height", 0) or self._host.winfo_height() or 1))
        else:
            view = max(1, int(getattr(event, "height", 0) or self._host.winfo_height() or 1))
            span = max(1, int(getattr(event, "width", 0) or self._host.winfo_width() or 1))
        self._view = view
        max_off = max(0, self._content - view)
        if self._offset > max_off:
            self._offset = float(max_off)
            self._place_offset()
        self._sync_bar()
        if not self._span_ready:
            self._commit_span()
            return
        if span == self._span:
            return
        self._cancel_after("_resize_after")
        try:
            self._resize_after = self.after(80, self._commit_span)
        except Exception:
            self._commit_span()

    def _on_inner_configure(self, _event=None) -> None:
        if RESIZE_FROZEN:
            return
        if self._measure_after is not None:
            return
        try:
            self._measure_after = self.after_idle(self._measure_from_idle)
        except Exception:
            self._measure_from_idle()

    def _measure_from_idle(self) -> None:
        self._measure_after = None
        self._measure_content()
        self._apply_offset()

    def _on_bar(self, *args) -> None:
        if not args:
            return
        content = max(1, int(self._content))
        view = max(1, int(self._view))
        if args[0] == "moveto":
            try:
                self._offset = float(args[1]) * content
            except (TypeError, ValueError):
                return
        elif args[0] == "scroll":
            try:
                amount = int(float(args[1]))
            except (TypeError, ValueError):
                return
            unit = args[2] if len(args) > 2 else "units"
            self._offset += amount * (30 if unit == "units" else view)
        else:
            return
        self._apply_offset()

    def scroll(self, units: int, horizontal: bool = False) -> None:
        if not units:
            return
        self._offset += units * 90
        self._apply_offset()

    def scroll_to_end(self) -> None:
        self._measure_content()
        self._offset = float(self._content)
        self._apply_offset()

    def scroll_to_widget(self, widget) -> None:
        if widget is None:
            return
        try:
            self.update_idletasks()
            self._measure_content()
            view = max(1, int(self._view))
            if self._content <= view:
                self._offset = 0
                self._apply_offset()
                return
            top = int(widget.winfo_rooty()) - int(self.inner.winfo_rooty())
            row_h = max(1, int(widget.winfo_height()))
            self._offset = top + (row_h / 2) - (view / 2)
            self._apply_offset()
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


def text_entry(parent, textvariable=None, **kwargs):
    """창 너비를 따라가는 입력칸. CTkEntry 캔버스는 리사이즈마다 다시 그린다."""
    kwargs.pop("height", None)
    kwargs.pop("fg_color", None)
    kwargs.pop("border_color", None)
    kwargs.pop("text_color", None)
    kwargs.pop("placeholder_text", None)
    kwargs.pop("corner_radius", None)
    font = kwargs.pop("font", FONTS["body"])
    return tk.Entry(
        parent,
        textvariable=textvariable,
        font=font,
        bg=COLORS["input_bg"],
        fg=COLORS["text"],
        relief="flat",
        highlightthickness=1,
        highlightbackground=COLORS["border"],
        highlightcolor=COLORS["accent"],
        insertbackground=COLORS["text"],
        **kwargs,
    )


def install_ctk_resize_guard() -> None:
    """CTk 위젯은 크기가 1px만 바뀌어도 캔버스를 다시 그린다. 손 뗀 뒤에 한 번만 그린다."""
    if ctk is None:
        return
    try:
        from customtkinter.windows.widgets.core_widget_classes.ctk_base_class import CTkBaseClass
    except Exception:
        return

    def _flush(self) -> None:
        self._blogspot_draw_job = None
        try:
            if self.winfo_exists():
                self._draw(no_color_updates=True)
        except Exception:
            pass

    def _update_dimensions_event(self, event) -> None:
        new_w = self._reverse_widget_scaling(event.width)
        new_h = self._reverse_widget_scaling(event.height)
        if round(self._current_width) == round(new_w) and round(self._current_height) == round(new_h):
            return
        self._current_width = new_w
        self._current_height = new_h
        job = getattr(self, "_blogspot_draw_job", None)
        if job is not None:
            try:
                self.after_cancel(job)
            except Exception:
                pass
        try:
            self._blogspot_draw_job = self.after(80, self._blogspot_flush_draw)
        except Exception:
            try:
                self._draw(no_color_updates=True)
            except Exception:
                pass

    CTkBaseClass._blogspot_flush_draw = _flush
    CTkBaseClass._update_dimensions_event = _update_dimensions_event


install_ctk_resize_guard()


def label(parent, text, font_key="body", color=None, **kwargs):
    color = color or COLORS["text"]
    kwargs.pop("text_color", None)
    kwargs.pop("fg_color", None)
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
    kwargs.setdefault("padx", 8)
    kwargs.setdefault("pady", 3)
    return tk_pill(parent, text, tone, **kwargs)


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


class LightButton(tk.Frame):
    """픽셀 크기의 버튼. 캔버스가 없어서 창 크기 조절 때 다시 그리지 않는다."""

    def __init__(self, parent, text, variant="primary", width=120, height=40, command=None):
        fg, hover, tc = BUTTON_STYLES.get(variant, BUTTON_STYLES["primary"])
        self._pixel_width = int(width or 120)
        self._pixel_height = int(height or 40)
        super().__init__(
            parent,
            bg=fg,
            width=self._pixel_width,
            height=self._pixel_height,
            highlightthickness=0,
            bd=0,
        )
        try:
            self.pack_propagate(False)
        except Exception:
            pass
        self._command = command
        self._fg = fg
        self._hover = hover
        self._tc = tc
        self._state = "normal"
        self._inside = False
        self._label = tk.Label(
            self,
            text=text,
            bg=fg,
            fg=tc,
            font=FONTS["body_bold"],
            cursor="hand2",
        )
        self._label.pack(fill=tk.BOTH, expand=True)
        for widget in (self, self._label):
            widget.bind("<Enter>", self._on_enter)
            widget.bind("<Leave>", self._on_leave)
            widget.bind("<Button-1>", self._on_click)

    def cget(self, key):
        if key == "width":
            return self._pixel_width
        if key == "height":
            return self._pixel_height
        if key == "text":
            return self._label.cget("text")
        if key == "state":
            return self._state
        return tk.Frame.cget(self, key)

    def configure(self, **kwargs):
        if "text" in kwargs:
            self._label.configure(text=kwargs.pop("text"))
        if "state" in kwargs:
            self._state = str(kwargs.pop("state") or "normal")
        if "command" in kwargs:
            self._command = kwargs.pop("command")
        if "width" in kwargs:
            self._pixel_width = int(kwargs.pop("width"))
            tk.Frame.configure(self, width=self._pixel_width)
        if "height" in kwargs:
            self._pixel_height = int(kwargs.pop("height"))
            tk.Frame.configure(self, height=self._pixel_height)
        if "fg_color" in kwargs:
            self._fg = kwargs.pop("fg_color")
        elif "bg" in kwargs:
            self._fg = kwargs.pop("bg")
        if "hover_color" in kwargs:
            self._hover = kwargs.pop("hover_color")
        if "text_color" in kwargs:
            self._tc = kwargs.pop("text_color")
        elif "fg" in kwargs:
            self._tc = kwargs.pop("fg")
        kwargs.pop("font", None)
        kwargs.pop("corner_radius", None)
        kwargs.pop("border_width", None)
        kwargs.pop("border_color", None)
        if kwargs:
            tk.Frame.configure(self, **kwargs)
        self._paint()

    config = configure

    def _paint(self) -> None:
        disabled = self._state == "disabled"
        if disabled:
            bg, fg, cursor = "#cbd5e1", "#64748b", "arrow"
        elif self._inside:
            bg, fg, cursor = self._hover, self._tc, "hand2"
        else:
            bg, fg, cursor = self._fg, self._tc, "hand2"
        tk.Frame.configure(self, bg=bg)
        self._label.configure(bg=bg, fg=fg, cursor=cursor)

    def _on_enter(self, _event=None):
        self._inside = True
        self._paint()

    def _on_leave(self, _event=None):
        self._inside = False
        self._paint()

    def _on_click(self, _event=None):
        if self._state == "disabled" or self._command is None:
            return "break"
        self._command()
        return "break"


def button(parent, text, variant="primary", width=None, height=40, command=None):
    return LightButton(parent, text, variant=variant, width=width or 120, height=height or 40, command=command)
