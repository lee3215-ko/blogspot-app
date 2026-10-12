"""Blog list ScrollFrame geometry checks. Not imported by the app."""
import sys
import tkinter as tk
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from ui_theme import COLORS, ScrollFrame  # noqa: E402


def _rows(parent, count):
    items = []
    wrap = tk.Frame(parent, bg=COLORS["card"])
    wrap.pack(side=tk.TOP, anchor="nw", fill=tk.X)
    for i in range(count):
        row = tk.Frame(wrap, bg="#c7d2fe", highlightbackground="#3730a3", highlightthickness=1)
        row.pack(side=tk.TOP, anchor="nw", fill=tk.X, pady=3, padx=2)
        tk.Label(row, text=f"row {i}", bg="#c7d2fe", font=("Malgun Gothic", 13, "bold")).pack(
            anchor="w", padx=8, pady=8
        )
        items.append(row)
    return wrap, items


def _geom(sf, rows):
    sf._commit_span()
    sf.update_idletasks()
    first = rows[0].winfo_rooty() - sf._canvas.winfo_rooty() if rows else None
    visible = [
        i
        for i, row in enumerate(rows)
        if 0 <= (row.winfo_rooty() - sf._canvas.winfo_rooty()) < sf._canvas.winfo_height()
        and row.winfo_manager()
    ]
    region = sf._canvas.cget("scrollregion")
    return {
        "canvas": (sf._canvas.winfo_width(), sf._canvas.winfo_height()),
        "inner_h": sf.inner.winfo_height(),
        "req_h": sf.inner.winfo_reqheight(),
        "win_h": sf._canvas.itemcget(sf._win, "height"),
        "region": region,
        "yview": sf._canvas.yview(),
        "first_y": first,
        "visible": visible,
        "content": sf._content,
        "view": sf._view,
        "offset": sf._offset,
    }


def _fail(name, msg):
    raise SystemExit(f"FAIL {name}: {msg}")


def main():
    root = tk.Tk()
    root.geometry("900x700")
    sf = ScrollFrame(root, height=420, bg=COLORS["card"])
    sf.pack(fill=tk.BOTH, expand=True, padx=16, pady=14)
    wrap, rows = _rows(sf.inner, 19)
    root.update()
    root.update_idletasks()
    g = _geom(sf, rows)
    if g["first_y"] is None or g["first_y"] > 20:
        _fail("stack19", f"first row y={g['first_y']} geom={g}")
    if len(g["visible"]) < 5:
        _fail("stack19", f"visible={g['visible']} geom={g}")
    if g["req_h"] < 800:
        _fail("stack19", f"req_h too small {g}")

    sf._offset = 900
    sf.scroll_to_widget(rows[10])
    root.update_idletasks()
    g = _geom(sf, rows)
    if 10 not in g["visible"]:
        _fail("reveal10", f"row 10 not in view {g}")
    if g["visible"][0] == 10 and len(g["visible"]) == 1:
        _fail("reveal10", f"centered onto a single row {g}")

    for row in rows:
        if row is not rows[10]:
            row.pack_forget()
    root.update_idletasks()
    sf._offset = 900
    sf._commit_span()
    root.update_idletasks()
    g = _geom(sf, [rows[10]])
    if g["first_y"] is None or g["first_y"] > 20:
        _fail("forget18", f"remaining row y={g['first_y']} geom={g}")
    if g["req_h"] > 120:
        _fail("forget18", f"scroll region still tall {g}")
    if float(g["yview"][0]) > 0.02:
        _fail("forget18", f"still scrolled {g}")

    sf.scroll_to_widget(rows[10])
    root.update_idletasks()
    g = _geom(sf, [rows[10]])
    if g["first_y"] is None or g["first_y"] > 20:
        _fail("noscroll1", f"single row moved to y={g['first_y']} geom={g}")

    root.destroy()
    print("PASS blog list scroll geometry")


if __name__ == "__main__":
    main()
