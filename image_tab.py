"""
image_tab.py – plugin for the multi-tab editor.

If the opened file is an image, draw it in the graphical (Canvas) panel
and put a short description in the text area.

Viewing:
  toolbar   [-] [Fit] [+] [100%]  zoom %  -- Fit re-fits when the panel resizes
  wheel     zoom in/out around the mouse pointer (while over the image area)
  drag      pan (when the image is larger than the panel)
  dbl-click toggle Fit <-> 100%

With Pillow installed, only the visible part of the image is scaled for
each redraw, so zooming large photos stays quick; JPEG/BMP/WebP/TIFF also
need Pillow. Without it, PNG/GIF/PGM/PPM use Tk's own PhotoImage and
integer zoom/subsample (fine for moderate sizes).

onload() is discovered automatically because this file matches *_tab.py.

setup:
pip install Pillow  #for optional jpeg support (HPND license -- permissive)
"""

from __future__ import annotations

import tkinter as tk
from fractions import Fraction
from pathlib import Path
from tkinter import ttk
from typing import Optional

from utils import debug

IMAGE_EXTS = {".png", ".gif", ".pgm", ".ppm", ".jpg", ".jpeg", ".bmp", ".webp", ".tif", ".tiff"}
FILE_TYPES = [("Images", " ".join(f"*{e}" for e in sorted(IMAGE_EXTS)))]   # File > Open (tracked.py)

# Formats Tk PhotoImage can load without Pillow (Tk 8.6+)
_TK_NATIVE = {".png", ".gif", ".pgm", ".ppm"}

ZOOM_STEP = 1.25
MAX_SCALE = 32.0
SHIFT_MASK = 0x0001


def onload(filepath: str, canvas=None, text=None, tab=None):
    """
    Return a non-false value to claim this file.
    When canvas is provided, draw the image into the graphical panel.
    """
    p = Path(filepath)
    ext = p.suffix.lower()
    if ext not in IMAGE_EXTS:
        debug(1, f"{{red}}{p.resolve()} '{p.suffix.lower()} not image")
        return False   # not handled

    descr = (
        f"{{cyan}}[image_tab]\n"
        f"{{blue}}Image: {{cyan}}{p.name}\n"
        f"{{blue}}Path:  {p.resolve()}\n"
    )

    if canvas is None:
        return True  # probe only (find_create_tab_plugin): claim, draw nothing

    viewer = ImageViewer(canvas, str(p.resolve()), tab=tab)
    canvas._image_viewer = viewer   # keep a reference (and its PhotoImages) alive

    if viewer.source is None:
        descr += (
            f"{{red}}Could not load image into the graphical panel.\n"
            f"{{red}}PNG/GIF work with plain Tk; for JPEG/BMP/WebP install Pillow:\n"
            f"{{red}}  pip install Pillow\n"
        )
    else:
        iw, ih = viewer.image_size
        descr += (
            f"{{green}}Displayed in graphical panel ({iw}\u00d7{ih} px"
            f"{', via Pillow' if viewer.kind == 'pil' else ''}).\n"
            f"{{blue}}Zoom: {{cyan}}toolbar buttons{{blue}}, {{cyan}}mouse wheel{{blue}} over the image, "
            f"{{cyan}}drag{{blue}} to pan, {{cyan}}double-click{{blue}} = Fit / 100%\n"
        )
        if viewer.kind == "tk":
            descr += "{yellow}(install Pillow for smoother zooming of large images)\n"
        if tab is not None:
            tab.min_sash = viewer.min_panel_height
            tab.preferred_sash = viewer.preferred_panel_height
    if tab is not None:
        # The text panel is only a description: never save it over the image.
        tab.protect_file = True

    if text is not None:
        text.delete("1.0", "end")
        from utils import insert_styled_text
        insert_styled_text(text, descr)  #use styled text

    if viewer.source is not None:
        debug(1, f"{{green}}{p.resolve()} image {viewer.image_size[0]}×{viewer.image_size[1]} px")
    return True


class ImageViewer:
    """Draws one image into the tab's canvas with zoom/fit/pan."""

    def __init__(self, canvas, filepath: str, tab=None):
        self.canvas = canvas
        self.filepath = filepath
        self.tab = tab
        self.kind: Optional[str] = None        # "pil" | "tk"
        self.source = None                      # PIL.Image or tk.PhotoImage (unscaled)
        self.image_size = (0, 0)
        self.scale = 1.0
        self.fit = True
        self.cx = self.cy = 0.0                 # image coords shown at the canvas center
        self._photo = None                      # the PhotoImage currently drawn (keep alive)
        self._native_cache = {}                 # Fraction -> scaled tk.PhotoImage
        self._drag = None
        self._redraw_id = None

        self._load()
        self._build_toolbar()
        if self.source is None:
            return
        iw, ih = self.image_size
        self.cx, self.cy = iw / 2.0, ih / 2.0
        self._bind()
        canvas.after(20, self.redraw)

    # ------------------------------------------------------------------ loading
    def _load(self):
        path = self.filepath
        ext = Path(path).suffix.lower()
        try:
            from PIL import Image, ImageOps  # type: ignore
            img = Image.open(path)
            try:
                img = ImageOps.exif_transpose(img)  # honor camera rotation
            except Exception:
                pass
            if img.mode not in ("RGB", "RGBA"):
                img = img.convert("RGBA" if "transparency" in img.info or img.mode in ("LA", "P") else "RGB")
            self.kind, self.source, self.image_size = "pil", img, img.size
            return
        except Exception:
            pass
        if ext in _TK_NATIVE:
            try:
                photo = tk.PhotoImage(file=path, master=self.canvas)
                self.kind, self.source = "tk", photo
                self.image_size = (photo.width(), photo.height())
            except Exception:
                self.source = None

    # ------------------------------------------------------------------ toolbar
    def _build_toolbar(self):
        # Remove a previous plugin's toolbars from this tab's top pane.
        for attr in ("_plugin_toolbars", "_waveform_toolbars"):
            for w in getattr(self.canvas, attr, []) or []:
                try:
                    w.destroy()
                except Exception:
                    pass
            setattr(self.canvas, attr, [])
        self.toolbar = None
        if self.source is None:
            return
        bar = ttk.Frame(self.canvas.master)
        bar.pack(side="top", fill="x", before=self.canvas, pady=(2, 2))
        self.toolbar = bar
        self.canvas._plugin_toolbars = [bar]

        def btn(text, cmd, tip, width=4):
            b = ttk.Button(bar, text=text, width=width, command=cmd)
            b.pack(side="left", padx=(0, 2))
            _Tip(b, tip)
            return b

        btn("\u2212", self.zoom_out, "Zoom out (or mouse wheel down over the image)", 3)
        btn("Fit", self.zoom_fit, "Fit the whole image in the panel")
        btn("+", self.zoom_in, "Zoom in (or mouse wheel up over the image)", 3)
        btn("100%", self.zoom_actual, "Actual size (1 image pixel = 1 screen pixel)", 5)
        self.zoom_var = tk.StringVar(value="")
        ttk.Label(bar, textvariable=self.zoom_var, width=8, anchor="e").pack(side="left", padx=(8, 0))
        iw, ih = self.image_size
        ttk.Label(bar, text=f"{iw}\u00d7{ih} px", foreground="#666666").pack(side="left", padx=(8, 0))

    def _toolbar_height(self):
        try:
            return max(1, self.toolbar.winfo_reqheight()) if self.toolbar is not None else 0
        except tk.TclError:
            return 0

    def min_panel_height(self):
        return self._toolbar_height() + 100

    def preferred_panel_height(self):
        return self._toolbar_height() + max(200, min(self.image_size[1], 480))

    # ------------------------------------------------------------------ events
    def _bind(self):
        c = self.canvas
        # Plain bind (not add="+"): replaces the editor's placeholder grid
        # drawing and any previous plugin's handlers for these events.
        c.bind("<Configure>", lambda e: self._schedule_redraw())
        c.bind("<MouseWheel>", self._on_wheel)          # Windows / macOS
        c.bind("<Button-4>", self._on_wheel)            # X11 wheel up
        c.bind("<Button-5>", self._on_wheel)            # X11 wheel down
        c.bind("<ButtonPress-1>", self._on_press)
        c.bind("<B1-Motion>", self._on_drag)
        c.bind("<ButtonRelease-1>", self._on_release)
        c.bind("<Double-Button-1>", self._on_double)
        c.bind("<Enter>", lambda e: c.focus_set())
        for key, fn in (("<plus>", self.zoom_in), ("<equal>", self.zoom_in), ("<KP_Add>", self.zoom_in),
                        ("<minus>", self.zoom_out), ("<KP_Subtract>", self.zoom_out),
                        ("<Key-0>", self.zoom_fit), ("<Key-1>", self.zoom_actual)):
            c.bind(key, lambda e, fn=fn: fn())

    def _on_wheel(self, event):
        up = getattr(event, "num", None) == 4 or (getattr(event, "delta", 0) or 0) > 0
        self.zoom_by(ZOOM_STEP if up else 1 / ZOOM_STEP, at=(event.x, event.y))
        return "break"

    def _on_press(self, event):
        self._drag = (event.x, event.y, self.cx, self.cy)
        if self._pannable():
            self.canvas.configure(cursor="fleur")

    def _on_drag(self, event):
        if not self._drag or not self._pannable():
            return
        x0, y0, cx0, cy0 = self._drag
        self.cx = cx0 - (event.x - x0) / self.scale
        self.cy = cy0 - (event.y - y0) / self.scale
        self._clamp_center()
        self.redraw()

    def _on_release(self, event):
        self._drag = None
        self.canvas.configure(cursor="")

    def _on_double(self, event):
        if self.fit or abs(self.scale - 1.0) > 1e-6:
            self.zoom_actual(at=(event.x, event.y))
        else:
            self.zoom_fit()

    # ------------------------------------------------------------------ zoom API
    def canvas_size(self):
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w <= 1 or h <= 1:
            try:
                w = int(float(self.canvas.cget("width"))) if w <= 1 else w
                h = int(float(self.canvas.cget("height"))) if h <= 1 else h
            except (tk.TclError, ValueError):
                w, h = 400, 300
        return max(w, 1), max(h, 1)

    def fit_scale(self):
        iw, ih = self.image_size
        cw, ch = self.canvas_size()
        if not iw or not ih:
            return 1.0
        return max(0.001, min(cw / iw, ch / ih))

    def min_scale(self):
        return min(self.fit_scale(), 1.0) / 8.0

    def zoom_in(self):
        self.zoom_by(ZOOM_STEP)

    def zoom_out(self):
        self.zoom_by(1 / ZOOM_STEP)

    def zoom_fit(self):
        self.fit = True
        iw, ih = self.image_size
        self.cx, self.cy = iw / 2.0, ih / 2.0
        self.redraw()

    def zoom_actual(self, at=None):
        self.set_scale(1.0, at=at)

    def zoom_by(self, factor, at=None):
        self.set_scale(self.scale * factor, at=at)

    def set_scale(self, new_scale, at=None):
        """Zoom to new_scale, keeping the image point under `at` (canvas
        x, y -- default: the center) in the same place on screen."""
        if self.source is None:
            return
        new_scale = max(self.min_scale(), min(MAX_SCALE, new_scale))
        cw, ch = self.canvas_size()
        ax, ay = at if at is not None else (cw / 2.0, ch / 2.0)
        # image point under the anchor, before the zoom
        ix = self.cx + (ax - cw / 2.0) / self.scale
        iy = self.cy + (ay - ch / 2.0) / self.scale
        self.fit = False
        self.scale = new_scale
        self.cx = ix - (ax - cw / 2.0) / new_scale
        self.cy = iy - (ay - ch / 2.0) / new_scale
        self._clamp_center()
        self.redraw()

    def _pannable(self):
        iw, ih = self.image_size
        cw, ch = self.canvas_size()
        return iw * self.scale > cw + 1 or ih * self.scale > ch + 1

    def _clamp_center(self):
        """Keep the image from being dragged off screen: if it's larger
        than the panel its edges can't come inside the panel; if smaller
        it stays centered."""
        iw, ih = self.image_size
        cw, ch = self.canvas_size()
        half_w, half_h = cw / 2.0 / self.scale, ch / 2.0 / self.scale
        self.cx = min(max(self.cx, half_w), iw - half_w) if iw * self.scale > cw else iw / 2.0
        self.cy = min(max(self.cy, half_h), ih - half_h) if ih * self.scale > ch else ih / 2.0

    # ------------------------------------------------------------------ drawing
    def _schedule_redraw(self):
        if self._redraw_id is not None:
            try:
                self.canvas.after_cancel(self._redraw_id)
            except (tk.TclError, ValueError):
                pass
        self._redraw_id = self.canvas.after(30, self.redraw)

    def redraw(self):
        self._redraw_id = None
        if self.source is None:
            return
        c = self.canvas
        if self.fit:
            self.scale = self.fit_scale()
            iw, ih = self.image_size
            self.cx, self.cy = iw / 2.0, ih / 2.0
        else:
            self._clamp_center()
        c.delete("plugin_image")
        try:
            if self.kind == "pil":
                self._draw_pil()
            else:
                self._draw_native()
        except Exception as exc:  # never let a draw error break the tab
            debug(1, f"{{red}}image_tab draw error: {exc}")
        self.zoom_var.set(f"{self.scale * 100:.0f}%" + (" (fit)" if self.fit else ""))

    def _draw_pil(self):
        from PIL import Image, ImageTk  # type: ignore
        iw, ih = self.image_size
        cw, ch = self.canvas_size()
        s = self.scale
        # visible source box in image coordinates (clipped to the image)
        left = max(0.0, self.cx - cw / 2.0 / s)
        top = max(0.0, self.cy - ch / 2.0 / s)
        right = min(float(iw), self.cx + cw / 2.0 / s)
        bottom = min(float(ih), self.cy + ch / 2.0 / s)
        box = (int(left), int(top), min(iw, int(right) + 1), min(ih, int(bottom) + 1))
        if box[2] <= box[0] or box[3] <= box[1]:
            return
        out_w = max(1, round((box[2] - box[0]) * s))
        out_h = max(1, round((box[3] - box[1]) * s))
        filters = getattr(Image, "Resampling", Image)   # Pillow < 9.1 has them on Image
        if s >= 2.0:
            resample = filters.NEAREST   # crisp pixels when zoomed far in
        elif s >= 1.0:
            resample = filters.BILINEAR
        else:
            resample = filters.LANCZOS
        region = self.source.resize((out_w, out_h), resample, box=box)
        self._photo = ImageTk.PhotoImage(region, master=self.canvas)
        x = cw / 2.0 + (box[0] - self.cx) * s
        y = ch / 2.0 + (box[1] - self.cy) * s
        self.canvas.create_image(round(x), round(y), anchor="nw", image=self._photo, tags="plugin_image")

    def _draw_native(self):
        """No Pillow: scale the whole PhotoImage by a small rational factor
        (zoom p, subsample q) and cache it per factor."""
        frac = Fraction(self.scale).limit_denominator(8)
        if frac <= 0:
            frac = Fraction(1, 8)
        if frac.numerator > 16:  # keep zoom() memory bounded
            frac = Fraction(16, max(1, round(16 / self.scale)))
        photo = self._native_cache.get(frac)
        if photo is None:
            photo = self.source
            if frac.numerator > 1:
                photo = photo.zoom(frac.numerator)
            if frac.denominator > 1:
                photo = photo.subsample(frac.denominator)
            self._native_cache = {frac: photo}  # only keep the current one
        self.scale = float(frac)
        self._photo = photo
        cw, ch = self.canvas_size()
        x = cw / 2.0 - self.cx * self.scale
        y = ch / 2.0 - self.cy * self.scale
        self.canvas.create_image(round(x), round(y), anchor="nw", image=photo, tags="plugin_image")


class _Tip:
    """Small delayed tooltip (explicit colors: readable on dark desktop themes)."""

    def __init__(self, widget, text, delay_ms=500):
        self.widget, self.text, self.delay_ms = widget, text, delay_ms
        self._after = None
        self._tip = None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonPress>", self._hide, add="+")

    def _schedule(self, _e=None):
        self._after = self.widget.after(self.delay_ms, self._show)

    def _show(self):
        if self._tip is not None:
            return
        x = self.widget.winfo_rootx() + 10
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self._tip = tk.Toplevel(self.widget)
        self._tip.wm_overrideredirect(True)
        self._tip.wm_geometry(f"+{x}+{y}")
        tk.Label(self._tip, text=self.text, background="#ffffe0", foreground="#1e1e1e",
                 relief="solid", borderwidth=1, font=("TkDefaultFont", 8), padx=4, pady=2).pack()

    def _hide(self, _e=None):
        if self._after is not None:
            try:
                self.widget.after_cancel(self._after)
            except Exception:
                pass
            self._after = None
        if self._tip is not None:
            try:
                self._tip.destroy()
            except Exception:
                pass
            self._tip = None


#eof
