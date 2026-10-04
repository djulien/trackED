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
pip install Pillow  #JPEG etc., singing faces, pixel editor (HPND license -- permissive;
                   # offered by the Install button too)
"""

from __future__ import annotations

import tkinter as tk
from fractions import Fraction
from pathlib import Path
from tkinter import ttk, messagebox, colorchooser
from typing import Optional

from utils import debug

IMAGE_EXTS = {".png", ".gif", ".pgm", ".ppm", ".jpg", ".jpeg", ".bmp", ".webp", ".tif", ".tiff"}
FILE_TYPES = [("Images", " ".join(f"*{e}" for e in sorted(IMAGE_EXTS)))]   # File > Open (tracked.py)

MAX_PANEL_SHARE = 0.75      # zooming in grows the image panel up to this share of the window


def _pillow_installed() -> bool:
    import importlib.util
    try:
        return importlib.util.find_spec("PIL") is not None
    except (ImportError, ValueError):
        return False


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
            descr += "{yellow}(install Pillow for smoother zooming, singing faces and the pixel editor)\n"
        else:
            descr += (
                "{blue}Singing faces: {cyan}Eyes \u25ad{blue} / {cyan}Mouth \u25ad{blue} then drag a box on the "
                "image; {cyan}Make faces{blue} saves 20 images (10 mouth shapes \u00d7 eyes open/closed) in a "
                "\u201c-faces\u201d folder for xLights. {cyan}\u25c0 \u25b6{blue} (or Left/Right) and "
                "{cyan}\u25b6 Auto-browse{blue} show them.\n"
                "{blue}Pixel editor: {cyan}\u270e Pixels{blue}: left button paints, right-click picks a color, "
                "middle-drag pans, {cyan}Ctrl+Z{blue} undoes, {cyan}Save{blue} writes.\n")
            if viewer.variants:
                descr += f"{{green}}{len(viewer.variants)} face images found next to this image.\n"
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
        # singing faces / pixel editor (Pillow only)
        self.base = None                        # the original image (self.source shows a variant)
        self.variants = {}                      # "AI_EyesOpen" -> PIL image (see faces.py)
        self.view_name = None                   # None = the original
        self.eyes_box = self.mouth_box = None   # image pixels (x0, y0, x1, y1)
        self.tool = None                        # None | "eyes" | "mouth" | "pencil"
        self.pen_color = (0, 0, 0)
        self._undo = []                         # (view_name, image copy) for the pixel editor
        self._edited = set()                    # view names with unsaved pixel edits
        self._flip_id = None
        self._last_px = None

        self._load()
        if self.kind == "pil":
            self.base = self.source
            self._load_faces()
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
        pillow_missing = self.kind != "pil" and not _pillow_installed()
        if self.source is None and not pillow_missing:
            return
        bar = ttk.Frame(self.canvas.master)
        bar.pack(side="top", fill="x", before=self.canvas, pady=(2, 2))
        self.toolbar = bar
        self.canvas._plugin_toolbars = [bar]
        if pillow_missing:
            # the same Install dialog as an audio tab's (waveform_tab.py)
            b = tk.Button(bar, text="\u26a0 Install", command=self._open_install, fg="#b36b00",
                          relief="flat", padx=6)
            b.pack(side="right", padx=(6, 2))
            _Tip(b, "Pillow is missing: JPEG/BMP/WebP, smooth zoom, singing faces and the pixel editor need it.\n"
                    "Click to install it (and other missing packages)")
            self.install_btn = b
        if self.source is None:
            ttk.Label(bar, text="This image type needs Pillow.").pack(side="left", padx=(4, 0))
            return

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
        if self.kind == "pil":
            self._build_face_bar()

    def _build_face_bar(self):
        """Second toolbar row: singing faces (boxes, Make faces, flip
        through the results) and the pixel editor."""
        bar = ttk.Frame(self.canvas.master)
        bar.pack(side="top", fill="x", before=self.canvas, pady=(0, 2))
        self.canvas._plugin_toolbars.append(bar)
        self.face_bar = bar

        def btn(text, cmd, tip, width=None):
            b = ttk.Button(bar, text=text, command=cmd, width=width)
            b.pack(side="left", padx=(0, 2))
            _Tip(b, tip)
            return b
        faces_btn = ttk.Menubutton(bar, text="Faces \u25be")
        faces_btn.pack(side="left", padx=(0, 2))
        fmenu = tk.Menu(faces_btn, tearoff=False, bg="#ffffff", fg="#1e1e1e", activebackground="#cce4ff",
                        activeforeground="#1e1e1e")
        fmenu.add_command(label="Mark eyes \u25ad  (drag a box around both eyes)", command=lambda: self.mark("eyes"))
        fmenu.add_command(label="Mark mouth \u25ad  (drag a box around the mouth)", command=lambda: self.mark("mouth"))
        fmenu.add_separator()
        fmenu.add_command(label="Make faces", command=self.make_faces)
        faces_btn.configure(menu=fmenu)
        self.faces_menu = fmenu
        _Tip(faces_btn, "Singing faces for xLights: mark the eyes and the mouth, then Make faces\n"
                        "(10 mouth shapes, eyes open and closed, into a \u201c-faces\u201d folder)")
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=6)
        btn("\u25c0", lambda: self.step_variant(-1), "Previous image (or Left arrow)", 3)
        self.variant_var = tk.StringVar(value="")
        ttk.Label(bar, textvariable=self.variant_var, width=24, anchor="center").pack(side="left")
        btn("\u25b6", lambda: self.step_variant(1), "Next image (or Right arrow)", 3)
        self.flip_btn = btn("\u25b6 Auto-browse", self.toggle_flip,
                            "Step through the face images by themselves, like a flip book\n"
                            "(eyes open, then eyes closed); click again to stop")
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=6)
        btn("\u270e Pixels", lambda: self.set_tool(None if self.tool == "pencil" else "pencil"),
            "Pixel editor: click/drag paints the shown image; right-click picks a color;\n"
            "middle-drag pans; Ctrl+Z undoes. Save writes the edited images.")
        self.swatch = tk.Button(bar, width=2, bg=self._hex(self.pen_color), activebackground=self._hex(self.pen_color),
                                relief="sunken", command=self.choose_color)
        self.swatch.pack(side="left", padx=(0, 2))
        _Tip(self.swatch, "Paint color (click to change; right-click the image to pick one)")
        btn("Save", self.save_edits, "Save the pixel edits")
        self._update_variant_label()

    def _open_install(self):
        try:
            from waveform_tab import InstallDialog, _restart_app
        except Exception as exc:
            messagebox.showinfo("Install", f"The Install dialog couldn't open ({exc}).\n"
                                           "Run: python deps.py --list")
            return

        InstallDialog(self.canvas, restart=lambda: _restart_app(self.canvas))

    def _grow_panel(self):
        """Zoomed in past the panel's height: make the image panel taller
        (move the tab's sash down), at most to 75% of the window height.
        Never shrinks it."""
        paned = getattr(self.tab, "paned", None)
        if paned is None or self.fit:
            return False
        try:
            current = int(paned.sashpos(0))
            window_h = int(self.canvas.winfo_toplevel().winfo_height())
            paned_h = int(paned.winfo_height())
        except (tk.TclError, TypeError, ValueError, AttributeError):
            return False
        want = self._toolbar_height() + int(self.image_size[1] * self.scale) + 8
        limit = min(int(window_h * MAX_PANEL_SHARE), paned_h - 60 if paned_h > 120 else paned_h)
        new = min(want, limit)
        if new > current:
            try:
                paned.sashpos(0, new)
                return True
            except tk.TclError:
                return False
        return False

    def _toolbar_height(self):
        try:
            h = max(1, self.toolbar.winfo_reqheight()) if self.toolbar is not None else 0
            bar = getattr(self, "face_bar", None)
            return h + (max(1, bar.winfo_reqheight()) if bar is not None else 0)
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
        c.bind("<ButtonPress-3>", self._on_right)
        c.bind("<Motion>", self._on_motion, add="+")
        c.bind("<Leave>", self._on_leave, add="+")
        c.bind("<ButtonPress-2>", lambda e: self._on_press(e, pan=True))
        c.bind("<B2-Motion>", lambda e: self._on_drag(e, pan=True))
        c.bind("<ButtonRelease-2>", self._on_release)
        c.bind("<Left>", lambda e: self.step_variant(-1))
        c.bind("<Right>", lambda e: self.step_variant(1))
        for seq in ("<Control-z>", "<Control-Z>"):
            c.bind(seq, lambda e: self.undo_pixels())
        c.bind("<Escape>", lambda e: self.set_tool(None))
        c.bind("<Enter>", lambda e: c.focus_set())
        for key, fn in (("<plus>", self.zoom_in), ("<equal>", self.zoom_in), ("<KP_Add>", self.zoom_in),
                        ("<minus>", self.zoom_out), ("<KP_Subtract>", self.zoom_out),
                        ("<Key-0>", self.zoom_fit), ("<Key-1>", self.zoom_actual)):
            c.bind(key, lambda e, fn=fn: fn())

    def _on_wheel(self, event):
        up = getattr(event, "num", None) == 4 or (getattr(event, "delta", 0) or 0) > 0
        self.zoom_by(ZOOM_STEP if up else 1 / ZOOM_STEP, at=(event.x, event.y))
        return "break"

    def _on_press(self, event, pan=False):
        if not pan and self.tool in ("eyes", "mouth"):
            self._box_start = self.to_image(event.x, event.y)
            return
        if not pan and self.tool == "pencil":
            self._last_px = None
            self.paint_at(*self.to_image(event.x, event.y))
            return
        self._drag = (event.x, event.y, self.cx, self.cy)
        if self._pannable():
            self.canvas.configure(cursor="fleur")

    def _on_drag(self, event, pan=False):
        if not pan and self.tool in ("eyes", "mouth") and getattr(self, "_box_start", None):
            x0, y0 = self._box_start
            x1, y1 = self.to_image(event.x, event.y)
            self._set_box(self.tool, (x0, y0, x1, y1), final=False)
            return
        if not pan and self.tool == "pencil":
            self.paint_at(*self.to_image(event.x, event.y))
            return
        self._mouse = self.to_image(event.x, event.y)
        if not self._drag or not self._pannable():
            return
        x0, y0, cx0, cy0 = self._drag
        self.cx = cx0 - (event.x - x0) / self.scale
        self.cy = cy0 - (event.y - y0) / self.scale
        self._clamp_center()
        self.redraw()

    def _on_release(self, event):
        if self.tool in ("eyes", "mouth") and getattr(self, "_box_start", None):
            x0, y0 = self._box_start
            x1, y1 = self.to_image(event.x, event.y)
            self._box_start = None
            self._set_box(self.tool, (x0, y0, x1, y1), final=True)
            self.set_tool(None)
            return
        self._last_px = None
        self._drag = None
        self.canvas.configure(cursor=self._tool_cursor())

    def _on_right(self, event):
        """Pixel editor: right-click picks the color under the pointer."""
        if self.tool != "pencil" or self.kind != "pil":
            return
        x, y = (int(v) for v in self.to_image(event.x, event.y))
        iw, ih = self.image_size
        if 0 <= x < iw and 0 <= y < ih:
            px = self.source.getpixel((x, y))
            self.set_color(tuple(px[:3]) if isinstance(px, tuple) else (px, px, px))

    def _on_double(self, event):
        if self.tool is not None:
            return
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
        self._grow_panel()

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
        self._draw_backdrop()
        try:
            if self.kind == "pil":
                self._draw_pil()
            else:
                self._draw_native()
        except Exception as exc:  # never let a draw error break the tab
            debug(1, f"{{red}}image_tab draw error: {exc}")
        self._draw_pixel_grid()
        self._draw_boxes()
        self._draw_overlay()
        self.zoom_var.set(f"{self.scale * 100:.0f}%" + (" (fit)" if self.fit else ""))

    # ------------------------------------------------------------------ backdrop, grid, overlay
    BACKDROP = "#e4e4e4"
    BACKDROP_LINE = "#cdcdcd"
    PIXEL_GRID_MIN_SCALE = 8.0     # thin lines between pixels from this zoom on
    PIXEL_GRID = "#9a9a9a"

    def _grid_lines(self, step_px, x0, y0, x1, y1):
        """Canvas x and y positions of image-pixel boundaries every step_px
        image pixels, within the canvas rectangle (x0, y0)-(x1, y1)."""
        s = self.scale
        ix0, iy0 = self.to_image(x0, y0)
        ix1, iy1 = self.to_image(x1, y1)
        xs = [self.to_canvas(i, 0)[0] for i in range(int(ix0 // step_px) * step_px, int(ix1) + step_px, step_px)]
        ys = [self.to_canvas(0, j)[1] for j in range(int(iy0 // step_px) * step_px, int(iy1) + step_px, step_px)]
        return [x for x in xs if x0 <= x <= x1], [y for y in ys if y0 <= y <= y1]

    def _draw_backdrop(self):
        """A light gray grid behind the image, lined up with its pixels (a
        line every pixel, or every few pixels when zoomed out) -- it shows
        through transparent pixels and around the image."""
        c = self.canvas
        try:
            c.delete("plugin_bg")
        except tk.TclError:
            return
        cw, ch = self.canvas_size()
        c.create_rectangle(0, 0, cw, ch, fill=self.BACKDROP, outline="", tags="plugin_bg")
        s = max(self.scale, 1e-6)
        step = 1
        while step * s < 8:
            step *= 2
        xs, ys = self._grid_lines(step, 0, 0, cw, ch)
        if len(xs) + len(ys) <= 800:
            for x in xs:
                c.create_line(x, 0, x, ch, fill=self.BACKDROP_LINE, tags="plugin_bg")
            for y in ys:
                c.create_line(0, y, cw, y, fill=self.BACKDROP_LINE, tags="plugin_bg")
        try:
            c.tag_lower("plugin_bg")
        except tk.TclError:
            pass

    def _draw_pixel_grid(self):
        """Zoomed far in: thin lines between the image's pixels, over it."""
        c = self.canvas
        try:
            c.delete("plugin_pxgrid")
        except tk.TclError:
            return
        if self.scale < self.PIXEL_GRID_MIN_SCALE or self.source is None:
            return
        iw, ih = self.image_size
        cw, ch = self.canvas_size()
        left, top = self.to_canvas(0, 0)
        right, bottom = self.to_canvas(iw, ih)
        x0, y0, x1, y1 = max(0, left), max(0, top), min(cw, right), min(ch, bottom)
        if x1 <= x0 or y1 <= y0:
            return
        xs, ys = self._grid_lines(1, x0, y0, x1, y1)
        if len(xs) + len(ys) > 1200:
            return
        for x in xs:
            c.create_line(x, y0, x, y1, fill=self.PIXEL_GRID, tags="plugin_pxgrid")
        for y in ys:
            c.create_line(x0, y, x1, y, fill=self.PIXEL_GRID, tags="plugin_pxgrid")

    def _draw_overlay(self):
        """Along the bottom of the image area: the current message (left)
        and the pointer's image coordinates + color (right)."""
        c = self.canvas
        try:
            c.delete("plugin_overlay")
        except tk.TclError:
            return
        cw, ch = self.canvas_size()
        msg = getattr(self, "status_msg", "")
        coords = self.coords_text()
        if not msg and not coords:
            return
        y = ch - 4
        if msg:
            t = c.create_text(6, y, text=msg, anchor="sw", fill="#ffffff", tags="plugin_overlay",
                              font=("TkDefaultFont", 9))
            self._overlay_bg(t)
        if coords:
            t = c.create_text(cw - 6, y, text=coords, anchor="se", fill="#ffffff", tags="plugin_overlay",
                              font=("TkFixedFont", 9))
            self._overlay_bg(t)

    def _overlay_bg(self, item):
        c = self.canvas
        try:
            box = c.bbox(item)
            if box:
                bg = c.create_rectangle(box[0] - 4, box[1] - 2, box[2] + 4, box[3] + 2, fill="#333333",
                                        outline="", tags="plugin_overlay")
                c.tag_lower(bg, item)
        except (tk.TclError, TypeError):
            pass

    def coords_text(self):
        """"x 12  y 40  #a0b0c0" for the pixel under the pointer (empty off the image)."""
        pos = getattr(self, "_mouse", None)
        if pos is None or self.source is None:
            return ""
        x, y = int(pos[0] // 1), int(pos[1] // 1)
        iw, ih = self.image_size
        if not (0 <= x < iw and 0 <= y < ih):
            return ""
        text = f"x {x}  y {y}"
        if self.kind == "pil":
            try:
                px = self.source.getpixel((x, y))
                rgb = px[:3] if isinstance(px, tuple) else (px, px, px)
                text += "  " + self._hex(rgb)
                if isinstance(px, tuple) and len(px) == 4 and px[3] < 255:
                    text += f" a{px[3]}"
            except Exception:
                pass
        return text

    def _on_motion(self, event):
        self._mouse = self.to_image(event.x, event.y)
        self._draw_overlay()

    def _on_leave(self, event=None):
        self._mouse = None
        self._draw_overlay()

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


    # ------------------------------------------------------------------ coordinates
    def to_image(self, x, y):
        cw, ch = self.canvas_size()
        return self.cx + (x - cw / 2.0) / self.scale, self.cy + (y - ch / 2.0) / self.scale

    def to_canvas(self, ix, iy):
        cw, ch = self.canvas_size()
        return cw / 2.0 + (ix - self.cx) * self.scale, ch / 2.0 + (iy - self.cy) * self.scale

    # ------------------------------------------------------------------ singing faces
    @staticmethod
    def _hex(rgb):
        return "#%02x%02x%02x" % tuple(int(v) for v in rgb[:3])

    def _tool_cursor(self):
        return {"eyes": "crosshair", "mouth": "crosshair", "pencil": "pencil"}.get(self.tool, "")

    def set_tool(self, tool):
        self.tool = tool
        try:
            self.canvas.configure(cursor=self._tool_cursor())
        except tk.TclError:
            pass
        hints = {"eyes": "Drag a box around both eyes", "mouth": "Drag a box around the mouth",
                 "pencil": "Pixel editor on: paint with the left button, right-click picks a color"}
        self._status(hints.get(tool, ""))

    def mark(self, which):
        """Faces \u25be > Mark eyes / mouth: back to the original (where the
        boxes are drawn, also after the faces were made) and drag a new box."""
        if self.view_name is not None:
            self.show_variant(None)
        self.set_tool(which)
        self._draw_boxes()

    def _status(self, msg):
        """A message along the bottom of the image area (see _draw_overlay)."""
        self.status_msg = msg or ""
        self._draw_overlay()

    def _set_box(self, which, box, final):
        import faces
        box = faces.clamp_box(box, self.image_size) if final else box
        setattr(self, "eyes_box" if which == "eyes" else "mouth_box", box)
        self._draw_boxes()
        if final and box:
            self._status(f"{which.capitalize()} box: {box[2] - box[0]}\u00d7{box[3] - box[1]} px. "
                         + ("Now Make faces." if self.mouth_box else "Now mark the mouth."))

    def _draw_boxes(self):
        c = self.canvas
        try:
            c.delete("face_box")
        except tk.TclError:
            return
        if self.view_name is not None:
            return                               # boxes only over the original
        for box, color, name in ((self.eyes_box, "#4fc3f7", "eyes"), (self.mouth_box, "#f0b429", "mouth")):
            if not box:
                continue
            x0, y0 = self.to_canvas(box[0], box[1])
            x1, y1 = self.to_canvas(box[2], box[3])
            c.create_rectangle(x0, y0, x1, y1, outline=color, width=2, dash=(4, 2), tags="face_box")
            c.create_text(min(x0, x1) + 3, min(y0, y1) + 2, text=name, fill=color, anchor="nw",
                          font=("TkDefaultFont", 8, "bold"), tags="face_box")

    def _load_faces(self):
        try:
            import faces
            self.eyes_box, self.mouth_box = faces.load_boxes(self.filepath)
            self.variants = faces.load_set(self.filepath)
        except Exception as exc:
            debug(1, f"{{yellow}}image_tab: couldn't load the face images: {exc}")
            self.variants = {}

    def make_faces(self, confirm=True):
        """Generate the mouth-shape images (eyes open/closed) from the boxes,
        save them into "<image>-faces/" and show the first one."""
        import faces
        if self.base is None:
            return False
        if not self.mouth_box:
            messagebox.showinfo("Make faces", "First mark the mouth: click \u201cMouth \u25ad\u201d and drag a "
                                              "box around it (and \u201cEyes \u25ad\u201d for the eyes).")
            return False
        folder = faces.faces_dir(self.filepath)
        if confirm and self.variants and not messagebox.askyesno(
                "Make faces", f"Replace the {len(self.variants)} face images in {folder.name}?\n"
                              "(Pixel edits made to them are lost.)"):
            return False
        iw, ih = self.image_size
        if confirm and iw * ih > 1500 * 1500 and not messagebox.askyesno(
                "Make faces", f"This image is large ({iw}\u00d7{ih}); making 20 copies takes a while and "
                              "xLights matrices are usually much smaller. Continue?"):
            return False
        self._status("Making faces...")
        try:
            self.canvas.configure(cursor="watch")
            self.canvas.update_idletasks()
            images = faces.generate(self.base, self.eyes_box, self.mouth_box)
            faces.save_set(self.filepath, images, self.eyes_box, self.mouth_box)
        except Exception as exc:
            messagebox.showerror("Make faces", f"Couldn't make the faces:\n{exc}")
            self._status("")
            return False
        finally:
            try:
                self.canvas.configure(cursor=self._tool_cursor())
            except tk.TclError:
                pass
        self.variants = {name: images[name] for name in faces.variant_names() if name in images}
        self._edited = {n for n in self._edited if n is None}
        self._undo = [u for u in self._undo if u[0] is None]
        self.show_variant(next(iter(self.variants)))
        self._status(f"{len(images)} images saved in {folder.name}/ (see its README.txt for xLights)")
        debug(1, f"{{green}}image_tab: {len(images)} face images -> {folder}")
        return True

    def _names(self):
        return [None] + list(self.variants)

    def show_variant(self, name):
        """Show a face image (name) or the original (None)."""
        if name is not None and name not in self.variants:
            return
        self.view_name = name
        self.source = self.base if name is None else self.variants[name]
        self._update_variant_label()
        self.redraw()

    def step_variant(self, direction):
        names = self._names()
        if len(names) <= 1:
            return
        i = names.index(self.view_name) if self.view_name in names else 0
        self.show_variant(names[(i + direction) % len(names)])

    def _update_variant_label(self):
        var = getattr(self, "variant_var", None)
        if var is None:
            return
        if not self.variants:
            var.set("(no faces yet)")
        elif self.view_name is None:
            var.set(f"Original  (+{len(self.variants)} faces)")
        else:
            ph, eyes = self.view_name.rsplit("_Eyes", 1)
            i = list(self.variants).index(self.view_name) + 1
            var.set(f"{ph} \u00b7 eyes {eyes.lower()}  ({i}/{len(self.variants)})")

    FLIP_MS = 450

    def toggle_flip(self):
        """Flip book: the eyes-open mouth shapes, then the eyes-closed ones,
        over and over until clicked again."""
        if self._flip_id is not None:
            try:
                self.canvas.after_cancel(self._flip_id)
            except (tk.TclError, ValueError):
                pass
            self._flip_id = None
            self.flip_btn.configure(text="\u25b6 Auto-browse")
            return
        if not self.variants:
            self._status("Make faces first")
            return
        self.flip_btn.configure(text="\u275a\u275a Stop")
        # all the eyes-open shapes, then all the eyes-closed ones, round and round
        order = ([n for n in self.variants if n.endswith("_EyesOpen")]
                 + [n for n in self.variants if n.endswith("_EyesClosed")]) or list(self.variants)

        def tick(i=0):
            try:
                if not self.canvas.winfo_exists():
                    return
            except tk.TclError:
                return
            self.show_variant(order[i % len(order)])
            self._flip_id = self.canvas.after(self.FLIP_MS, lambda: tick(i + 1))
        tick(order.index(self.view_name) if self.view_name in order else 0)

    # ------------------------------------------------------------------ pixel editor
    def choose_color(self):
        rgb, _hex = colorchooser.askcolor(color=self._hex(self.pen_color), title="Paint color")
        if rgb:
            self.set_color(tuple(int(v) for v in rgb))

    def set_color(self, rgb):
        self.pen_color = tuple(int(v) for v in rgb[:3])
        try:
            self.swatch.configure(bg=self._hex(self.pen_color), activebackground=self._hex(self.pen_color))
        except (tk.TclError, AttributeError):
            pass

    def paint_at(self, ix, iy):
        """Paint one image pixel (and the line from the previous one while dragging)."""
        if self.kind != "pil" or self.source is None:
            return False
        from PIL import ImageDraw
        x, y = int(ix), int(iy)
        iw, ih = self.image_size
        if not (0 <= x < iw and 0 <= y < ih):
            self._last_px = None
            return False
        if self._last_px is None:
            self._undo.append((self.view_name, self.source.copy()))
            del self._undo[:-30]
        color = self.pen_color + ((255,) if self.source.mode == "RGBA" else ())
        if self._last_px is not None and self._last_px != (x, y):
            ImageDraw.Draw(self.source).line([self._last_px, (x, y)], fill=color, width=1)
        else:
            self.source.putpixel((x, y), color)
        self._last_px = (x, y)
        self._edited.add(self.view_name)
        self._status(f"Edited ({len(self._edited)} unsaved) \u2013 Save to keep")
        self.redraw()
        return True

    def undo_pixels(self):
        if not self._undo:
            return False
        name, img = self._undo.pop()
        self._last_px = None
        if name is None:
            self.base = img
        elif name in self.variants:
            self.variants[name] = img
        else:
            return False
        self.show_variant(name)
        return True

    def save_edits(self):
        """Write the edited images: face images to their files; the
        original only after asking (it overwrites the opened file)."""
        import faces
        saved = []
        for name in sorted(self._edited, key=lambda n: (n is not None, n or "")):
            if name is None:
                if not messagebox.askyesno("Save", f"Overwrite the original image {Path(self.filepath).name}?"):
                    continue
                self.base.save(self.filepath)
            elif name in self.variants:
                path = faces.variant_path(self.filepath, name)
                path.parent.mkdir(parents=True, exist_ok=True)
                self.variants[name].save(path)
            saved.append(name)
        for name in saved:
            self._edited.discard(name)
        self._status(f"Saved {len(saved)} image{'s' if len(saved) != 1 else ''}" if saved else "Nothing to save")
        return saved


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
