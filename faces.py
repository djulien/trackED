"""Singing faces for xLights from one picture (image_tab's Faces tools).

The user marks two boxes on the image: one around both eyes, one around
the mouth. generate() then makes one image per mouth shape (the
Preston Blair / Papagayo phoneme set xLights uses: AI E etc FV L MBP O
rest U WQ), each with eyes open and eyes closed -- 20 images:

  - the original mouth is painted over with skin, filled in smoothly from
    the colors around the box (a Coons patch), so no hole is left;
  - a new mouth is drawn at 4x size and scaled down (smooth edges), in
    lip/teeth/tongue colors taken from the picture where possible;
  - closed eyes: each half of the eye box is filled with skin the same
    way and gets a lid line in the darkest color found there (lashes).

Results are simple cartoon shapes meant as a starting point; the image
tab's pixel editor is there for touch-ups. Pillow + numpy only (both
permissive licenses); no Tk here.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple

try:
    import numpy as np
except ImportError:                       # pragma: no cover
    np = None  # type: ignore

PHONEMES = ["AI", "E", "etc", "FV", "L", "MBP", "O", "rest", "U", "WQ"]
EYE_STATES = ("Open", "Closed")
SUPERSAMPLE = 4

# Mouth shapes, as fractions of the mouth box: w/h = opening size (h 0 =
# closed lips), top/bottom = teeth showing (share of the opening),
# tongue = tongue showing at the bottom, tongue_up = tip behind the top
# teeth (L), tuck = lower lip under the top teeth (F/V), smile/press for
# closed mouths.
SHAPES: Dict[str, Dict[str, float]] = {
    "rest": dict(w=0.72, h=0.0, smile=0.10),
    "MBP": dict(w=0.62, h=0.0, press=1.0),
    "AI": dict(w=0.92, h=0.80, top=0.22, tongue=0.30),
    "E": dict(w=0.95, h=0.38, top=0.45, bottom=0.35),
    "etc": dict(w=0.80, h=0.42, top=0.40, bottom=0.30),
    "FV": dict(w=0.80, h=0.24, top=0.75, tuck=1.0),
    "L": dict(w=0.78, h=0.55, top=0.25, tongue_up=1.0),
    "O": dict(w=0.55, h=0.72, top=0.12),
    "U": dict(w=0.38, h=0.48),
    "WQ": dict(w=0.30, h=0.36),
}

Box = Tuple[int, int, int, int]       # x0, y0, x1, y1 (image pixels, x1/y1 exclusive)


def variant_names() -> List[str]:
    """"AI_EyesOpen", "AI_EyesClosed", ... in display order."""
    return [f"{p}_Eyes{e}" for p in PHONEMES for e in EYE_STATES]


def clamp_box(box, size) -> Optional[Box]:
    """Box in order and inside the image (at least 4x4 px), else None."""
    if not box:
        return None
    w, h = size
    x0, y0, x1, y1 = (int(round(v)) for v in box)
    x0, x1 = sorted((max(0, min(w, x0)), max(0, min(w, x1))))
    y0, y1 = sorted((max(0, min(h, y0)), max(0, min(h, y1))))
    if x1 - x0 < 4 or y1 - y0 < 4:
        return None
    return x0, y0, x1, y1


# ---------------------------------------------------------------------------
# Colors and skin fill
# ---------------------------------------------------------------------------

def _rgb(img):
    return np.asarray(img.convert("RGB"), dtype=np.float32)


def _ring(arr, box, depth=2):
    """Pixels just outside the box (up to depth px), as an (n, 3) array."""
    h, w = arr.shape[:2]
    x0, y0, x1, y1 = box
    parts = []
    for d in range(1, depth + 1):
        if y0 - d >= 0:
            parts.append(arr[y0 - d, x0:x1])
        if y1 - 1 + d < h:
            parts.append(arr[y1 - 1 + d, x0:x1])
        if x0 - d >= 0:
            parts.append(arr[y0:y1, x0 - d])
        if x1 - 1 + d < w:
            parts.append(arr[y0:y1, x1 - 1 + d])
    if not parts:
        return arr[y0:y1, x0:x1].reshape(-1, 3)
    return np.concatenate(parts, axis=0)


def skin_color(arr, box) -> Tuple[float, float, float]:
    ring = _ring(arr, box)
    return tuple(float(v) for v in np.median(ring, axis=0))


def coons_fill(arr, box):
    """Fill the box from the colors around it: each edge's colors are
    blended smoothly across (a Coons patch), so shading carries through."""
    h, w = arr.shape[:2]
    x0, y0, x1, y1 = box
    bw, bh = x1 - x0, y1 - y0

    def row(y):
        a = arr[max(0, min(h - 1, y)), x0:x1]
        b = arr[max(0, min(h - 1, y + (1 if y < y0 else -1))), x0:x1]
        return (a + b) / 2

    def col(x):
        a = arr[y0:y1, max(0, min(w - 1, x))]
        b = arr[y0:y1, max(0, min(w - 1, x + (1 if x < x0 else -1)))]
        return (a + b) / 2
    top, bottom = row(y0 - 1), row(y1)
    left, right = col(x0 - 1), col(x1)
    u = (np.arange(bw, dtype=np.float32) + 0.5) / bw          # 0..1 across
    v = (np.arange(bh, dtype=np.float32) + 0.5) / bh          # 0..1 down
    U, V = u[None, :, None], v[:, None, None]
    c00, c10 = (top[0] + left[0]) / 2, (top[-1] + right[0]) / 2
    c01, c11 = (bottom[0] + left[-1]) / 2, (bottom[-1] + right[-1]) / 2
    ruled_v = (1 - V) * top[None, :, :] + V * bottom[None, :, :]
    ruled_u = (1 - U) * left[:, None, :] + U * right[:, None, :]
    bilinear = ((1 - U) * (1 - V) * c00 + U * (1 - V) * c10 + (1 - U) * V * c01 + U * V * c11)
    return np.clip(ruled_v + ruled_u - bilinear, 0, 255)


def _feather_mask(size, ellipse=False, soft=0.12):
    from PIL import Image, ImageDraw, ImageFilter
    w, h = size
    m = Image.new("L", (w, h), 0)
    d = ImageDraw.Draw(m)
    pad = max(1, int(min(w, h) * soft))
    if ellipse:
        d.ellipse((pad, pad, w - 1 - pad, h - 1 - pad), fill=255)
    else:
        d.rectangle((pad, pad, w - 1 - pad, h - 1 - pad), fill=255)
    return m.filter(ImageFilter.GaussianBlur(max(0.6, pad / 2)))


def paint_over(img, box, ellipse=False):
    """img with the box painted over in skin (feathered into its surroundings)."""
    from PIL import Image
    arr = _rgb(img)
    x0, y0, x1, y1 = box
    patch = Image.fromarray(coons_fill(arr, box).astype("uint8"), "RGB")
    out = img.copy()
    region = out.crop(box)
    mask = _feather_mask((x1 - x0, y1 - y0), ellipse=ellipse)
    blended = Image.composite(patch.convert(region.mode), region, mask)
    out.paste(blended, box[:2])
    return out


def lip_color(arr, box, skin) -> Tuple[int, int, int]:
    """The mouth's own color: the pixels in the box that differ most from
    the skin (lips), or a darker, redder skin if nothing stands out."""
    x0, y0, x1, y1 = box
    px = arr[y0:y1, x0:x1].reshape(-1, 3)
    dist = np.linalg.norm(px - np.asarray(skin, dtype=np.float32), axis=1)
    if px.size and float(np.percentile(dist, 90)) > 30:
        pick = px[dist >= np.percentile(dist, 80)]
        c = np.median(pick, axis=0)
        if c.mean() < 50:                 # mostly the dark inside of an open mouth
            c = np.asarray(skin) * np.array([0.85, 0.55, 0.55])
    else:
        c = np.asarray(skin) * np.array([0.85, 0.55, 0.55])
    return tuple(int(max(0, min(255, v))) for v in c)


def dark_color(arr, box, skin=None) -> Tuple[int, int, int]:
    """The darkest few pixels of the box (lashes / pupil), median -- or a
    dark shade of the skin when nothing there is clearly darker."""
    x0, y0, x1, y1 = box
    px = arr[y0:y1, x0:x1].reshape(-1, 3)
    lum = px.mean(axis=1)
    c = np.median(px[lum <= np.percentile(lum, 2)], axis=0)
    ref = np.asarray(skin if skin is not None else np.median(px, axis=0), dtype=np.float32)
    if c.mean() > 0.7 * ref.mean():
        c = ref * 0.35
    return tuple(int(v) for v in c)


def grow(box, frac, size) -> Box:
    """The box made bigger by frac of its size on every side (inside the image)."""
    x0, y0, x1, y1 = box
    dx, dy = max(1, int((x1 - x0) * frac)), max(1, int((y1 - y0) * frac))
    w, h = size
    return max(0, x0 - dx), max(0, y0 - dy), min(w, x1 + dx), min(h, y1 + dy)


# ---------------------------------------------------------------------------
# Drawing
# ---------------------------------------------------------------------------

def _mouth_layer(size, shape, lip, s=SUPERSAMPLE):
    """An RGBA layer the size of the mouth box with this mouth drawn on it."""
    from PIL import Image, ImageDraw, ImageChops
    bw, bh = size
    W, H = bw * s, bh * s
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(layer)
    cx, cy = W / 2.0, H / 2.0
    lip_c = tuple(lip) + (255,)
    inside = (int(lip[0] * 0.22), int(lip[1] * 0.12), int(lip[2] * 0.14), 255)
    teeth = (242, 240, 232, 255)
    tongue = (196, 84, 96, 255)
    t = max(1.5 * s, 0.16 * H)                    # lip thickness
    w = max(3 * s, shape.get("w", 0.7) * W)
    oh = shape.get("h", 0.0) * H
    if oh <= 0:                                    # closed lips
        smile = shape.get("smile", 0.0) * H
        thick = t * (1.6 if shape.get("press") else 1.0)
        pts = []
        for i in range(25):
            x = cx - w / 2 + w * i / 24
            rel = (x - cx) / (w / 2)
            pts.append((x, cy + smile * 0.5 - smile * rel * rel))
        d.line(pts, fill=lip_c, width=int(round(thick)), joint="curve")
        d.line(pts, fill=inside, width=max(1, int(round(thick / 3))), joint="curve")
        return layer.resize((bw, bh), _lanczos())
    oh = max(oh, 2 * s)
    outer = (cx - w / 2, cy - oh / 2 - t / 2, cx + w / 2, cy + oh / 2 + t / 2)
    inner = (cx - w / 2 + t * 0.8, cy - oh / 2, cx + w / 2 - t * 0.8, cy + oh / 2)
    d.ellipse(outer, fill=lip_c)
    d.ellipse(inner, fill=inside)
    # teeth / tongue, clipped to the opening
    parts = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    pd = ImageDraw.Draw(parts)
    ix0, iy0, ix1, iy1 = inner
    ih = iy1 - iy0
    if shape.get("tongue"):
        tg = shape["tongue"] * ih
        pd.ellipse((cx - (ix1 - ix0) * 0.35, iy1 - tg, cx + (ix1 - ix0) * 0.35, iy1 + tg), fill=tongue)
    if shape.get("tongue_up"):
        pd.ellipse((cx - (ix1 - ix0) * 0.18, iy0 + ih * 0.12, cx + (ix1 - ix0) * 0.18, iy0 + ih * 0.65),
                   fill=tongue)
    if shape.get("top"):
        pd.rectangle((ix0, iy0, ix1, iy0 + shape["top"] * ih), fill=teeth)
    if shape.get("bottom"):
        pd.rectangle((ix0, iy1 - shape["bottom"] * ih, ix1, iy1), fill=teeth)
    clip = Image.new("L", (W, H), 0)
    ImageDraw.Draw(clip).ellipse(inner, fill=255)
    parts.putalpha(ImageChops.multiply(parts.getchannel("A"), clip))
    layer = Image.alpha_composite(layer, parts)
    if shape.get("tuck"):                          # F/V: lower lip under the top teeth
        d2 = ImageDraw.Draw(layer)
        d2.ellipse((cx - w * 0.42, cy + oh * 0.05, cx + w * 0.42, cy + oh / 2 + t * 0.9), fill=lip_c)
    return layer.resize((bw, bh), _lanczos())


def _lanczos():
    from PIL import Image
    return getattr(Image, "Resampling", Image).LANCZOS


def _eye_halves(box) -> List[Box]:
    x0, y0, x1, y1 = box
    mid = (x0 + x1) // 2
    return [(x0, y0, mid, y1), (mid, y0, x1, y1)]


def close_eyes(img, eyes_box, s=SUPERSAMPLE):
    """Both eyes closed: each half of the box (one eye each) is painted
    over with skin and gets a curved lid line in the lash color."""
    from PIL import Image, ImageDraw
    arr = _rgb(img)
    out = img
    for half in _eye_halves(eyes_box):
        x0, y0, x1, y1 = half
        hw, hh = x1 - x0, y1 - y0
        lash = dark_color(arr, half, skin_color(arr, half))
        # paint over a little more than the half box: the feathered edge
        # then lies outside what the user marked
        out = paint_over(out, grow(half, 0.12, img.size), ellipse=True)
        W, H = hw * s, hh * s
        layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        d = ImageDraw.Draw(layer)
        lw = W * 0.68
        cx, cy = W / 2.0, H * 0.55
        sag = H * 0.12
        pts = []
        for i in range(21):
            x = cx - lw / 2 + lw * i / 20
            rel = (x - cx) / (lw / 2)
            pts.append((x, cy + sag * (1 - rel * rel)))
        d.line(pts, fill=tuple(lash) + (255,), width=max(s, int(H * 0.10)), joint="curve")
        layer = layer.resize((hw, hh), _lanczos())
        base = out.convert("RGBA")
        base.alpha_composite(layer, (x0, y0))
        out = base.convert(img.mode)
    return out


def make_mouth(img, mouth_box, phoneme, lip=None):
    """img with its mouth replaced by this phoneme's shape."""
    arr = _rgb(img)
    skin = skin_color(arr, mouth_box)
    if lip is None:
        lip = lip_color(arr, mouth_box, skin)
    base = paint_over(img, grow(mouth_box, 0.15, img.size)).convert("RGBA")
    x0, y0, x1, y1 = mouth_box
    base.alpha_composite(_mouth_layer((x1 - x0, y1 - y0), SHAPES[phoneme], lip), (x0, y0))
    return base.convert(img.mode)


def generate(img, eyes_box, mouth_box) -> Dict[str, "object"]:
    """All variants: {"AI_EyesOpen": Image, "AI_EyesClosed": Image, ...}.
    eyes_box may be None (then only eyes-open images are made)."""
    if np is None:
        raise RuntimeError("numpy is needed for the singing faces")
    if img.mode not in ("RGB", "RGBA"):
        img = img.convert("RGBA")
    mouth_box = clamp_box(mouth_box, img.size)
    if mouth_box is None:
        raise ValueError("draw a box around the mouth first (at least 4x4 pixels)")
    eyes_box = clamp_box(eyes_box, img.size)
    lip = lip_color(_rgb(img), mouth_box, skin_color(_rgb(img), mouth_box))
    closed = close_eyes(img, eyes_box) if eyes_box else None
    out = {}
    for ph in PHONEMES:
        out[f"{ph}_EyesOpen"] = make_mouth(img, mouth_box, ph, lip)
        if closed is not None:
            out[f"{ph}_EyesClosed"] = make_mouth(closed, mouth_box, ph, lip)
    return out


# ---------------------------------------------------------------------------
# Files: <image folder>/<stem>-faces/<stem>_<phoneme>_Eyes<state>.png
# and the boxes in <stem>-faces/boxes.json
# ---------------------------------------------------------------------------

def faces_dir(image_path) -> Path:
    p = Path(image_path)
    return p.with_name(p.stem + "-faces")


def variant_path(image_path, name) -> Path:
    return faces_dir(image_path) / f"{Path(image_path).stem}_{name}.png"


README = """Singing-face images made by trackED from {image}.

xLights: Faces > define a face for your matrix model, type "Matrix", and
pick for each mouth shape the matching file here (the "_EyesOpen" files;
the "_EyesClosed" ones are for the eyes-closed column, if you use blinks).

Mouth shapes (Papagayo/Preston Blair set): AI E etc FV L MBP O rest U WQ.
boxes.json keeps the eye and mouth boxes, so trackED can make them again.
"""


def save_set(image_path, images, eyes_box=None, mouth_box=None) -> Path:
    folder = faces_dir(image_path)
    folder.mkdir(parents=True, exist_ok=True)
    for name, im in images.items():
        im.save(variant_path(image_path, name))
    (folder / "boxes.json").write_text(json.dumps({"eyes": eyes_box, "mouth": mouth_box}), encoding="utf-8")
    (folder / "README.txt").write_text(README.format(image=Path(image_path).name), encoding="utf-8")
    return folder


def load_boxes(image_path) -> Tuple[Optional[Box], Optional[Box]]:
    try:
        data = json.loads((faces_dir(image_path) / "boxes.json").read_text(encoding="utf-8"))
        eyes, mouth = data.get("eyes"), data.get("mouth")
        return (tuple(eyes) if eyes else None), (tuple(mouth) if mouth else None)
    except (OSError, ValueError, TypeError):
        return None, None


def load_set(image_path) -> Dict[str, "object"]:
    """The variants saved for this image (in display order), if any."""
    from PIL import Image
    out = {}
    for name in variant_names():
        path = variant_path(image_path, name)
        if path.exists():
            try:
                with Image.open(path) as im:
                    out[name] = im.convert("RGBA" if im.mode in ("RGBA", "LA", "P") else "RGB")
            except Exception:
                pass
    return out
