"""간단한 앱 아이콘 생성."""
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent
ASSETS = ROOT / "assets"
ICO = ASSETS / "app_icon.ico"


def build_ico():
    ASSETS.mkdir(exist_ok=True)
    image = Image.new("RGBA", (256, 256), (79, 70, 229, 255))
    draw = ImageDraw.Draw(image)
    draw.rounded_rectangle((18, 18, 238, 238), radius=36, fill=(67, 56, 202, 255))
    try:
        font = ImageFont.truetype("malgun.ttf", 140)
    except Exception:
        font = ImageFont.load_default()
    text = "B"
    bbox = draw.textbbox((0, 0), text, font=font)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
    draw.text(((256 - tw) / 2, (256 - th) / 2 - 12), text, font=font, fill="white")
    image.save(ICO, format="ICO", sizes=[(s, s) for s in (16, 24, 32, 48, 64, 128, 256)])
    print(f"ICO 생성: {ICO}")


if __name__ == "__main__":
    build_ico()
