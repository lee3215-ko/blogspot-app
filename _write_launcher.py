from pathlib import Path

root = Path(__file__).resolve().parent / "release" / "BloggerSpot"
root.mkdir(parents=True, exist_ok=True)
content = '@echo off\r\ncd /d "%~dp0"\r\nstart "" "BloggerSpot.exe"\r\n'
(root / "run.bat").write_text(content, encoding="ascii")
(root / "실행.bat").write_text(content, encoding="utf-8")
print("wrote launchers")
