@echo off
setlocal
cd /d "%~dp0"

if not exist ".venv\Scripts\python.exe" (
    python -m venv .venv
)

call .venv\Scripts\activate.bat
python -m pip install -q --upgrade pip
pip install -q -r requirements.txt
pip install -q pyinstaller pillow certifi

python make_icon.py
pyinstaller --noconfirm --clean build.spec
if errorlevel 1 exit /b 1

set "RELEASE=release\BloggerSpot"
if exist "release" rmdir /s /q "release"
mkdir "%RELEASE%"
xcopy /E /I /Y "dist\BloggerSpot\*" "%RELEASE%\" >nul

if not exist "%RELEASE%\data" mkdir "%RELEASE%\data"

> "%RELEASE%\run.bat" echo @echo off
>> "%RELEASE%\run.bat" echo cd /d "%%~dp0"
>> "%RELEASE%\run.bat" echo start "" "BloggerSpot.exe"
python _write_launcher.py

endlocal
