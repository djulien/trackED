@echo off
rem trackED launcher / installer for Windows.
rem
rem   trackED.cmd [trackED options and files]      (or double-click it)
rem
rem First run: looks for Python 3.8+; if there is none it asks before
rem installing Python 3.12 for this user (winget, or the python.org
rem installer). Then it makes trackED's own Python environment in
rem %USERPROFILE%\.tracked\venv, installs the small core packages, offers
rem ffmpeg, and starts trackED. Later runs just start trackED. The big
rem optional packages (demucs, Whisper, librosa) are offered by the app's
rem Install button.
rem
rem   trackED.cmd --reinstall     rebuild the environment
rem   trackED.cmd --check         if the window doesn't open: checks Python, Tk,
rem                               the packages and trackED's files, and shows the
rem                               last error (also in %USERPROFILE%\.tracked\console.log)
rem   trackED.cmd --console       run with a console window, to see messages
rem   set TRACKED_CONSOLE=1       run with a console window (to see messages)
rem   set TRACKED_VENV=C:\dir     use another environment folder

setlocal EnableExtensions
set "HERE=%~dp0"
set "VENV=%USERPROFILE%\.tracked\venv"
if not "%TRACKED_VENV%"=="" set "VENV=%TRACKED_VENV%"
set "PY=%VENV%\Scripts\python.exe"
set "PYW=%VENV%\Scripts\pythonw.exe"
set "ARGS=%*"
if /I "%~1"=="--reinstall" (
    if exist "%VENV%" rmdir /s /q "%VENV%"
    set "ARGS="
)
if /I "%~1"=="--console" (
    set "TRACKED_CONSOLE=1"
    set "ARGS="
)
if /I "%~1"=="--check" (
    if not exist "%PY%" (
        echo trackED's environment %VENV% doesn't exist yet: run trackED.cmd once to set it up.
        pause
        exit /b 1
    )
    "%PY%" "%HERE%tracked.py" --check
    echo.
    echo Python's own record of the last start without a console: %USERPROFILE%\.tracked\console.log
    pause
    exit /b 0
)
if exist "%PY%" goto run

echo trackED: first-time setup
call :find_python
if not defined SYSPY (
    choice /M "Python 3 is not installed. Install Python 3.12 for this user now"
    if errorlevel 2 (
        echo trackED needs Python 3.8 or newer.
        pause
        exit /b 1
    )
    call :install_python
    call :find_python
)
if not defined SYSPY (
    echo Python is still not found. Close this window, open a new one and run trackED.cmd again.
    pause
    exit /b 1
)
"%SYSPY%" -c "import tkinter" 2>nul
if errorlevel 1 (
    echo This Python has no Tk support. Re-run its installer, choose Modify, and check "tcl/tk and IDLE".
    pause
    exit /b 1
)
echo Creating trackED's Python environment in %VENV% ...
"%SYSPY%" -m venv "%VENV%"
if errorlevel 1 (
    echo Could not create %VENV%
    pause
    exit /b 1
)
"%PY%" -m pip install --upgrade pip >nul 2>&1
echo Installing the core packages (about 30 MB) ...
"%PY%" "%HERE%deps.py" --install-core
if errorlevel 1 echo Some core packages failed; the app's Install button can retry.
where ffmpeg >nul 2>&1
if errorlevel 1 (
    where winget >nul 2>&1
    if not errorlevel 1 (
        choice /M "ffmpeg (audio decoding, recommended) is not installed. Install it now with winget"
        if not errorlevel 2 winget install -e --id Gyan.FFmpeg --accept-source-agreements --accept-package-agreements
    )
)
echo Setup done. If the trackED window doesn't appear, run:  trackED.cmd --check
echo Optional extras (stems, transcription, mood) are offered by the Install button.

:run
if "%TRACKED_CONSOLE%"=="1" (
    "%PY%" "%HERE%tracked.py" %ARGS%
    if errorlevel 1 pause
    exit /b %errorlevel%
)
if not exist "%PYW%" (
    echo %PYW% is missing; running with a console instead.
    "%PY%" "%HERE%tracked.py" %ARGS%
    if errorlevel 1 pause
    exit /b %errorlevel%
)
rem Quick check that Tk works in this environment before starting without
rem a console (an error there would otherwise be invisible).
"%PY%" -c "import tkinter; tkinter.Tcl()" 2>"%TEMP%\tracked-tk-check.txt"
if errorlevel 1 (
    echo trackED can't start: Tk doesn't work in %VENV%.
    type "%TEMP%\tracked-tk-check.txt"
    echo.
    echo Try:  trackED.cmd --reinstall     or, for details:  trackED.cmd --check
    pause
    exit /b 1
)
start "" "%PYW%" "%HERE%tracked.py" %ARGS%
exit /b 0

:find_python
set "SYSPY="
for /f "delims=" %%I in ('py -3 -c "import sys; assert sys.version_info >= (3, 8); print(sys.executable)" 2^>nul') do set "SYSPY=%%I"
if defined SYSPY exit /b 0
rem (the Microsoft Store "python" alias prints nothing here, so it's skipped)
for /f "delims=" %%I in ('python -c "import sys; assert sys.version_info >= (3, 8); print(sys.executable)" 2^>nul') do set "SYSPY=%%I"
if defined SYSPY exit /b 0
for /d %%D in ("%LocalAppData%\Programs\Python\Python3*") do (
    if exist "%%D\python.exe" set "SYSPY=%%D\python.exe"
)
exit /b 0

:install_python
where winget >nul 2>&1
if not errorlevel 1 (
    winget install -e --id Python.Python.3.12 --scope user --accept-source-agreements --accept-package-agreements
    exit /b 0
)
echo Downloading the Python installer from python.org ...
powershell -NoProfile -ExecutionPolicy Bypass -Command "Invoke-WebRequest -UseBasicParsing -Uri 'https://www.python.org/ftp/python/3.12.10/python-3.12.10-amd64.exe' -OutFile \"$env:TEMP\python-3.12.10-amd64.exe\""
if not exist "%TEMP%\python-3.12.10-amd64.exe" (
    echo Download failed. Install Python from https://www.python.org/downloads/ and run trackED.cmd again.
    exit /b 1
)
"%TEMP%\python-3.12.10-amd64.exe" /passive InstallAllUsers=0 PrependPath=1 Include_tcltk=1 Include_pip=1 Include_launcher=1
exit /b 0
