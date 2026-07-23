@echo off
setlocal EnableDelayedExpansion
cd /d "%~dp0"
title Skript Installer

:: ════════════════════════════════════════════════════════════════════════════
::  Skript — Launcher / Bootstrap
::  Ensures Python 3.10+ is present, then runs the GUI installer (Install.py).
::  No admin rights required — Python installs to %LOCALAPPDATA%.
:: ════════════════════════════════════════════════════════════════════════════

set PY_EXE=
set PY_OK=0
set MIN_MINOR=10

echo.
echo  Skript Installer
echo  ----------------------------------------------------------
echo.

:: ── 1. Try Windows Python Launcher (py.exe) — most reliable on Windows ──────
py --version >nul 2>&1
if !ERRORLEVEL! EQU 0 (
    for /f "tokens=2 delims= " %%V in ('py --version 2^>^&1') do set PY_VER=%%V
    call :CHECK_VER !PY_VER!
    if !PY_OK! EQU 1 (
        set PY_EXE=py
        goto :LAUNCH
    )
)

:: ── 2. Try "python" / "python3" from PATH ────────────────────────────────────
for %%C in (python python3) do (
    if !PY_OK! EQU 0 (
        %%C --version >nul 2>&1
        if !ERRORLEVEL! EQU 0 (
            for /f "tokens=2 delims= " %%V in ('%%C --version 2^>^&1') do set PY_VER=%%V
            call :CHECK_VER !PY_VER!
            if !PY_OK! EQU 1 (
                set PY_EXE=%%C
                goto :LAUNCH
            )
        )
    )
)

:: ── 3. Check known default install paths directly ────────────────────────────
for %%P in (
    "%LOCALAPPDATA%\Programs\Python\Python313\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python312\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python311\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python310\python.exe"
    "%PROGRAMFILES%\Python313\python.exe"
    "%PROGRAMFILES%\Python312\python.exe"
    "%PROGRAMFILES%\Python311\python.exe"
    "%PROGRAMFILES%\Python310\python.exe"
) do (
    if !PY_OK! EQU 0 (
        if exist %%P (
            for /f "tokens=2 delims= " %%V in ('%%P --version 2^>^&1') do set PY_VER=%%V
            call :CHECK_VER !PY_VER!
            if !PY_OK! EQU 1 (
                set "PY_EXE=%%~P"
                goto :LAUNCH
            )
        )
    )
)

:: ════════════════════════════════════════════════════════════════════════════
::  Python not found — download and install silently
:: ════════════════════════════════════════════════════════════════════════════
:AUTO_INSTALL

echo  Python 3.10+ was not found on this system.
echo  Skript will download and install Python automatically.
echo  No administrator password required -- installs for current user only.
echo.

:: Detect 32-bit vs 64-bit Windows
set PY_ARCH=amd64
if /i "%PROCESSOR_ARCHITECTURE%"=="x86" (
    if not defined PROCESSOR_ARCHITEW6432 set PY_ARCH=32
)

:: Python 3.12.9 — stable, small, includes tkinter
set PY_VER_NUM=3.12.9
if "%PY_ARCH%"=="amd64" (
    set PY_FILENAME=python-%PY_VER_NUM%-amd64.exe
) else (
    set PY_FILENAME=python-%PY_VER_NUM%.exe
)
set PY_URL=https://www.python.org/ftp/python/%PY_VER_NUM%/%PY_FILENAME%
set PY_INSTALLER=%TEMP%\sfg_%PY_FILENAME%

echo  Downloading Python %PY_VER_NUM% (%PY_ARCH%)...
echo  Source: %PY_URL%
echo.

powershell -NoProfile -NonInteractive -ExecutionPolicy Bypass -Command ^
  "$ProgressPreference='SilentlyContinue'; try { Invoke-WebRequest -Uri '%PY_URL%' -OutFile '%PY_INSTALLER%' -UseBasicParsing; exit 0 } catch { Write-Host ('Download error: ' + $_.Exception.Message); exit 1 }"

if !ERRORLEVEL! NEQ 0 (
    echo.
    echo  ERROR: Could not download Python. Please check your internet connection.
    echo.
    echo  Alternatively, install Python manually from https://www.python.org/downloads/
    echo  then run Install.bat again.
    echo.
    pause
    exit /b 1
)

echo  Download complete. Installing Python %PY_VER_NUM%...
echo  This may take 30-60 seconds -- please wait.
echo.

:: Silent install flags:
::   InstallAllUsers=0  — current user only, no UAC prompt
::   PrependPath=1      — adds Python to PATH for this user
::   Include_launcher=1 — installs py.exe launcher
::   Include_test=0     — skips test suite (saves ~30 MB)
::   SimpleInstall=1    — skips optional features screen
"%PY_INSTALLER%" /quiet ^
    InstallAllUsers=0 ^
    PrependPath=1 ^
    Include_launcher=1 ^
    Include_test=0 ^
    SimpleInstall=1

set INSTALL_RC=!ERRORLEVEL!
del /f /q "%PY_INSTALLER%" >nul 2>&1

if !INSTALL_RC! NEQ 0 (
    echo.
    echo  ERROR: Python installation failed (exit code !INSTALL_RC!).
    echo.
    echo  Please install Python 3.10+ manually from https://www.python.org
    echo  then re-run Install.bat.
    echo.
    pause
    exit /b 1
)

echo  Python %PY_VER_NUM% installed successfully!
echo.

:: ── Locate the freshly installed Python ──────────────────────────────────────
:: PATH is not refreshed in this cmd session after a silent install,
:: so we check known install locations directly first.

set PY_EXE=
for %%P in (
    "%LOCALAPPDATA%\Programs\Python\Python312\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python313\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python311\python.exe"
    "%LOCALAPPDATA%\Programs\Python\Python310\python.exe"
) do (
    if not defined PY_EXE (
        if exist %%P set "PY_EXE=%%~P"
    )
)

:: Fallback: query registry via PowerShell
if not defined PY_EXE (
    for /f "usebackq delims=" %%P in (
        `powershell -NoProfile -NonInteractive -ExecutionPolicy Bypass -Command "$v=@('3.12','3.13','3.11','3.10'); foreach($x in $v){try{$p=(Get-ItemProperty \"HKCU:\Software\Python\PythonCore\$x\InstallPath\" -EA Stop).'(default)';if($p){Write-Output ($p+'python.exe');break}}catch{}}"`
    ) do (
        if "%%P" NEQ "" if exist "%%P" set "PY_EXE=%%P"
    )
)

:: Last resort: py.exe launcher (was installed with Include_launcher=1)
if not defined PY_EXE (
    py --version >nul 2>&1
    if !ERRORLEVEL! EQU 0 set PY_EXE=py
)

if not defined PY_EXE (
    echo.
    echo  Python was installed but could not be located in this session.
    echo  Please close this window, open a NEW Command Prompt, and run:
    echo.
    echo    python Install.py
    echo.
    pause
    exit /b 1
)

set PY_OK=1

:: ════════════════════════════════════════════════════════════════════════════
::  Launch the GUI installer
:: ════════════════════════════════════════════════════════════════════════════
:LAUNCH

echo  Python ready: !PY_EXE!
echo  Launching Skript Installer...
echo.

"!PY_EXE!" Install.py
if !ERRORLEVEL! NEQ 0 (
    echo.
    echo  ERROR: The installer exited with an error.
    echo  Check failreport.txt next to Install.bat for details.
    echo.
    pause
)
goto :EOF

:: ════════════════════════════════════════════════════════════════════════════
::  Subroutine: CHECK_VER
::  Sets PY_OK=1 if version string (e.g. "3.12.5") is >= 3.MIN_MINOR
:: ════════════════════════════════════════════════════════════════════════════
:CHECK_VER
set _V=%~1
set _V=!_V:Python =!
for /f "tokens=1,2 delims=." %%A in ("!_V!") do (
    set _MAJOR=%%A
    set _MINOR=%%B
)
echo !_MAJOR!| findstr /r "^[0-9][0-9]*$" >nul 2>&1
if !ERRORLEVEL! NEQ 0 goto :EOF
echo !_MINOR!| findstr /r "^[0-9][0-9]*$" >nul 2>&1
if !ERRORLEVEL! NEQ 0 goto :EOF
if !_MAJOR! GEQ 3 (
    if !_MINOR! GEQ !MIN_MINOR! (
        set PY_OK=1
    )
)
goto :EOF
