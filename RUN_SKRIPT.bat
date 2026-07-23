@echo off
setlocal
cd /d "%~dp0"

set "PYTHON_EXE=%USERPROFILE%\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe"
if exist "%PYTHON_EXE%" goto RUN_SOURCE

where py >nul 2>&1
if %ERRORLEVEL% EQU 0 (
  set "PYTHON_EXE=py"
  goto RUN_SOURCE
)

where python >nul 2>&1
if %ERRORLEVEL% EQU 0 (
  set "PYTHON_EXE=python"
  goto RUN_SOURCE
)

set "INSTALLED_EXE=%LOCALAPPDATA%\ScriptForge\Skript.exe"
if exist "%INSTALLED_EXE%" (
  start "Skript" "%INSTALLED_EXE%"
  exit /b 0
)

echo Skript could not find Python or an installed Skript.exe.
echo Run Install.bat to install the application.
pause
exit /b 1

:RUN_SOURCE
start "Skript" "%PYTHON_EXE%" "%~dp0scriptforge.py"
exit /b 0
