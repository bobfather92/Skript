#!/usr/bin/env python3
"""
Skript — GUI Installer
Builds Skript.exe from skript.py using PyInstaller.
Zero extra dependencies — uses only Python stdlib (tkinter, subprocess, threading).
"""

import sys
import os
import subprocess
import threading
import pathlib
import shutil
import time
import tkinter as tk
from tkinter import font as tkfont

# Hide the console window immediately when launched via python.exe (not pythonw)
if sys.platform == 'win32':
    try:
        import ctypes
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 0)  # SW_HIDE
    except Exception:
        pass



# ── Version ─────────────────────────────────────────────────────────────────
VERSION = '1.0.0.4'

# ── Paths ──────────────────────────────────────────────────────────────────
HERE        = pathlib.Path(__file__).parent.resolve()
SCRIPT      = HERE / 'skript.py'
BUILD_DIR   = HERE / '_build'

# Install destination: %LOCALAPPDATA%\Programs\Skript
# Using LocalAppData (like VS Code / Slack / Discord) avoids UAC elevation,
# prevents PyInstaller running-as-admin warnings, and avoids Defender locking.
_LOCALAPPDATA = pathlib.Path(os.environ.get('LOCALAPPDATA',
                    pathlib.Path.home() / 'AppData' / 'Local'))
INSTALL_DIR  = _LOCALAPPDATA / 'Programs' / 'Skript'
EXE_PATH     = INSTALL_DIR / 'Skript.exe'
VERSION_FILE = INSTALL_DIR / 'version.txt'

# Legacy dist/ path (cleaned up if found next to installer)
DIST_DIR    = HERE / 'dist'

# ── Palette ────────────────────────────────────────────────────────────────
BG          = '#0f0f17'
CARD        = '#1a1a26'
BORDER      = '#2a2a3a'
ACCENT      = '#7b5ef8'          # purple
ACCENT_HOV  = '#9474ff'
GREEN       = '#3ecf8e'
RED         = '#e05c5c'
TEXT        = '#e8e8f0'
TEXT_DIM    = '#7070a0'
TRACK       = '#252535'
BAR         = '#7b5ef8'

WIN_W, WIN_H = 520, 520


class InstallerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title('Skript Installer')
        self.root.geometry(f'{WIN_W}x{WIN_H}')
        self.root.resizable(False, False)
        self.root.configure(bg=BG)
        self._center()

        # Try to set a window icon (silently skip if unavailable)
        try:
            self.root.iconbitmap(default='')
        except Exception:
            pass

        self._state      = 'idle'   # idle | running | done | error
        self._log_lines  = []
        self._output_buf = []       # accumulates all subprocess output for failreport
        self._progress   = 0.0      # 0.0 – 1.0
        self._phase      = 0        # 0=pip  1=compile  2=done

        self._build_ui()

    # ── Layout ────────────────────────────────────────────────────────────

    def _build_ui(self):
        root = self.root

        # ── Header ──────────────────────────────────────────────────────
        hdr = tk.Frame(root, bg=BG)
        hdr.pack(fill='x', padx=36, pady=(40, 0))

        logo_font  = tkfont.Font(family='Segoe UI', size=26, weight='bold')
        sub_font   = tkfont.Font(family='Segoe UI', size=11)

        tk.Label(hdr, text='Skript', font=logo_font,
                 bg=BG, fg=TEXT).pack(anchor='w')
        tk.Label(hdr, text='Professional Screenwriting  ·  Installer',
                 font=sub_font, bg=BG, fg=TEXT_DIM).pack(anchor='w', pady=(2, 0))

        # Divider
        tk.Frame(root, bg=BORDER, height=1).pack(fill='x', padx=36, pady=(20, 0))

        # ── Info card ──────────────────────────────────────────────────
        card = tk.Frame(root, bg=CARD, bd=0, highlightthickness=1,
                        highlightbackground=BORDER)
        card.pack(fill='x', padx=36, pady=20)

        info_font = tkfont.Font(family='Segoe UI', size=10)
        pad = dict(padx=18)

        tk.Label(card, text='What this installer does:', font=tkfont.Font(
            family='Segoe UI', size=10, weight='bold'),
            bg=CARD, fg=TEXT, anchor='w').pack(fill='x', padx=18, pady=(14, 6))

        steps = [
            ('①', 'Installs Python 3.12 if not already present'),
            ('②', 'Installs PyInstaller (Python build tool)'),
            ('③', 'Compiles Skript into a single .exe  (~2 min)'),
            ('④', 'Places Skript.exe in AppData — ready to run'),
        ]
        for num, desc in steps:
            row = tk.Frame(card, bg=CARD)
            row.pack(fill='x', padx=18, pady=2)
            tk.Label(row, text=num, font=info_font, bg=CARD,
                     fg=ACCENT, width=2, anchor='w').pack(side='left')
            tk.Label(row, text=desc, font=info_font, bg=CARD,
                     fg=TEXT_DIM, anchor='w').pack(side='left', padx=(6, 0))

        tk.Frame(card, bg=BORDER, height=1).pack(fill='x', padx=18, pady=(12, 0))

        note_font = tkfont.Font(family='Segoe UI', size=9)
        tk.Label(card, text='Installs locally in AppData  ·  No admin required  ·  Python auto-installed if missing',
                 font=note_font, bg=CARD, fg=TEXT_DIM, anchor='w', wraplength=440, justify='left'
                 ).pack(fill='x', padx=18, pady=(8, 14))

        # ── Progress bar ────────────────────────────────────────────────
        pb_frame = tk.Frame(root, bg=BG)
        pb_frame.pack(fill='x', padx=36, pady=(0, 4))

        self._status_var = tk.StringVar(value='Ready to install')
        status_font = tkfont.Font(family='Segoe UI', size=10)
        tk.Label(pb_frame, textvariable=self._status_var, font=status_font,
                 bg=BG, fg=TEXT_DIM, anchor='w', wraplength=440, justify='left').pack(fill='x', pady=(0, 6))

        # Canvas-based progress bar
        self._bar_canvas = tk.Canvas(pb_frame, height=6, bg=TRACK,
                                     highlightthickness=0, bd=0)
        self._bar_canvas.pack(fill='x')
        self._bar_fill = self._bar_canvas.create_rectangle(
            0, 0, 0, 6, fill=BAR, width=0)

        self._bar_canvas.bind('<Configure>', self._on_bar_resize)

        # ── Install button ───────────────────────────────────────────────
        btn_frame = tk.Frame(root, bg=BG)
        btn_frame.pack(fill='x', padx=36, pady=(14, 20))

        self._btn = tk.Button(
            btn_frame, text='Install',
            font=tkfont.Font(family='Segoe UI', size=12, weight='bold'),
            bg=ACCENT, fg='white', activebackground=ACCENT_HOV,
            activeforeground='white', relief='flat', bd=0,
            cursor='hand2', pady=11,
            command=self._start_install)
        self._btn.pack(fill='x')

        self._btn.bind('<Enter>', lambda _: self._btn.config(bg=ACCENT_HOV)
                       if self._state == 'idle' else None)
        self._btn.bind('<Leave>', lambda _: self._btn.config(bg=ACCENT)
                       if self._state == 'idle' else None)

    # ── Helpers ───────────────────────────────────────────────────────────

    def _center(self):
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x  = (sw - WIN_W) // 2
        y  = (sh - WIN_H) // 2
        self.root.geometry(f'{WIN_W}x{WIN_H}+{x}+{y}')

    def _on_bar_resize(self, _event=None):
        self._draw_bar(self._progress)

    def _draw_bar(self, frac: float):
        self._progress = max(0.0, min(1.0, frac))
        w = self._bar_canvas.winfo_width()
        if w < 2:
            return
        fill_w = int(w * self._progress)
        self._bar_canvas.coords(self._bar_fill, 0, 0, fill_w, 6)

    def _log(self, msg: str, tag: str = ''):
        pass   # progress shown via status label and bar only

    def _set_status(self, msg: str, colour: str = TEXT_DIM):
        def _do():
            self._status_var.set(msg)
            for w in self.root.winfo_children():
                pass   # label is updated via StringVar
        self.root.after(0, _do)

    def _set_progress(self, frac: float):
        self.root.after(0, lambda: self._draw_bar(frac))

    # ── Install flow ──────────────────────────────────────────────────────

    def _start_install(self):
        if self._state != 'idle':
            return
        self._state = 'running'
        self._btn.config(text='Installing…', state='disabled',
                         bg='#3a3a55', cursor='arrow')
        threading.Thread(target=self._run_install, daemon=True).start()

    def _run_install(self):
        self._cmd_output = []   # reset capture buffer for this run
        try:
            self._do_install()
        except Exception as exc:
            import traceback
            tb = traceback.format_exc()
            self._cmd_output.append(tb)
            self._finish_error(str(exc))

    def _run_cmd(self, cmd, log_prefix=''):
        """Run a subprocess, capture all output. Returns returncode."""
        flags = subprocess.CREATE_NO_WINDOW if sys.platform == 'win32' else 0
        proc = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding='utf-8', errors='replace',
            cwd=str(HERE), creationflags=flags)
        for line in proc.stdout:
            line = line.rstrip()
            if line:
                self._cmd_output.append(line)
        proc.wait()
        return proc.returncode

    def _write_failreport(self, error_msg: str):
        """Write failreport.txt next to the installer with full diagnostic info."""
        import datetime
        lines = [
            'Skript Installer — Failure Report',
            '=' * 60,
            f'Date/Time : {datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")}',
            f'Python    : {sys.version}',
            f'Installer : {__file__}',
            f'Install to: {INSTALL_DIR}',
            f'Version   : {VERSION}',
            '',
            'ERROR',
            '-' * 60,
            error_msg,
            '',
            'FULL OUTPUT',
            '-' * 60,
        ] + (self._cmd_output if hasattr(self, '_cmd_output') and self._cmd_output
             else ['(no subprocess output captured)'])
        report_path = HERE / 'failreport.txt'
        try:
            report_path.write_text('\n'.join(lines), encoding='utf-8')
        except Exception:
            pass
        return report_path
    def _kill_running_processes(self):
        """Terminate any running Skript or earlier preview processes before install."""
        if sys.platform != 'win32':
            return

        former_stem = 'Script' + 'Forge'
        targets = ['Skript.exe', 'skript.exe', former_stem + '.exe', former_stem.lower() + '.exe']
        killed = []

        # Use tasklist + taskkill — available on all Windows versions, no extra libs needed
        try:
            result = subprocess.run(
                ['tasklist', '/FO', 'CSV', '/NH'],
                capture_output=True, text=True,
                creationflags=subprocess.CREATE_NO_WINDOW, timeout=10
            )
            running = [line.strip('"').split('","') for line in result.stdout.splitlines() if line]
        except Exception:
            running = []

        our_pid = os.getpid()

        for row in running:
            if len(row) < 2:
                continue
            name = row[0].lower()
            try:
                pid = int(row[1])
            except ValueError:
                continue

            # Kill Skript itself and earlier preview builds.
            if name in [t.lower() for t in targets]:
                try:
                    subprocess.run(
                        ['taskkill', '/F', '/PID', str(pid)],
                        creationflags=subprocess.CREATE_NO_WINDOW,
                        capture_output=True, timeout=10
                    )
                    killed.append(f'Skript (PID {pid})')
                except Exception:
                    pass

            # Kill python/pythonw processes that are NOT this installer
            if name in ('python.exe', 'pythonw.exe', 'python3.exe') and pid != our_pid:
                # Only kill if it's running from the same install folder (old app instance)
                try:
                    loc_result = subprocess.run(
                        ['wmic', 'process', 'where', f'ProcessId={pid}', 'get', 'ExecutablePath'],
                        capture_output=True, text=True,
                        creationflags=subprocess.CREATE_NO_WINDOW, timeout=10
                    )
                    exe_path = loc_result.stdout.strip().splitlines()[-1].strip().lower()
                    if str(INSTALL_DIR).lower() in exe_path or str(HERE).lower() in exe_path:
                        subprocess.run(
                            ['taskkill', '/F', '/PID', str(pid)],
                            creationflags=subprocess.CREATE_NO_WINDOW,
                            capture_output=True, timeout=10
                        )
                        killed.append(f'Python (PID {pid})')
                except Exception:
                    pass

        if killed:
            self._set_status(f'Stopped running processes: {", ".join(killed)}')
            time.sleep(1.0)
        else:
            self._set_status('No conflicting processes found')
            time.sleep(0.5)

    def _do_install(self):
        # ── Step 0a: Kill any running Skript / Python instances ──────────────
        self._set_status('Checking for running processes…')
        self._set_progress(0.01)
        self._kill_running_processes()

        # ── Step 0b: Remove old build if present ─────────────────────
        self._set_status('Checking for previous installation…')
        self._set_progress(0.03)
        self._remove_old_build()

        # ── Step 1: Confirm Python ────────────────────────────────────────
        self._set_status('Checking Python…')
        self._set_progress(0.05)
        py_ver = sys.version.split()[0]
        self._log(f'\n[1/4]  Python {py_ver}  ({sys.executable})', 'ok')
        self._set_status(f'Python {py_ver}  ✓')
        self._set_progress(0.12)

        # ── Step 2: pip install pyinstaller ──────────────────────────
        self._log('\n[2/4]  Installing PyInstaller…', 'head')
        self._set_status('Installing PyInstaller…')
        self._set_progress(0.18)

        pip_cmd = [sys.executable, '-m', 'pip', 'install', 'pyinstaller', '--upgrade', '-q']
        self._log('  > ' + ' '.join(pip_cmd), 'dim')
        rc = self._run_cmd(pip_cmd)
        if rc != 0:
            raise RuntimeError('pip install pyinstaller failed (see log above).')

        self._log('       PyInstaller ready', 'ok')
        self._set_progress(0.30)

        # ── Step 3: PyInstaller compile ──────────────────────────────
        self._log('\n[3/4]  Compiling Skript.exe  (this takes 1–3 minutes)…', 'head')
        self._set_status('Compiling… please wait (~2 min)')
        self._set_progress(0.35)

        # PyInstaller must NOT run as admin (deprecated in 6.x, blocked in 7.x).
        # Compile into a temp folder next to the installer, then copy to Program Files.
        TEMP_DIST = HERE / '_dist_tmp'
        TEMP_DIST.mkdir(parents=True, exist_ok=True)
        TEMP_EXE  = TEMP_DIST / 'Skript.exe'

        # Animate the bar slowly while compile runs in background
        compile_done = threading.Event()

        def _animate():
            p = 0.35
            while not compile_done.is_set():
                p = min(0.88, p + 0.003)
                self._set_progress(p)
                time.sleep(0.25)

        anim = threading.Thread(target=_animate, daemon=True)
        anim.start()

        rc = self._run_cmd([
            sys.executable, '-m', 'PyInstaller',
            '--onefile',
            '--noupx',
            '--windowed',
            '--name', 'Skript',
            '--distpath', str(TEMP_DIST),
            '--workpath', str(BUILD_DIR),
            '--specpath', str(BUILD_DIR),
            '--hidden-import', 'tkinter',
            '--hidden-import', 'tkinter.filedialog',
            str(SCRIPT),
        ])

        compile_done.set()
        anim.join()

        if rc != 0:
            raise RuntimeError('PyInstaller compilation failed (see log above).')

        if not TEMP_EXE.exists():
            raise RuntimeError(f'Build succeeded but EXE not found at: {TEMP_EXE}')

        # ── Step 4: Copy EXE into install folder ─────────────────────
        self._set_status('Installing to AppData…')
        self._set_progress(0.92)
        INSTALL_DIR.mkdir(parents=True, exist_ok=True)
        shutil.copy2(str(TEMP_EXE), str(EXE_PATH))

        # Clean up temp dist folder
        shutil.rmtree(TEMP_DIST, ignore_errors=True)

        size_mb = EXE_PATH.stat().st_size / 1024 / 1024
        self._log(f'\n  ✓  Skript.exe  ({size_mb:.1f} MB)', 'ok')
        self._log(f'     {EXE_PATH}', 'dim')

        # Write version file so future installs can detect and upgrade
        try:
            VERSION_FILE.write_text(VERSION, encoding='utf-8')
        except Exception:
            pass

        self._set_progress(1.0)
        self._finish_success()

    def _remove_old_build(self):
        """Check for an existing installation, compare versions, and clean up if upgrading.
        Never touches user data in the Documents project folders."""

        # ── Check for a previous installation ─────────────────────────────
        if not INSTALL_DIR.exists():
            # Also clean up any legacy dist/ folder next to the installer
            if DIST_DIR.exists():
                shutil.rmtree(DIST_DIR, ignore_errors=True)
            self._set_status('No previous installation found')
            time.sleep(0.8)
            return

        # ── Read installed version ─────────────────────────────────────────
        installed_ver = None
        if VERSION_FILE.exists():
            try:
                installed_ver = VERSION_FILE.read_text(encoding='utf-8').strip()
            except Exception:
                pass

        if installed_ver == VERSION:
            self._set_status(f'Reinstalling version {VERSION}…')
            time.sleep(0.8)
        elif installed_ver:
            self._set_status(f'Upgrading {installed_ver} → {VERSION}…')
            time.sleep(1.0)
        else:
            self._set_status('Previous installation found — updating…')
            time.sleep(0.8)

        # ── Remove old app files only — preserve user data ────────────────
        # User data lives in ~/Documents/Skript — never touched here.
        # We only delete files inside INSTALL_DIR (the Program Files folder).
        try:
            shutil.rmtree(INSTALL_DIR, ignore_errors=True)
            self._set_status('Old version removed  ✓')
        except Exception as e:
            self._set_status(f'Warning: could not fully remove old version ({e})')
        time.sleep(0.6)

        # Clean up legacy dist/ next to installer if present
        if DIST_DIR.exists():
            shutil.rmtree(DIST_DIR, ignore_errors=True)

        # Clean up stale .spec and _build/
        for spec in HERE.glob('*.spec'):
            try: spec.unlink()
            except Exception: pass
        if BUILD_DIR.exists():
            shutil.rmtree(BUILD_DIR, ignore_errors=True)

    # ── Finish states ─────────────────────────────────────────────────────

    def _finish_success(self):
        def _do():
            self._state = 'done'
            self._set_status('Installation complete  ✓')
            self._bar_canvas.itemconfig(self._bar_fill, fill=GREEN)
            self._btn.config(
                text='Done  ✓', bg='#1e4a35',
                fg=GREEN, state='disabled', cursor='arrow')
            self.root.after(400, self._ask_launch)
        self.root.after(0, _do)

    def _finish_error(self, msg: str):
        report_path = self._write_failreport(msg)
        short = str(msg).split('\n')[0][:72]
        def _do():
            self._state = 'error'
            self._set_status(
                f'Failed: {short}\n'
                f'Details saved to: {report_path.name}  (next to Install.bat)'
            )
            self._bar_canvas.itemconfig(self._bar_fill, fill=RED)
            self._btn.config(
                text='Retry', state='normal',
                bg='#5a1e1e', fg=RED, cursor='hand2',
                command=self._retry)
        self.root.after(0, _do)

    def _retry(self):
        self._state = 'idle'
        self._draw_bar(0)
        self._bar_canvas.itemconfig(self._bar_fill, fill=BAR)
        self._set_status('Ready to install')
        self._btn.config(text='Install', state='normal',
                         bg=ACCENT, fg='white', cursor='hand2',
                         command=self._start_install)
        self._start_install()

    # ── Launch dialog ─────────────────────────────────────────────────────

    def _create_shortcuts(self, desktop: bool, start_menu: bool):
        """Create Windows shortcuts via PowerShell WScript.Shell COM object.
        Paths are passed as PowerShell variables to avoid quoting/space issues."""
        if sys.platform != 'win32':
            return
        if not desktop and not start_menu:
            return

        exe_path   = str(EXE_PATH).replace("'", "''")   # escape PS single quotes
        work_dir   = str(EXE_PATH.parent).replace("'", "''")

        def _make_lnk(destination_expr: str) -> str:
            """Return PS script that creates a .lnk at destination_expr."""
            return (
                f"$ws = New-Object -ComObject WScript.Shell; "
                f"$lnk = $ws.CreateShortcut({destination_expr}); "
                f"$lnk.TargetPath = '{exe_path}'; "
                f"$lnk.WorkingDirectory = '{work_dir}'; "
                f"$lnk.Description = 'Skript Professional Screenwriting'; "
                f"$lnk.Save()"
            )

        if desktop:
            dest = r'([Environment]::GetFolderPath("Desktop") + "\Skript.lnk")'
            ps   = _make_lnk(dest)
            try:
                result = subprocess.run(
                    ['powershell', '-NoProfile', '-NonInteractive',
                     '-ExecutionPolicy', 'Bypass', '-Command', ps],
                    creationflags=subprocess.CREATE_NO_WINDOW,
                    capture_output=True, text=True, timeout=15
                )
                if result.returncode == 0:
                    self._log('  ✓  Desktop shortcut created', 'ok')
                else:
                    self._log(f'  ⚠  Desktop shortcut: {result.stderr.strip()[:120]}', 'err')
            except Exception as e:
                self._log(f'  ⚠  Desktop shortcut failed: {e}', 'err')

        if start_menu:
            dest = r'([Environment]::GetFolderPath("StartMenu") + "\Skript.lnk")'
            ps   = _make_lnk(dest)
            try:
                result = subprocess.run(
                    ['powershell', '-NoProfile', '-NonInteractive',
                     '-ExecutionPolicy', 'Bypass', '-Command', ps],
                    creationflags=subprocess.CREATE_NO_WINDOW,
                    capture_output=True, text=True, timeout=15
                )
                if result.returncode == 0:
                    self._log('  ✓  Start Menu shortcut created', 'ok')
                else:
                    self._log(f'  ⚠  Start Menu: {result.stderr.strip()[:120]}', 'err')
            except Exception as e:
                self._log(f'  ⚠  Start Menu shortcut failed: {e}', 'err')

    def _ask_launch(self):
        # Guard: prevent double-call
        if getattr(self, '_launch_dlg_open', False):
            return
        self._launch_dlg_open = True

        dlg = tk.Toplevel(self.root)
        dlg.title('Skript — Installation Complete')
        dlg.configure(bg=CARD)
        dlg.resizable(False, False)
        dlg.grab_set()

        dlg_w, dlg_h = 400, 300
        px = self.root.winfo_x() + (WIN_W - dlg_w) // 2
        py = self.root.winfo_y() + (WIN_H - dlg_h) // 2
        dlg.geometry(f'{dlg_w}x{dlg_h}+{px}+{py}')

        head_font  = tkfont.Font(family='Segoe UI', size=13, weight='bold')
        body_font  = tkfont.Font(family='Segoe UI', size=10)
        small_font = tkfont.Font(family='Segoe UI', size=9)
        btn_font   = tkfont.Font(family='Segoe UI', size=10, weight='bold')

        tk.Label(dlg, text='Installation complete!',
                 font=head_font, bg=CARD, fg=TEXT).pack(pady=(24, 4))
        tk.Label(dlg, text='Skript is ready to use.',
                 font=body_font, bg=CARD, fg=TEXT_DIM).pack()

        # ── Shortcut options ───────────────────────────────────────────
        tk.Frame(dlg, bg=BORDER, height=1).pack(fill='x', padx=24, pady=(16, 10))
        tk.Label(dlg, text='Add shortcuts:', font=small_font,
                 bg=CARD, fg=TEXT_DIM, anchor='w').pack(fill='x', padx=28)

        # BooleanVars must specify master=dlg so they bind to this Toplevel
        var_desktop    = tk.BooleanVar(master=dlg, value=True)
        var_start_menu = tk.BooleanVar(master=dlg, value=True)

        chk = dict(bg=CARD, fg=TEXT, activebackground=CARD, activeforeground=TEXT,
                   selectcolor=TRACK, font=body_font, anchor='w', cursor='hand2',
                   relief='flat', bd=0)

        tk.Checkbutton(dlg, text='Desktop shortcut',
                       variable=var_desktop, **chk).pack(fill='x', padx=32, pady=(4, 0))
        tk.Checkbutton(dlg, text='Start Menu shortcut',
                       variable=var_start_menu, **chk).pack(fill='x', padx=32, pady=(2, 0))

        tk.Frame(dlg, bg=BORDER, height=1).pack(fill='x', padx=24, pady=(14, 0))

        # ── Buttons ────────────────────────────────────────────────────
        btn_row = tk.Frame(dlg, bg=CARD)
        btn_row.pack(pady=16)

        def _do_shortcuts():
            d = var_desktop.get()
            s = var_start_menu.get()
            if d or s:
                threading.Thread(
                    target=self._create_shortcuts,
                    args=(d, s), daemon=True
                ).start()

        def _launch():
            _do_shortcuts()
            dlg.destroy()
            try:
                os.startfile(str(EXE_PATH))
            except AttributeError:
                subprocess.Popen([str(EXE_PATH)])
            self.root.after(1200, self.root.destroy)

        def _close():
            _do_shortcuts()
            dlg.destroy()

        tk.Button(btn_row, text='Launch Now', font=btn_font,
                  bg=ACCENT, fg='white', activebackground=ACCENT_HOV,
                  activeforeground='white', relief='flat', bd=0,
                  cursor='hand2', padx=20, pady=9,
                  command=_launch).pack(side='left', padx=(0, 10))

        tk.Button(btn_row, text='Close', font=btn_font,
                  bg=TRACK, fg=TEXT_DIM, activebackground=BORDER,
                  activeforeground=TEXT, relief='flat', bd=0,
                  cursor='hand2', padx=20, pady=9,
                  command=_close).pack(side='left')


# ── Entry point ────────────────────────────────────────────────────────────

def main():
    root = tk.Tk()
    app  = InstallerApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
