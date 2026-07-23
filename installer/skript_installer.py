import os
import pathlib
import platform
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk

if os.name == 'nt':
    import winreg


APP_NAME = 'Skript'
APP_VERSION = '1.0.0.4'
PUBLISHER = 'Jake McNeil'
UNINSTALL_KEY = rf'Software\Microsoft\Windows\CurrentVersion\Uninstall\{APP_NAME}'
VERSION_MARKER = 'version.txt'
APP_RUNTIME_DIR = '_runtime_1_0_0_3'
OBSOLETE_RUNTIME_NAMES = {'_internal'}
INSTALLER_LOG = pathlib.Path(tempfile.gettempdir()) / 'Skript-Setup.log'


def _write_installer_log(message):
    """Write a small setup trace without ever interrupting installation."""
    try:
        with INSTALLER_LOG.open('a', encoding='utf-8') as stream:
            stream.write(f'[{time.strftime("%Y-%m-%d %H:%M:%S")}] {message}\n')
    except OSError:
        pass


def installer_test_root():
    """Return an isolated release-test root only when explicitly enabled."""
    if os.environ.get('SKRIPT_INSTALLER_TEST_MODE') != '1':
        return None
    raw = os.environ.get('SKRIPT_INSTALLER_TEST_ROOT', '').strip()
    if not raw:
        raise RuntimeError('SKRIPT_INSTALLER_TEST_ROOT is required in installer test mode.')
    root = pathlib.Path(raw).resolve()
    if len(root.parts) < 3 or root == pathlib.Path(root.anchor):
        raise RuntimeError('Installer test root is not a safe isolated directory.')
    return root


def uninstall_key():
    if installer_test_root() is not None:
        return rf'Software\SkriptReleaseTests\{APP_NAME}'
    return UNINSTALL_KEY


def resource_path(*parts):
    root = pathlib.Path(getattr(sys, '_MEIPASS', pathlib.Path(__file__).parent))
    return root.joinpath(*parts)


def install_dir():
    test_root = installer_test_root()
    if test_root is not None:
        return test_root / 'LocalAppData' / 'Programs' / APP_NAME
    return pathlib.Path(os.environ.get('LOCALAPPDATA', pathlib.Path.home() / 'AppData' / 'Local')) / 'Programs' / APP_NAME


def start_menu_link():
    test_root = installer_test_root()
    if test_root is not None:
        return test_root / 'AppData' / 'Microsoft' / 'Windows' / 'Start Menu' / 'Programs' / APP_NAME / f'{APP_NAME}.lnk'
    appdata = pathlib.Path(os.environ.get('APPDATA', pathlib.Path.home() / 'AppData' / 'Roaming'))
    return appdata / 'Microsoft' / 'Windows' / 'Start Menu' / 'Programs' / APP_NAME / f'{APP_NAME}.lnk'


def desktop_link():
    test_root = installer_test_root()
    if test_root is not None:
        return test_root / 'Desktop' / f'{APP_NAME}.lnk'
    return pathlib.Path.home() / 'Desktop' / f'{APP_NAME}.lnk'


def powershell_quote(value):
    return str(value).replace("'", "''")


def create_shortcut(link_path, target_path, working_dir, icon_path):
    link_path.parent.mkdir(parents=True, exist_ok=True)
    command = (
        "$w=New-Object -ComObject WScript.Shell;"
        f"$s=$w.CreateShortcut('{powershell_quote(link_path)}');"
        f"$s.TargetPath='{powershell_quote(target_path)}';"
        f"$s.WorkingDirectory='{powershell_quote(working_dir)}';"
        f"$s.IconLocation='{powershell_quote(icon_path)},0';"
        "$s.Save()"
    )
    subprocess.run(
        ['powershell.exe', '-NoProfile', '-NonInteractive', '-Command', command],
        check=True,
        creationflags=getattr(subprocess, 'CREATE_NO_WINDOW', 0),
    )


def register_uninstaller(target):
    uninstaller = target / 'Uninstall Skript.exe'
    with winreg.CreateKey(winreg.HKEY_CURRENT_USER, uninstall_key()) as key:
        values = {
            'DisplayName': APP_NAME,
            'DisplayVersion': APP_VERSION,
            'Publisher': PUBLISHER,
            'InstallLocation': str(target),
            'DisplayIcon': str(target / 'Skript.exe'),
            'UninstallString': f'"{uninstaller}" --uninstall',
            'ModifyPath': f'"{uninstaller}" --repair',
        }
        for name, value in values.items():
            winreg.SetValueEx(key, name, 0, winreg.REG_SZ, value)
        winreg.SetValueEx(key, 'NoModify', 0, winreg.REG_DWORD, 0)
        winreg.SetValueEx(key, 'NoRepair', 0, winreg.REG_DWORD, 0)


def detected_installed_version():
    """Return the installed version without reading or changing user projects."""
    target = install_dir()
    if not (target / 'Skript.exe').is_file():
        return ''
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, uninstall_key()) as key:
            value, _ = winreg.QueryValueEx(key, 'DisplayVersion')
            if value:
                return str(value).strip()
    except (FileNotFoundError, OSError):
        pass
    try:
        return (target / VERSION_MARKER).read_text(encoding='utf-8').strip()
    except OSError:
        return ''


def remove_registration():
    try:
        winreg.DeleteKey(winreg.HKEY_CURRENT_USER, uninstall_key())
    except FileNotFoundError:
        pass


def remove_shortcuts():
    for link in (start_menu_link(), desktop_link()):
        try:
            link.unlink()
        except FileNotFoundError:
            pass
    try:
        start_menu_link().parent.rmdir()
    except OSError:
        pass


def find_supported_browser():
    candidates = [
        pathlib.Path(os.environ.get('PROGRAMFILES(X86)', '')) / 'Microsoft' / 'Edge' / 'Application' / 'msedge.exe',
        pathlib.Path(os.environ.get('PROGRAMFILES', '')) / 'Microsoft' / 'Edge' / 'Application' / 'msedge.exe',
        pathlib.Path(os.environ.get('PROGRAMFILES', '')) / 'Google' / 'Chrome' / 'Application' / 'chrome.exe',
        pathlib.Path(os.environ.get('PROGRAMFILES(X86)', '')) / 'Google' / 'Chrome' / 'Application' / 'chrome.exe',
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    for command in ('msedge.exe', 'chrome.exe'):
        located = shutil.which(command)
        if located:
            return pathlib.Path(located)
    return None


def check_prerequisites(payload, progress):
    progress(4, 'Checking Windows and bundled components...')
    if os.name != 'nt' or platform.system() != 'Windows':
        raise RuntimeError('Skript requires Windows 10 or Windows 11.')
    if sys.getwindowsversion().major < 10:
        raise RuntimeError('Skript requires Windows 10 or newer.')

    required = [
        payload / 'Skript.exe',
        payload / APP_RUNTIME_DIR / 'assets' / 'skript-icon.png',
        payload / APP_RUNTIME_DIR / 'assets' / 'skript.ico',
        payload / APP_RUNTIME_DIR / 'vendor' / 'pdfjs' / 'pdf.min.mjs',
        payload / APP_RUNTIME_DIR / 'vendor' / 'pdfjs' / 'pdf.worker.min.mjs',
    ]
    missing = [path.name for path in required if not path.is_file()]
    if missing:
        raise RuntimeError('The setup payload is incomplete: ' + ', '.join(missing))
    if not find_supported_browser():
        raise RuntimeError('Microsoft Edge or Google Chrome is required. Install one browser, then run setup again.')
    if not shutil.which('powershell.exe'):
        raise RuntimeError('Windows PowerShell is required to create application shortcuts.')

    progress(7, 'Checking local service access and disk space...')
    probe_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        probe_socket.bind(('127.0.0.1', 0))
    except OSError as exc:
        raise RuntimeError(f'Skript cannot use the Windows local service: {exc}') from exc
    finally:
        probe_socket.close()

    target_parent = install_dir().parent
    target_parent.mkdir(parents=True, exist_ok=True)
    probe_file = target_parent / f'.skript-install-check-{os.getpid()}'
    try:
        probe_file.write_text('ok', encoding='ascii')
        probe_file.unlink()
    except OSError as exc:
        raise RuntimeError(f'The installation folder is not writable: {exc}') from exc

    payload_size = sum(path.stat().st_size for path in payload.rglob('*') if path.is_file())
    free_space = shutil.disk_usage(target_parent).free
    required_space = payload_size * 2 + 64 * 1024 * 1024
    if free_space < required_space:
        required_mb = max(1, required_space // (1024 * 1024))
        raise RuntimeError(f'At least {required_mb} MB of free disk space is required.')


def schedule_post_install_launch(app_exe):
    subprocess.Popen(
        [sys.executable, '--post-install-launch', str(app_exe)],
        close_fds=True,
        creationflags=(
            getattr(subprocess, 'DETACHED_PROCESS', 0)
            | getattr(subprocess, 'CREATE_NEW_PROCESS_GROUP', 0)
            | getattr(subprocess, 'CREATE_NO_WINDOW', 0)
        ),
    )


def post_install_launch(app_exe):
    time.sleep(1.5)
    if not app_exe.is_file():
        return
    subprocess.Popen(
        [str(app_exe)],
        cwd=str(app_exe.parent),
        close_fds=True,
        creationflags=(
            getattr(subprocess, 'DETACHED_PROCESS', 0)
            | getattr(subprocess, 'CREATE_NEW_PROCESS_GROUP', 0)
            | getattr(subprocess, 'CREATE_NO_WINDOW', 0)
        ),
    )


def _remove_tree_retry(path, attempts=20, delay=0.25, on_retry=None):
    """Remove an application directory, tolerating short AV/process locks."""
    path = pathlib.Path(path)
    last_error = None
    for attempt in range(attempts):
        try:
            shutil.rmtree(path)
            return
        except FileNotFoundError:
            return
        except OSError as exc:
            last_error = exc
            if on_retry is not None:
                try:
                    on_retry(attempt + 1, attempts, exc)
                except Exception:
                    pass
            time.sleep(delay)
    if path.exists():
        raise RuntimeError(f'Could not remove old Skript application files: {last_error}')


def _move_path_retry(source, destination, attempts=40, delay=0.25, on_retry=None):
    """Move one application file or directory with a bounded AV-lock retry."""
    source = pathlib.Path(source)
    destination = pathlib.Path(destination)
    last_error = None
    for attempt in range(attempts):
        try:
            source.replace(destination)
            return
        except OSError as exc:
            last_error = exc
            if on_retry is not None:
                try:
                    on_retry(attempt + 1, attempts, source, exc)
                except Exception:
                    pass
            time.sleep(delay)
    raise RuntimeError(f'Windows could not replace {source.name}: {last_error}') from last_error


def _replace_application_contents(staging, target, previous, progress):
    """Install new versioned content while deferring a locked obsolete runtime."""
    staging = pathlib.Path(staging)
    target = pathlib.Path(target)
    previous = pathlib.Path(previous)
    previous.mkdir(parents=False, exist_ok=False)
    moved_old = []
    moved_new = []
    deferred_old = []

    def waiting(attempt, total, source, _error):
        if attempt == 3 or attempt % 8 == 0:
            progress(68, f'Replacing {source.name} ({attempt}/{total})...')

    try:
        staged_children = list(staging.iterdir())
        new_names = {child.name.casefold() for child in staged_children}
        for child in staged_children:
            destination = target / child.name
            if destination.exists():
                backup = previous / child.name
                _move_path_retry(destination, backup, on_retry=waiting)
                moved_old.append((backup, destination))
            _move_path_retry(child, destination, on_retry=waiting)
            moved_new.append((destination, child))

        for child in list(target.iterdir()):
            if child.name.casefold() in new_names:
                continue
            destination = previous / child.name
            try:
                _move_path_retry(child, destination, attempts=8, on_retry=waiting)
                moved_old.append((destination, child))
            except RuntimeError:
                is_old_runtime = (
                    child.name in OBSOLETE_RUNTIME_NAMES
                    or (child.name.startswith('_runtime_') and child.name != APP_RUNTIME_DIR)
                )
                if not is_old_runtime:
                    raise
                deferred_old.append(child)
                progress(70, f'Keeping locked old runtime {child.name} for later cleanup...')
        staging.rmdir()
        return deferred_old
    except Exception as replacement_error:
        rollback_errors = []
        for installed, staged in reversed(moved_new):
            try:
                if installed.exists():
                    installed.replace(staged)
            except OSError as exc:
                rollback_errors.append(str(exc))
        for backup, installed in reversed(moved_old):
            try:
                if backup.exists():
                    backup.replace(installed)
            except OSError as exc:
                rollback_errors.append(str(exc))
        try:
            previous.rmdir()
        except OSError:
            pass
        detail = f' Rollback issue: {rollback_errors[0]}' if rollback_errors else ''
        raise RuntimeError(f'Application replacement failed: {replacement_error}.{detail}') from replacement_error


def _cleanup_old_application_paths(target, progress=None):
    """Best-effort cleanup that is never allowed to block a successful update."""
    target = pathlib.Path(target)
    candidates = list(target.parent.glob(target.name + '.previous*'))
    if target.exists():
        candidates.extend(
            child for child in target.iterdir()
            if child.is_dir() and (
                child.name in OBSOLETE_RUNTIME_NAMES
                or (child.name.startswith('_runtime_') and child.name != APP_RUNTIME_DIR)
            )
        )
    pending = []
    for candidate in candidates:
        try:
            _remove_tree_retry(candidate, attempts=4, delay=0.15)
        except RuntimeError:
            pending.append(candidate)
    if pending and progress is not None:
        progress(75, 'New application installed; locked old runtime cleanup was deferred.')
    return pending


def _detach_installer_working_directory():
    """Ensure Setup never holds the installed application directory open."""
    safe_directory = pathlib.Path(tempfile.gettempdir()) / 'Skript-Setup-Work'
    try:
        safe_directory.mkdir(parents=True, exist_ok=True)
        os.chdir(safe_directory)
    except OSError:
        try:
            os.chdir(tempfile.gettempdir())
        except OSError:
            pass


def _assert_safe_application_target(target):
    """Refuse any repair/update target that could overlap user documents."""
    resolved = pathlib.Path(target).resolve()
    expected = pathlib.Path(install_dir()).resolve()
    home = pathlib.Path.home().resolve()
    documents = (home / 'Documents').resolve()
    project_roots = {
        (documents / 'Skript').resolve(),
        (documents / 'ScriptForge').resolve(),  # protected legacy location
    }
    if resolved != expected:
        raise RuntimeError('Safety check stopped maintenance outside the registered Skript application folder.')
    if resolved.name.casefold() != APP_NAME.casefold():
        raise RuntimeError('Safety check stopped maintenance outside the Skript application folder.')
    if resolved in ({resolved.anchor and pathlib.Path(resolved.anchor), home, documents} | project_roots):
        raise RuntimeError('Safety check stopped maintenance from changing user projects.')
    if any(projects in resolved.parents or resolved in projects.parents for projects in project_roots):
        raise RuntimeError('Safety check stopped maintenance from changing user projects.')
    return resolved


def _stop_installed_skript(target):
    """Stop only Skript.exe launched from this installation without using WMI."""
    app_exe = pathlib.Path(target) / 'Skript.exe'
    if not app_exe.exists() or os.name != 'nt':
        return

    try:
        import ctypes
        from ctypes import wintypes

        class PROCESSENTRY32W(ctypes.Structure):
            _fields_ = [
                ('dwSize', wintypes.DWORD), ('cntUsage', wintypes.DWORD),
                ('th32ProcessID', wintypes.DWORD), ('th32DefaultHeapID', ctypes.c_size_t),
                ('th32ModuleID', wintypes.DWORD), ('cntThreads', wintypes.DWORD),
                ('th32ParentProcessID', wintypes.DWORD), ('pcPriClassBase', ctypes.c_long),
                ('dwFlags', wintypes.DWORD), ('szExeFile', wintypes.WCHAR * 260),
            ]

        kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel32.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
        kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
        kernel32.Process32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
        kernel32.Process32FirstW.restype = wintypes.BOOL
        kernel32.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
        kernel32.Process32NextW.restype = wintypes.BOOL
        kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel32.OpenProcess.restype = wintypes.HANDLE
        kernel32.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
        kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL
        kernel32.TerminateProcess.argtypes = [wintypes.HANDLE, wintypes.UINT]
        kernel32.TerminateProcess.restype = wintypes.BOOL
        kernel32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        kernel32.WaitForSingleObject.restype = wintypes.DWORD
        kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
        kernel32.CloseHandle.restype = wintypes.BOOL

        snapshot = kernel32.CreateToolhelp32Snapshot(0x00000002, 0)
        if snapshot == wintypes.HANDLE(-1).value:
            return
        expected = os.path.normcase(os.path.abspath(str(app_exe)))
        entry = PROCESSENTRY32W()
        entry.dwSize = ctypes.sizeof(entry)
        try:
            more = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while more:
                if entry.szExeFile.casefold() == 'skript.exe' and entry.th32ProcessID != os.getpid():
                    rights = 0x0001 | 0x1000 | 0x00100000
                    process = kernel32.OpenProcess(rights, False, entry.th32ProcessID)
                    if process:
                        try:
                            size = wintypes.DWORD(32768)
                            path_buffer = ctypes.create_unicode_buffer(size.value)
                            if (kernel32.QueryFullProcessImageNameW(process, 0, path_buffer, ctypes.byref(size))
                                    and os.path.normcase(os.path.abspath(path_buffer.value)) == expected):
                                if kernel32.TerminateProcess(process, 0):
                                    kernel32.WaitForSingleObject(process, 4000)
                        finally:
                            kernel32.CloseHandle(process)
                more = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
        finally:
            kernel32.CloseHandle(snapshot)
    except Exception:
        # The bounded directory replacement below reports a clear error if
        # Windows still has the installed application open.
        return


def _replace_application_files(staging, target, progress):
    """Atomically replace installed program files; never touches project data."""
    target = _assert_safe_application_target(target)
    staging = pathlib.Path(staging).resolve()
    if staging.parent != target.parent or staging.name != target.name + '.installing':
        raise RuntimeError('Safety check stopped an invalid Skript staging folder.')
    # A unique backup folder means a locked remnant from an earlier run can
    # never prevent this repair from installing the new application.
    previous = target.with_name(f'{target.name}.previous-{os.getpid()}')
    _cleanup_old_application_paths(target)
    progress(66, 'Closing the existing Skript application...')
    _stop_installed_skript(target)

    used_content_fallback = False
    if target.exists():
        progress(67, 'Replacing old application files...')
        last_error = None
        for attempt in range(8):
            try:
                target.replace(previous)
                last_error = None
                break
            except OSError as exc:
                last_error = exc
                if attempt == 3 or attempt == 7:
                    progress(
                        67,
                        f'Waiting for Windows to release the application folder ({attempt + 1}/8)...',
                    )
                time.sleep(0.25)
        if last_error is not None:
            progress(68, 'Windows is holding the folder — switching replacement method...')
            _replace_application_contents(staging, target, previous, progress)
            used_content_fallback = True

    if not used_content_fallback:
        try:
            staging.replace(target)
        except Exception:
            if previous.exists() and not target.exists():
                previous.replace(target)
            raise

    app_exe = target / 'Skript.exe'
    app_runtime = target / APP_RUNTIME_DIR
    if not app_exe.is_file() or not app_runtime.is_dir():
        raise RuntimeError('The new Skript application files did not pass installation validation.')

    progress(72, 'Finalising application files...')
    pending = _cleanup_old_application_paths(target, progress)
    if pending:
        _write_installer_log(
            'Installed the new application; deferred locked cleanup: '
            + ', '.join(str(path) for path in pending)
        )


def install_payload(create_desktop=True, progress=None):
    progress = progress or (lambda value, status: None)
    target = _assert_safe_application_target(install_dir())
    staging = target.with_name(target.name + '.installing')
    payload = resource_path('payload', 'Skript')
    check_prerequisites(payload, progress)
    progress(10, 'Preparing installation...')
    _remove_tree_retry(
        staging,
        attempts=40,
        on_retry=lambda attempt, total, _error: progress(
            10, f'Cleaning the incomplete installation ({attempt}/{total})...'
        ),
    )
    staging.parent.mkdir(parents=True, exist_ok=True)
    progress(25, 'Copying Skript files...')
    shutil.copytree(payload, staging)
    shutil.copy2(sys.executable, staging / 'Uninstall Skript.exe')
    (staging / VERSION_MARKER).write_text(APP_VERSION, encoding='utf-8')
    progress(65, 'Replacing old application files...')
    _replace_application_files(staging, target, progress)
    progress(78, 'Creating shortcuts...')
    app_exe = target / 'Skript.exe'
    create_shortcut(start_menu_link(), app_exe, target, app_exe)
    if create_desktop:
        create_shortcut(desktop_link(), app_exe, target, app_exe)
    else:
        try:
            desktop_link().unlink()
        except FileNotFoundError:
            pass
    progress(92, 'Registering uninstaller...')
    register_uninstaller(target)
    progress(100, 'Installation complete')
    return target


def uninstall_worker(target, notify=True):
    target = _assert_safe_application_target(target)
    time.sleep(1.2)
    last_error = None
    for _ in range(10):
        try:
            shutil.rmtree(target)
            last_error = None
            break
        except FileNotFoundError:
            last_error = None
            break
        except OSError as exc:
            last_error = exc
            time.sleep(0.5)
    if target.exists():
        message = 'Close Skript and run the uninstaller again.'
        if last_error:
            message += f'\n\n{last_error}'
        if notify:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror('Skript Uninstaller', message)
            root.destroy()
            return
        raise RuntimeError(message)
    remove_shortcuts()
    remove_registration()
    if notify:
        root = tk.Tk()
        root.withdraw()
        messagebox.showinfo('Skript Uninstaller', 'Skript has been removed from this computer.')
        root.destroy()


def begin_uninstall():
    root = tk.Tk()
    root.withdraw()
    if not messagebox.askyesno('Uninstall Skript', 'Remove Skript from this computer?\n\nClose Skript before continuing.'):
        root.destroy()
        return
    root.destroy()
    worker = pathlib.Path(tempfile.gettempdir()) / f'Skript-Uninstall-{os.getpid()}.exe'
    shutil.copy2(sys.executable, worker)
    subprocess.Popen(
        [str(worker), '--uninstall-worker', str(install_dir())],
        cwd=tempfile.gettempdir(),
        close_fds=True,
        creationflags=getattr(subprocess, 'DETACHED_PROCESS', 0) | getattr(subprocess, 'CREATE_NO_WINDOW', 0),
    )


def launch_repair_worker_if_needed():
    """Run an installed repair copy from Temp so its own folder can be replaced."""
    try:
        running_from_install = pathlib.Path(sys.executable).parent.resolve() == install_dir().resolve()
    except OSError:
        running_from_install = False
    if not running_from_install or '--repair-worker' in sys.argv:
        return False
    worker = pathlib.Path(tempfile.gettempdir()) / f'Skript-Repair-{os.getpid()}.exe'
    shutil.copy2(sys.executable, worker)
    subprocess.Popen(
        [str(worker), '--repair-worker'],
        cwd=tempfile.gettempdir(),
        close_fds=True,
        creationflags=getattr(subprocess, 'DETACHED_PROCESS', 0) | getattr(subprocess, 'CREATE_NO_WINDOW', 0),
    )
    return True


class RoundedButton(tk.Canvas):
    """Small canvas-backed button so Tk can display a genuinely rounded CTA."""
    def __init__(self, parent, text, command, width=92, height=36,
                 bg='#7657f6', fg='#ffffff', activebackground='#8a70ff',
                 disabledbackground='#454052'):
        parent_bg = parent.cget('bg')
        super().__init__(parent, width=width, height=height, bg=parent_bg,
                         highlightthickness=0, bd=0, cursor='hand2')
        self._text = text
        self._command = command
        self._fill = bg
        self._active_fill = activebackground
        self._disabled_fill = disabledbackground
        self._fg = fg
        self._state = 'normal'
        self.bind('<Enter>', lambda _event: self._draw(self._active_fill))
        self.bind('<Leave>', lambda _event: self._draw())
        self.bind('<ButtonRelease-1>', self._activate)
        self._draw()

    def _rounded_rect(self, x1, y1, x2, y2, radius, **kwargs):
        points = [
            x1 + radius, y1, x2 - radius, y1, x2, y1, x2, y1 + radius,
            x2, y2 - radius, x2, y2, x2 - radius, y2, x1 + radius, y2,
            x1, y2, x1, y2 - radius, x1, y1 + radius, x1, y1,
        ]
        return self.create_polygon(points, smooth=True, splinesteps=24, **kwargs)

    def _draw(self, hover_fill=None):
        self.delete('all')
        fill = self._disabled_fill if self._state == 'disabled' else (hover_fill or self._fill)
        self._rounded_rect(1, 1, int(self.cget('width')) - 1,
                           int(self.cget('height')) - 1, 17,
                           fill=fill, outline='')
        self.create_text(int(self.cget('width')) // 2,
                         int(self.cget('height')) // 2,
                         text=self._text, fill=self._fg,
                         font=('Segoe UI Semibold', 9))

    def _activate(self, _event):
        if self._state != 'disabled' and self._command:
            self._command()

    def configure(self, cnf=None, **kwargs):
        state = kwargs.pop('state', None)
        result = super().configure(cnf, **kwargs)
        if state is not None:
            self._state = str(state)
            self.configure(cursor='arrow' if self._state == 'disabled' else 'hand2')
            self._draw()
        return result

    config = configure

    def cget(self, key):
        if key == 'state':
            return self._state
        return super().cget(key)


class InstallerWindow:
    def __init__(self, force_repair=False):
        self.root = tk.Tk()
        self.root.title(f'{APP_NAME} Setup')
        self.root.resizable(False, False)
        self.root.configure(bg='#17171a')
        self.desktop_var = tk.BooleanVar(value=True)
        self.launch_var = tk.BooleanVar(value=True)
        self.status_var = tk.StringVar(value='Ready to install')
        self.installed_version = detected_installed_version()
        self.mode = ('repair' if force_repair or self.installed_version == APP_VERSION
                     else ('update' if self.installed_version else 'install'))
        if self.mode == 'repair':
            self.status_var.set(f'Version {APP_VERSION} is installed — ready to repair')
        elif self.mode == 'update':
            self.status_var.set(f'Version {self.installed_version} is installed — ready to update')
        self._build_ui()
        self._fit_window()
        self.root.bind('<Return>', lambda event: self.start_install())
        self.root.bind('<Escape>', lambda event: self.root.destroy())

    def _fit_window(self):
        self.root.update_idletasks()
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        width = min(max(520, self.root.winfo_reqwidth()), max(480, screen_width - 40))
        height = min(max(440, self.root.winfo_reqheight() + 12), max(420, screen_height - 40))
        x = max(0, (screen_width - width) // 2)
        y = max(0, (screen_height - height) // 2)
        self.root.geometry(f'{width}x{height}+{x}+{y}')

    def _build_ui(self):
        style = ttk.Style(self.root)
        style.theme_use('clam')
        style.configure('TProgressbar', troughcolor='#303034', background='#7657f6', borderwidth=0)

        header = tk.Frame(self.root, bg='#202024', height=112)
        header.pack(fill='x')
        header.pack_propagate(False)
        icon_file = resource_path('payload', 'Skript', APP_RUNTIME_DIR, 'assets', 'skript-icon.png')
        try:
            image = tk.PhotoImage(file=str(icon_file)).subsample(10, 10)
            icon = tk.Label(header, image=image, bg='#202024')
            icon.image = image
            icon.pack(side='left', padx=(24, 14), pady=16)
            self.root.iconphoto(True, image)
        except Exception:
            pass
        title = tk.Frame(header, bg='#202024')
        title.pack(side='left', fill='y', pady=24)
        heading = {'repair': 'Repair Skript', 'update': 'Update Skript', 'install': 'Install Skript'}[self.mode]
        tk.Label(title, text=heading, bg='#202024', fg='#ffffff', font=('Segoe UI Semibold', 18)).pack(anchor='w')
        tk.Label(title, text=f'Professional screenwriting  |  Version {APP_VERSION}', bg='#202024', fg='#a8a8b0', font=('Segoe UI', 9)).pack(anchor='w', pady=(5, 0))

        body = tk.Frame(self.root, bg='#17171a', padx=28, pady=22)
        body.pack(fill='both', expand=True)
        action_text = {
            'repair': 'Replace all application files and repair shortcuts',
            'update': f'Replace version {self.installed_version} with {APP_VERSION}',
            'install': 'Install for this Windows user',
        }[self.mode]
        tk.Label(body, text=action_text, bg='#17171a', fg='#f2f2f2', font=('Segoe UI Semibold', 11)).pack(anchor='w')
        tk.Label(body, text=str(install_dir()), bg='#17171a', fg='#8f8f98', font=('Segoe UI', 9), wraplength=450, justify='left').pack(anchor='w', pady=(5, 18))
        tk.Checkbutton(body, text='Create a desktop shortcut', variable=self.desktop_var, bg='#17171a', fg='#d7d7dc', activebackground='#17171a', activeforeground='#ffffff', selectcolor='#303034', font=('Segoe UI', 10)).pack(anchor='w')
        tk.Checkbutton(body, text='Launch Skript after installation', variable=self.launch_var, bg='#17171a', fg='#d7d7dc', activebackground='#17171a', activeforeground='#ffffff', selectcolor='#303034', font=('Segoe UI', 10)).pack(anchor='w', pady=(5, 18))
        safety_text = ('Repair and Update replace program files only. '
                       'Your projects, backups and recovery copies are never removed.')
        tk.Label(body, text=safety_text, bg='#17171a', fg='#b7a7ff', font=('Segoe UI Semibold', 9), wraplength=450, justify='left').pack(anchor='w', pady=(0, 3))
        tk.Label(body, text='Python, PDF import and Word import/export engines are included.', bg='#17171a', fg='#8f8f98', font=('Segoe UI', 9)).pack(anchor='w', pady=(0, 8))
        self.progress = ttk.Progressbar(body, mode='determinate', maximum=100)
        self.progress.pack(fill='x')
        tk.Label(body, textvariable=self.status_var, bg='#17171a', fg='#9999a2', font=('Segoe UI', 9)).pack(anchor='w', pady=(6, 16))

        actions = tk.Frame(body, bg='#17171a')
        actions.pack(fill='x')
        self.cancel_btn = tk.Button(actions, text='Cancel', command=self.root.destroy, bg='#29292d', fg='#e4e4e8', activebackground='#35353a', activeforeground='#ffffff', relief='flat', padx=18, pady=7, font=('Segoe UI Semibold', 9))
        self.cancel_btn.pack(side='right')
        button_text = {'repair': 'Repair', 'update': 'Update', 'install': 'Install'}[self.mode]
        self.install_btn = RoundedButton(actions, text=button_text, command=self.start_install,
                                         bg='#7657f6', fg='#ffffff', activebackground='#8a70ff')
        self.install_btn.pack(side='right', padx=(0, 8))

    def start_install(self):
        if str(self.install_btn.cget('state')) == 'disabled':
            return
        self.install_btn.configure(state='disabled')
        self.cancel_btn.configure(state='disabled')
        self.create_desktop = self.desktop_var.get()
        self.launch_after = self.launch_var.get()
        threading.Thread(target=self.install, daemon=True).start()

    def set_progress(self, value, status):
        _write_installer_log(f'{value}% {status}')
        self.root.after(0, lambda: (self.progress.configure(value=value), self.status_var.set(status)))

    def install(self):
        try:
            self.installed_target = install_payload(self.create_desktop, self.set_progress)
            self.root.after(0, self.finish)
        except Exception as exc:
            error = str(exc)
            self.root.after(0, lambda error=error: self.fail(error))

    def finish(self):
        result = {'repair': 'Skript was repaired successfully.',
                  'update': 'Skript was updated successfully.',
                  'install': 'Skript was installed successfully.'}[self.mode]
        messagebox.showinfo('Skript Setup', result)
        self.root.destroy()
        if self.launch_after:
            schedule_post_install_launch(self.installed_target / 'Skript.exe')

    def fail(self, error):
        _write_installer_log(f'FAILED: {error}')
        self.status_var.set(f'Installation failed: {error}')
        try:
            self.root.attributes('-topmost', True)
            messagebox.showerror(
                'Skript Setup',
                f'Skript could not be installed.\n\n{error}\n\nDiagnostic log: {INSTALLER_LOG}',
                parent=self.root,
            )
        finally:
            self.root.attributes('-topmost', False)
        self.install_btn.configure(state='normal')
        self.cancel_btn.configure(state='normal')

    def run(self):
        self.root.mainloop()


def main():
    _detach_installer_working_directory()
    if '--post-install-launch' in sys.argv:
        index = sys.argv.index('--post-install-launch')
        if len(sys.argv) > index + 1:
            post_install_launch(pathlib.Path(sys.argv[index + 1]))
        return
    if '--uninstall-worker' in sys.argv:
        index = sys.argv.index('--uninstall-worker')
        target = pathlib.Path(sys.argv[index + 1]) if len(sys.argv) > index + 1 else install_dir()
        uninstall_worker(target, notify='--silent' not in sys.argv)
        return
    if '--uninstall' in sys.argv:
        begin_uninstall()
        return
    if '--repair' in sys.argv and launch_repair_worker_if_needed():
        return
    if '--silent' in sys.argv:
        target = install_payload(create_desktop='--no-desktop' not in sys.argv)
        if '--launch' in sys.argv:
            schedule_post_install_launch(target / 'Skript.exe')
        return
    InstallerWindow(force_repair=('--repair' in sys.argv or '--repair-worker' in sys.argv)).run()


if __name__ == '__main__':
    main()
