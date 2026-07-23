import importlib.util
from pathlib import Path
import tempfile


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "skript_installer", ROOT / "installer" / "skript_installer.py"
)
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)


with tempfile.TemporaryDirectory(dir=ROOT / "tmp") as temp_dir:
    base = Path(temp_dir)
    target = base / "Programs" / "Skript"
    staging = base / "Programs" / "Skript.installing"
    projects = base / "Documents" / "Skript" / "scripts"
    legacy_projects = base / "Documents" / "ScriptForge" / "scripts"
    target.mkdir(parents=True)
    staging.mkdir(parents=True)
    projects.mkdir(parents=True)
    legacy_projects.mkdir(parents=True)

    (target / "old-only.dll").write_text("old", encoding="utf-8")
    (target / "Skript.exe").write_text("old app", encoding="utf-8")
    (staging / "Skript.exe").write_text("new app", encoding="utf-8")
    (staging / installer.APP_RUNTIME_DIR).mkdir()
    project = projects / "tester-project.script"
    project.write_text("user project", encoding="utf-8")
    legacy_project = legacy_projects / "legacy-project.script"
    legacy_project.write_text("legacy user project", encoding="utf-8")

    original_stop = installer._stop_installed_skript
    original_install_dir = installer.install_dir
    installer._stop_installed_skript = lambda _target: None
    installer.install_dir = lambda: target
    progress_updates = []
    try:
        installer._replace_application_files(
            staging, target, lambda value, status: progress_updates.append((value, status))
        )
    finally:
        installer._stop_installed_skript = original_stop
        installer.install_dir = original_install_dir

    assert (target / "Skript.exe").read_text(encoding="utf-8") == "new app"
    assert not (target / "old-only.dll").exists()
    assert not list(target.parent.glob("Skript.previous*"))
    assert project.read_text(encoding="utf-8") == "user project"
    assert legacy_project.read_text(encoding="utf-8") == "legacy user project"
    assert [status for _value, status in progress_updates] == [
        "Closing the existing Skript application...",
        "Replacing old application files...",
        "Finalising application files...",
    ]

    retry_target = base / "retry-cleanup"
    retry_target.mkdir()
    retry_events = []
    real_rmtree = installer.shutil.rmtree
    retry_count = {"value": 0}

    def flaky_rmtree(path):
        if Path(path) == retry_target and retry_count["value"] < 2:
            retry_count["value"] += 1
            raise PermissionError("simulated antivirus lock")
        return real_rmtree(path)

    installer.shutil.rmtree = flaky_rmtree
    try:
        installer._remove_tree_retry(
            retry_target,
            attempts=3,
            delay=0,
            on_retry=lambda attempt, total, _error: retry_events.append((attempt, total)),
        )
    finally:
        installer.shutil.rmtree = real_rmtree
    assert retry_events == [(1, 3), (2, 3)]
    assert not retry_target.exists()

    fallback_target = base / "Programs" / "SkriptFallback"
    fallback_staging = base / "Programs" / "SkriptFallback.installing"
    fallback_previous = base / "Programs" / "SkriptFallback.previous"
    fallback_target.mkdir()
    fallback_staging.mkdir()
    (fallback_target / "obsolete.dll").write_text("old", encoding="utf-8")
    (fallback_target / "Skript.exe").write_text("old app", encoding="utf-8")
    (fallback_staging / "Skript.exe").write_text("new app", encoding="utf-8")
    installer._replace_application_contents(
        fallback_staging, fallback_target, fallback_previous, lambda *_args: None
    )
    assert (fallback_target / "Skript.exe").read_text(encoding="utf-8") == "new app"
    assert not (fallback_target / "obsolete.dll").exists()
    assert (fallback_previous / "obsolete.dll").read_text(encoding="utf-8") == "old"
    assert not fallback_staging.exists()
    installer._remove_tree_retry(fallback_previous)

    locked_target = base / "Programs" / "SkriptLockedRuntime"
    locked_staging = base / "Programs" / "SkriptLockedRuntime.installing"
    locked_previous = base / "Programs" / "SkriptLockedRuntime.previous"
    old_runtime = locked_target / "_internal"
    new_runtime = locked_staging / installer.APP_RUNTIME_DIR
    old_runtime.mkdir(parents=True)
    new_runtime.mkdir(parents=True)
    (old_runtime / "old.dll").write_text("locked old runtime", encoding="utf-8")
    (locked_target / "Skript.exe").write_text("old app", encoding="utf-8")
    (locked_staging / "Skript.exe").write_text("new app", encoding="utf-8")
    (new_runtime / "new.dll").write_text("new runtime", encoding="utf-8")
    real_move_retry = installer._move_path_retry

    def hold_obsolete_runtime(source, destination, *args, **kwargs):
        if Path(source) == old_runtime:
            raise RuntimeError("simulated antivirus runtime lock")
        return real_move_retry(source, destination, *args, **kwargs)

    installer._move_path_retry = hold_obsolete_runtime
    try:
        deferred = installer._replace_application_contents(
            locked_staging, locked_target, locked_previous, lambda *_args: None
        )
    finally:
        installer._move_path_retry = real_move_retry
    assert deferred == [old_runtime]
    assert (locked_target / "Skript.exe").read_text(encoding="utf-8") == "new app"
    assert (locked_target / installer.APP_RUNTIME_DIR / "new.dll").is_file()
    assert (old_runtime / "old.dll").is_file()
    installer._remove_tree_retry(locked_previous)

    rollback_target = base / "Programs" / "SkriptRollback"
    rollback_staging = base / "Programs" / "SkriptRollback.installing"
    rollback_previous = base / "Programs" / "SkriptRollback.previous"
    rollback_target.mkdir()
    rollback_staging.mkdir()
    (rollback_target / "Skript.exe").write_text("known good app", encoding="utf-8")
    (rollback_staging / "Skript.exe").write_text("replacement app", encoding="utf-8")
    real_move_retry = installer._move_path_retry

    def fail_new_content(source, destination, *args, **kwargs):
        if Path(source).parent == rollback_staging:
            raise RuntimeError("simulated replacement failure")
        return real_move_retry(source, destination, *args, **kwargs)

    installer._move_path_retry = fail_new_content
    try:
        try:
            installer._replace_application_contents(
                rollback_staging, rollback_target, rollback_previous, lambda *_args: None
            )
            raise AssertionError("Fallback replacement failure must be reported")
        except RuntimeError as error:
            assert "simulated replacement failure" in str(error)
    finally:
        installer._move_path_retry = real_move_retry
    assert (rollback_target / "Skript.exe").read_text(encoding="utf-8") == "known good app"
    assert (rollback_staging / "Skript.exe").read_text(encoding="utf-8") == "replacement app"
    assert not rollback_previous.exists()

    original_cwd = Path.cwd()
    try:
        installer._detach_installer_working_directory()
        assert Path.cwd().name == "Skript-Setup-Work"
    finally:
        installer.os.chdir(original_cwd)

    installer.install_dir = lambda: target
    try:
        try:
            installer._assert_safe_application_target(projects.parent)
            raise AssertionError("Project folders must never pass the installer safety check")
        except RuntimeError:
            pass
    finally:
        installer.install_dir = original_install_dir

source = (ROOT / "installer" / "skript_installer.py").read_text(encoding="utf-8")
for required in (
    "ModifyPath", "--repair", "Repair Skript", "Finalising application files",
    "CreateToolhelp32Snapshot", "QueryFullProcessImageNameW",
    "Waiting for Windows to release the application folder",
    "Cleaning the incomplete installation",
    "Windows is holding the folder — switching replacement method",
    "_replace_application_contents", "_cleanup_old_application_paths",
    "_detach_installer_working_directory", "Skript-Setup.log",
):
    assert required in source
assert "Get-CimInstance Win32_Process" not in source
for required in ("SKRIPT_INSTALLER_TEST_MODE", "SKRIPT_INSTALLER_TEST_ROOT", "SkriptReleaseTests"):
    assert required in source

installer_spec = (ROOT / "SkriptInstaller.spec").read_text(encoding="utf-8")
assert "usable Tkinter/Tcl resources are required" in installer_spec
assert "_build_tk.Tcl()" in installer_spec

app_spec = (ROOT / "Skript.spec").read_text(encoding="utf-8")
assert "project_root / 'assets' / 'skript.ico'" in app_spec
assert "payload / APP_RUNTIME_DIR / 'assets' / 'skript.ico'" in source
assert "contents_directory='_runtime_1_0_0_3'" in app_spec

print("Installer repair and project-preserving replacement tests passed.")
