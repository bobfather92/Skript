import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("skript_window", ROOT / "skript.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


assert module._centred_window_geometry(0, 0, 1920, 1240) == (320, 220, 1280, 800)
assert module._centred_window_geometry(0, 0, 1366, 728) == (43, 50, 1280, 628)

x, y, width, height = module._centred_window_geometry(100, 50, 900, 610)
assert (x, y, width, height) == (140, 90, 720, 480)
assert width > height
assert x - 100 == (800 - width) // 2
assert y - 50 == (560 - height) // 2

# A large desktop receives the requested Full HD default.
assert module._adaptive_desktop_geometry(0, 0, 2560, 1400) == (320, 160, 1920, 1080)

# A 1920x1080 display scales 16:9 down around the Windows taskbar/work area.
x, y, width, height = module._adaptive_desktop_geometry(0, 0, 1920, 1040)
assert (width, height) == (1707, 960)
assert abs((width / height) - (16 / 9)) < 0.002
assert (x, y) == (106, 40)

# Touch hardware keeps the previous touch-friendly sizing policy.
assert module._adaptive_desktop_geometry(0, 0, 1920, 1240, touch_mode=True) == (320, 220, 1280, 800)

class FakeTouchUser32:
    def GetSystemMetrics(self, metric):
        return {94: 0x81, 95: 10}.get(metric, 0)

assert module._windows_touch_capable(FakeTouchUser32()) is True


class FakeIconUser32:
    def __init__(self):
        self.messages = []

    def GetSystemMetrics(self, metric):
        return {11: 32, 12: 32, 49: 16, 50: 16}.get(metric, 0)

    def LoadImageW(self, _instance, _path, _kind, width, height, _flags):
        return (width * 100) + height

    def SendMessageW(self, hwnd, message, size, handle):
        self.messages.append((hwnd, message, size, handle))


fake_icons = FakeIconUser32()
assert module._set_windows_window_icon(
    123, user32=fake_icons, icon_path=ROOT / 'assets' / 'skript.ico'
) is True
assert [message[2] for message in fake_icons.messages] == [1, 0]
assert all(message[1] == 0x0080 for message in fake_icons.messages)


window_source = (ROOT / "skript.py").read_text(encoding="utf-8")
placement_source = window_source.split(
    "def _force_centred_browser_window", 1
)[1].split("def _find_free_port", 1)[0]
assert placement_source.count("_set_windows_window_icon(hwnd)") == 1
assert "_set_windows_app_identity(hwnd)" in placement_source
assert "SetWindowPos(hwnd, 0, x, y, width, height" in placement_source
assert "_enable_native_app_shell(hwnd)" not in placement_source
assert "target=_maintain_native_app_shell" not in placement_source
assert "_create_native_titlebar_overlay(hwnd)" in placement_source
assert "_create_native_browser_host(hwnd" not in placement_source
assert "_resize_native_host(" not in placement_source
control_source = window_source.split("def _window_control", 1)[1].split("def launch", 1)[0]
assert "_titlebar_overlay_is_active" in control_source
assert "_native_host_is_active" not in control_source
html_injection_source = window_source.split("def _get_html", 1)[1].split("class SFHandler", 1)[0]
assert "_SF_NATIVE_SHELL" not in html_injection_source
assert "_SF_NATIVE_TITLEBAR_OVERLAY" in html_injection_source
assert "'/api/window-events'" in window_source

# Chromium can hand the app window to an already-running Edge process. The
# launcher subprocess exiting must not stop Skript's local desktop service.
launch_source = (ROOT / "skript.py").read_text(encoding="utf-8").split("def launch():", 1)[1]
assert "cwd=tempfile.gettempdir()" in window_source
assert "_EDGE_PROC.poll()" not in launch_source
assert "while not _APP_SHUTDOWN_EVENT.wait(0.05)" in launch_source
assert "_pump_native_titlebar_overlay()" in launch_source
assert "_destroy_native_titlebar_overlay()" in launch_source
assert "--start-minimized" in window_source

print("Centred landscape desktop-window geometry tests passed.")
