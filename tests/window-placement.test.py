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


class FakeDragUser32:
    def __init__(self):
        self.released = 0
        self.points = [(321, 654), (341, 664), (371, 684)]
        self.button_states = [0x8000, 0x8000, 0]
        self.positions = []

    def GetCursorPos(self, pointer):
        x, y = self.points.pop(0)
        pointer._obj.x = x
        pointer._obj.y = y
        return 1

    def GetWindowRect(self, _hwnd, pointer):
        pointer._obj.left = 100
        pointer._obj.top = 200
        pointer._obj.right = 900
        pointer._obj.bottom = 800
        return 1

    def ReleaseCapture(self):
        self.released += 1
        return 1

    def GetAsyncKeyState(self, _key):
        return self.button_states.pop(0)

    def SetWindowPos(self, hwnd, insert_after, x, y, width, height, flags):
        self.positions.append((hwnd, insert_after, x, y, width, height, flags))
        return True


fake_drag = FakeDragUser32()
drag_worker = module._start_native_window_drag(456, user32=fake_drag)
assert drag_worker is True
for _ in range(100):
    if len(fake_drag.positions) == 2:
        break
    module.time.sleep(0.001)
assert fake_drag.released == 1
assert [(position[2], position[3]) for position in fake_drag.positions] == [
    (120, 210),
    (150, 230),
]
assert all(position[6] == 0x4015 for position in fake_drag.positions)


class FakeFrameUser32:
    def GetWindowRect(self, _hwnd, pointer):
        pointer._obj.left = 92
        pointer._obj.top = 92
        pointer._obj.right = 1308
        pointer._obj.bottom = 908
        return 1


class FakeDwmApi:
    def DwmGetWindowAttribute(self, _hwnd, _attribute, pointer, _size):
        pointer._obj.left = 100
        pointer._obj.top = 100
        pointer._obj.right = 1300
        pointer._obj.bottom = 900
        return 0


assert module._visible_native_window_bounds(
    456, user32=FakeFrameUser32(), dwmapi=FakeDwmApi()
) == (100, 100, 1300, 900)


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
assert "_start_native_window_drag(hwnd, u32)" in control_source
assert "threading.Thread" in window_source
assert "GetAsyncKeyState(0x01)" in window_source
overlay_source = window_source.split(
    "def _sync_native_titlebar_overlay", 1
)[1].split("def _create_native_titlebar_overlay", 1)[0]
assert "geometry[2], geometry[3], 0x0010 | 0x0040" in overlay_source
assert "geometry[2], geometry[3], 0x0004 | 0x0010 | 0x0040" not in overlay_source
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
