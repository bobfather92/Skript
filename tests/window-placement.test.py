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


class FakeForegroundUser32:
    def __init__(self, foreground, roots=None, owners=None):
        self.foreground = foreground
        self.roots = roots or {}
        self.owners = owners or {}

    def GetForegroundWindow(self):
        return self.foreground

    def GetAncestor(self, hwnd, _flag):
        return self.roots.get(hwnd, hwnd)

    def GetWindow(self, hwnd, _flag):
        return self.owners.get(hwnd, 0)


assert module._native_titlebar_target_is_foreground(
    100, 200, FakeForegroundUser32(100)
) is True
assert module._native_titlebar_target_is_foreground(
    100, 200, FakeForegroundUser32(201, roots={201: 200})
) is True
assert module._native_titlebar_target_is_foreground(
    100, 200, FakeForegroundUser32(300)
) is False
assert module._native_titlebar_target_is_foreground(
    100, 200, FakeForegroundUser32(301, owners={301: 100})
) is True


class FakeOverlayRoot:
    def __init__(self):
        self.geometries = []
        self.deiconified = 0
        self.idle_updates = 0

    def geometry(self, value):
        self.geometries.append(value)

    def deiconify(self):
        self.deiconified += 1

    def update_idletasks(self):
        self.idle_updates += 1

    def withdraw(self):
        pass


class FakeOverlayUser32(FakeForegroundUser32):
    def __init__(self):
        super().__init__(100)
        self.positions = []
        self.overlay_rect = (105, 201, 995, 240)
        self.target_rect = (100, 200, 1000, 800)
        self.zoomed = False
        self.dpi = 96

    def IsWindow(self, _hwnd):
        return True

    def IsIconic(self, _hwnd):
        return False

    def IsZoomed(self, _hwnd):
        return self.zoomed

    def GetDpiForWindow(self, _hwnd):
        return self.dpi

    def IsWindowVisible(self, _hwnd):
        return True

    def GetWindowRect(self, hwnd, pointer):
        rect = self.overlay_rect if hwnd == 200 else self.target_rect
        pointer._obj.left, pointer._obj.top, pointer._obj.right, pointer._obj.bottom = rect
        return True

    def SetWindowPos(self, hwnd, insert_after, x, y, width, height, flags):
        self.positions.append((hwnd, insert_after, x, y, width, height, flags))
        if hwnd == 200:
            self.overlay_rect = (x, y, x + width, y + height)
        return True


fake_overlay_root = FakeOverlayRoot()
fake_overlay_user32 = FakeOverlayUser32()
measure_calls = []
clock_values = iter((0.0, 0.1, 1.1, 1.2, 1.3, 1.4))
module._TITLEBAR_OVERLAY_ROOT = fake_overlay_root
module._TITLEBAR_OVERLAY_HWND = 200
module._TITLEBAR_OVERLAY_TARGET = 100
module._TITLEBAR_OVERLAY_GEOMETRY = None
module._TITLEBAR_OVERLAY_INSETS = None
module._TITLEBAR_OVERLAY_NEXT_INSET_CHECK = 0.0
module._TITLEBAR_OVERLAY_TARGET_STATE = None


def fake_measure(_hwnd, _user32):
    measure_calls.append(True)
    return (5, 40, 5, 5)


for force in (True, False, False):
    assert module._sync_native_titlebar_overlay(
        force=force,
        user32=fake_overlay_user32,
        clock=lambda: next(clock_values),
        measure_insets=fake_measure,
        apply_region=lambda *_args: True,
    )

# Resizing must invalidate the cached right inset immediately, rather than
# leaving the caption controls wider than Edge's newly sized frame.
fake_overlay_user32.target_rect = (100, 200, 900, 800)
assert module._sync_native_titlebar_overlay(
    user32=fake_overlay_user32,
    clock=lambda: next(clock_values),
    measure_insets=fake_measure,
    apply_region=lambda *_args: True,
)

# Position-only movement repositions the overlay without re-enumerating Edge's
# renderer children. A DPI change does invalidate the measurement.
fake_overlay_user32.target_rect = (150, 250, 950, 850)
assert module._sync_native_titlebar_overlay(
    user32=fake_overlay_user32,
    clock=lambda: next(clock_values),
    measure_insets=fake_measure,
    apply_region=lambda *_args: True,
)
fake_overlay_user32.dpi = 120
assert module._sync_native_titlebar_overlay(
    user32=fake_overlay_user32,
    clock=lambda: next(clock_values),
    measure_insets=fake_measure,
    apply_region=lambda *_args: True,
)

assert len(measure_calls) == 4
assert len(fake_overlay_user32.positions) == 3
assert fake_overlay_root.geometries == [
    "890x39+105+201",
    "790x39+105+201",
    "790x39+155+251",
]

module._TITLEBAR_OVERLAY_ROOT = None
module._TITLEBAR_OVERLAY_HWND = None
module._TITLEBAR_OVERLAY_TARGET = None
module._TITLEBAR_OVERLAY_GEOMETRY = None
module._TITLEBAR_OVERLAY_INSETS = None
module._TITLEBAR_OVERLAY_NEXT_INSET_CHECK = 0.0
module._TITLEBAR_OVERLAY_TARGET_STATE = None


# A monitor-scale mismatch can make Tk's physical titlebar wider than the
# logical width requested through SetWindowPos. The physical-frame feedback
# must issue one narrower correction so the close button remains inside Edge.
scaled_overlay_root = FakeOverlayRoot()
scaled_overlay_user32 = FakeOverlayUser32()
scaled_regions = []
module._TITLEBAR_OVERLAY_ROOT = scaled_overlay_root
module._TITLEBAR_OVERLAY_HWND = 200
module._TITLEBAR_OVERLAY_TARGET = 100
module._TITLEBAR_OVERLAY_GEOMETRY = None
module._TITLEBAR_OVERLAY_INSETS = None
module._TITLEBAR_OVERLAY_NEXT_INSET_CHECK = 0.0
module._TITLEBAR_OVERLAY_TARGET_STATE = None


def scaled_visible_bounds(hwnd, user32=None):
    del user32
    if hwnd == 100:
        return (100, 200, 1000, 800)
    return (105, 201, 1028, 240)


assert module._sync_native_titlebar_overlay(
    force=True,
    user32=scaled_overlay_user32,
    clock=lambda: 0.0,
    measure_insets=lambda *_args: (5, 40, 5, 5),
    apply_region=lambda _hwnd, width, *_args: scaled_regions.append(width),
    visible_bounds=scaled_visible_bounds,
)
assert len(scaled_overlay_user32.positions) == 2
assert scaled_overlay_user32.positions[0][4] == 890
assert scaled_overlay_user32.positions[1][4] < 890
assert scaled_regions[-1] == scaled_overlay_user32.positions[1][4]

module._TITLEBAR_OVERLAY_ROOT = None
module._TITLEBAR_OVERLAY_HWND = None
module._TITLEBAR_OVERLAY_TARGET = None
module._TITLEBAR_OVERLAY_GEOMETRY = None
module._TITLEBAR_OVERLAY_INSETS = None
module._TITLEBAR_OVERLAY_NEXT_INSET_CHECK = 0.0
module._TITLEBAR_OVERLAY_TARGET_STATE = None


class FakeDesktopWindow:
    native = None

    def __init__(self):
        self.actions = []

    def minimize(self):
        self.actions.append('minimize')

    def maximize(self):
        self.actions.append('maximize')

    def restore(self):
        self.actions.append('restore')

    def destroy(self):
        self.actions.append('destroy')


fake_desktop = FakeDesktopWindow()
module._DESKTOP_WINDOW = fake_desktop
module._DESKTOP_CLOSE_APPROVED = False
assert module._window_control('minimize') is True
assert module._window_control('maximize') is True
assert module._window_control('close') is True
assert fake_desktop.actions == ['minimize', 'maximize', 'destroy']
assert module._DESKTOP_CLOSE_APPROVED is True
module._DESKTOP_WINDOW = None
module._DESKTOP_CLOSE_APPROVED = False


window_source = (ROOT / "skript.py").read_text(encoding="utf-8")
embedded_source = window_source.split(
    "def _run_embedded_webview", 1
)[1].split("def _enable_native_app_shell", 1)[0]
assert "import webview" in embedded_source
assert "webview.create_window(" in embedded_source
assert "webview.start(" in embedded_source
assert "gui='edgechromium'" in embedded_source
assert "private_mode=True" in embedded_source
assert "window.events.closing += closing" in embedded_source
assert "_publish_window_event('request-close')" in embedded_source
assert "_set_windows_window_icon(hwnd)" in embedded_source
assert "_set_windows_app_identity(hwnd)" in embedded_source
assert "--app=" not in embedded_source
control_source = window_source.split("def _window_control", 1)[1].split("def launch", 1)[0]
assert "window = _DESKTOP_WINDOW" in control_source
assert "window.minimize()" in control_source
assert "window.maximize()" in control_source
assert "window.restore()" in control_source
assert "window.destroy()" in control_source
assert "_DESKTOP_CLOSE_APPROVED = True" in control_source
assert "_EDGE_PROC" not in control_source
assert "threading.Thread" in window_source
assert "GetAsyncKeyState(0x01)" in window_source
overlay_source = window_source.split(
    "def _sync_native_titlebar_overlay", 1
)[1].split("def _create_native_titlebar_overlay", 1)[0]
assert "_native_titlebar_target_is_foreground" in overlay_source
assert "visible_bounds = visible_bounds or _visible_native_window_bounds" in overlay_source
assert "logical-to-physical scaling" in overlay_source
assert "corrected_width" in overlay_source
assert "side_left = max(0, int(left) - 1)" in overlay_source
assert "frame_gap = 1" in overlay_source
assert "visible_top = int(outer.top) + frame_gap" in overlay_source
assert "strip_height = max(28, min(64, int(top) - frame_gap))" in overlay_source
assert "_TITLEBAR_OVERLAY_NEXT_INSET_CHECK = now + 1.0" in overlay_source
assert "target_state_changed" in overlay_source
assert "Position-only movement is" in overlay_source
assert "no child-window enumeration, Tk" in overlay_source
assert "if not (was_hidden or force)" in overlay_source
assert "position_flags |= 0x0004" in overlay_source
assert "def _apply_titlebar_overlay_region" in window_source
assert "CreateRoundRectRgn" in window_source
assert "SetWindowRgn" in window_source
create_overlay_source = window_source.split(
    "def _create_native_titlebar_overlay", 1
)[1].split("def _pump_native_titlebar_overlay", 1)[0]
assert "widget.bind('<B1-Motion>', continue_drag)" in create_overlay_source
assert "widget.bind('<ButtonRelease-1>', end_drag)" in create_overlay_source
assert "if drag_state['was_zoomed'] and not drag_state['restored']" in create_overlay_source
assert "user32.SendMessageW(browser_hwnd, 0x0112, 0xF120, 0)" in create_overlay_source
assert "user32.SetWindowPos(\n                    browser_hwnd" in create_overlay_source
assert "'font': ('Segoe UI Symbol', 16)" in create_overlay_source
assert "'width': 3" in create_overlay_source
html_injection_source = window_source.split("def _get_html", 1)[1].split("class SFHandler", 1)[0]
assert "_SF_NATIVE_SHELL" not in html_injection_source
assert "window._SF_NATIVE_TITLEBAR=" in html_injection_source
assert "window._SF_NATIVE_TITLEBAR_OVERLAY=false" in html_injection_source
assert 'classList.add("sf-native-titlebar")' in html_injection_source
assert "'/api/window-events'" in window_source

# Skript owns the native top-level process. WebView2 is only its renderer.
launch_source = (ROOT / "skript.py").read_text(encoding="utf-8").split("def launch():", 1)[1]
assert "_enable_windows_dpi_awareness" not in window_source
assert "_EDGE_PROC.poll()" not in launch_source
assert "_set_windows_process_identity()" in launch_source
assert "_run_embedded_webview(url, low_perf)" in launch_source
assert "_APP_SHUTDOWN_EVENT.wait(1.5)" in launch_source
assert "_launch_edge(" not in launch_source
assert "_launch_chrome(" not in launch_source
assert "webbrowser.open(" not in launch_source
assert "_pump_native_titlebar_overlay()" not in launch_source
assert "_destroy_native_titlebar_overlay()" not in launch_source
assert "_cleanup_isolated_browser_profile()" not in launch_source
assert "stat.dwMemoryLoad >= 85 or available_gb < 1.5" in window_source

spec_source = (ROOT / "Skript.spec").read_text(encoding="utf-8")
assert "'webview'" in spec_source
assert "'webview.platforms.winforms'" in spec_source
assert "'webview.platforms.edgechromium'" in spec_source

print("Centred landscape desktop-window geometry tests passed.")
