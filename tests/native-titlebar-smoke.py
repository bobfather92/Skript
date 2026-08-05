"""Windows-only smoke test for Skript's native WebView2 desktop shell.

The test proves the top-level window belongs to Skript.exe rather than an Edge
app-mode process. It also exercises the genuine Windows caption through
maximise, restore, resize, and foreground-window changes.
"""

import argparse
import ctypes
import os
import subprocess
import time
import tkinter as tk
from ctypes import wintypes
from pathlib import Path


WM_CLOSE = 0x0010
WM_SYSCOMMAND = 0x0112
SC_MAXIMIZE = 0xF030
SC_RESTORE = 0xF120
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
GWL_STYLE = -16
WS_CAPTION = 0x00C00000
WS_SYSMENU = 0x00080000
WS_MINIMIZEBOX = 0x00020000
WS_MAXIMIZEBOX = 0x00010000
DWMWA_EXTENDED_FRAME_BOUNDS = 9

user32 = ctypes.windll.user32
dwmapi = ctypes.windll.dwmapi
try:
    user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(-4))
except Exception:
    try:
        user32.SetProcessDPIAware()
    except Exception:
        pass


class RECT(ctypes.Structure):
    _fields_ = [
        ("left", ctypes.c_long),
        ("top", ctypes.c_long),
        ("right", ctypes.c_long),
        ("bottom", ctypes.c_long),
    ]


class POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


def windows():
    found = []
    callback_type = ctypes.WINFUNCTYPE(
        ctypes.c_bool, wintypes.HWND, wintypes.LPARAM
    )

    def visit(hwnd, _lparam):
        visible = bool(user32.IsWindowVisible(hwnd))
        title = ctypes.create_unicode_buffer(512)
        class_name = ctypes.create_unicode_buffer(128)
        pid = wintypes.DWORD()
        user32.GetWindowTextW(hwnd, title, len(title))
        user32.GetClassNameW(hwnd, class_name, len(class_name))
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        rect = RECT()
        if user32.GetWindowRect(hwnd, ctypes.byref(rect)):
            found.append(
                {
                    "hwnd": int(hwnd),
                    "pid": int(pid.value),
                    "title": title.value,
                    "class": class_name.value,
                    "visible": visible,
                    "rect": (rect.left, rect.top, rect.right, rect.bottom),
                }
            )
        return True

    callback = callback_type(visit)
    user32.EnumWindows(callback, 0)
    return found


def visible_bounds(hwnd):
    rect = RECT()
    result = dwmapi.DwmGetWindowAttribute(
        hwnd, DWMWA_EXTENDED_FRAME_BOUNDS, ctypes.byref(rect), ctypes.sizeof(rect)
    )
    if result != 0:
        if not user32.GetWindowRect(hwnd, ctypes.byref(rect)):
            raise RuntimeError("Could not read the Skript window bounds.")
    return rect.left, rect.top, rect.right, rect.bottom


def browser_renderer_bounds(hwnd):
    renderers = []
    callback_type = ctypes.WINFUNCTYPE(
        ctypes.c_bool, wintypes.HWND, wintypes.LPARAM
    )

    def visit(child, _lparam):
        class_name = ctypes.create_unicode_buffer(128)
        user32.GetClassNameW(child, class_name, len(class_name))
        if class_name.value == "Chrome_RenderWidgetHostHWND":
            rect = RECT()
            if user32.GetWindowRect(child, ctypes.byref(rect)):
                area = max(0, rect.right - rect.left) * max(0, rect.bottom - rect.top)
                renderers.append(
                    (area, (rect.left, rect.top, rect.right, rect.bottom))
                )
        return True

    callback = callback_type(visit)
    user32.EnumChildWindows(hwnd, callback, 0)
    return max(renderers, default=(0, None), key=lambda item: item[0])[1]


def wait_for_renderer_bounds(hwnd, timeout=5):
    deadline = time.time() + timeout
    while time.time() < deadline:
        renderer = browser_renderer_bounds(hwnd)
        if renderer:
            return renderer
        time.sleep(0.05)
    return None


def assert_renderer_fills_window(frame, renderer, label):
    if not renderer:
        raise RuntimeError(f"{label}: Edge's editor renderer could not be found.")
    left_gap = max(0, renderer[0] - frame[0])
    right_gap = max(0, frame[2] - renderer[2])
    bottom_gap = max(0, frame[3] - renderer[3])
    if left_gap > 20 or right_gap > 20 or bottom_gap > 20:
        raise RuntimeError(
            f"{label}: the editor did not fill the window "
            f"(frame={frame}, renderer={renderer}, "
            f"gaps={left_gap},{right_gap},{bottom_gap})."
        )


def wait_for_browser(process_id, timeout):
    deadline = time.time() + timeout
    while time.time() < deadline:
        current = windows()
        candidates = [
            item
            for item in current
            if item["visible"]
            and item["title"].startswith("Skript")
            and item["pid"] == process_id
        ]
        browser = next(iter(candidates), None)
        if browser:
            return browser
        time.sleep(0.1)
    diagnostics = [
        item for item in windows()
        if item["pid"] == process_id or item["title"].startswith("Skript")
    ]
    raise RuntimeError(
        f"The packaged Skript window did not appear in time. Windows: {diagnostics}"
    )


def wait_for_zoomed(hwnd, expected, timeout=5):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if bool(user32.IsZoomed(hwnd)) == expected:
            return
        time.sleep(0.05)
    state = "maximise" if expected else "restore"
    raise RuntimeError(f"The native Windows titlebar did not {state} Skript.")


def assert_no_titlebar_overlay():
    overlays = [item for item in windows() if item["title"] == "Skript titlebar"]
    if overlays:
        raise RuntimeError(
            "The obsolete foreground titlebar overlay was created: "
            f"{overlays}"
        )


def assert_native_caption(hwnd):
    style = int(user32.GetWindowLongW(hwnd, GWL_STYLE)) & 0xFFFFFFFF
    required = WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX
    if style & required != required:
        raise RuntimeError(
            "Skript is missing genuine Windows titlebar controls "
            f"(style=0x{style:08X}, required=0x{required:08X})."
        )


def window_process_id(hwnd):
    pid = wintypes.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    return int(pid.value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("app", type=Path)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--screenshot", type=Path)
    args = parser.parse_args()
    app = args.app.resolve()
    if os.name != "nt":
        raise SystemExit("This smoke test requires Windows.")
    if not app.is_file():
        raise SystemExit(f"Skript executable not found: {app}")
    if any(
        item["visible"]
        and item["title"].startswith("Skript — Professional Screenwriting")
        for item in windows()
    ):
        raise SystemExit("Close the existing Skript window before running this test.")

    original_cursor = POINT()
    user32.GetCursorPos(ctypes.byref(original_cursor))
    process = subprocess.Popen(
        [str(app)], env={**os.environ, "SKRIPT_DIAGNOSTIC": "1"}
    )
    browser = None
    try:
        browser = wait_for_browser(process.pid, args.timeout)
        time.sleep(4.0)
        browser = wait_for_browser(process.pid, 5)
        assert_no_titlebar_overlay()

        related_windows = [
            item
            for item in windows()
            if item["visible"]
            and item["title"].startswith("Skript")
            and item["pid"] == process.pid
        ]
        if len(related_windows) != 1:
            raise RuntimeError(
                f"Expected one Skript window, found {len(related_windows)}."
            )

        hwnd = browser["hwnd"]
        if browser["pid"] != process.pid:
            raise RuntimeError(
                "The top-level Skript window is owned by another executable."
            )
        if browser["class"].startswith("Chrome_WidgetWin"):
            raise RuntimeError(
                "Skript is still using an external Edge app-mode window."
            )
        assert_native_caption(hwnd)
        frame = visible_bounds(hwnd)
        renderer = wait_for_renderer_bounds(hwnd)
        assert_renderer_fills_window(frame, renderer, "Normal window")

        if args.screenshot:
            from PIL import ImageGrab

            screenshot_path = args.screenshot.resolve()
            screenshot_path.parent.mkdir(parents=True, exist_ok=True)
            ImageGrab.grab(
                bbox=(frame[0] - 16, frame[1] - 16, frame[2] + 16, frame[3] + 16),
                all_screens=True,
            ).save(screenshot_path)
            print(
                f"Captured native frame={frame}, renderer={renderer} "
                f"to {screenshot_path}"
            )

        user32.SendMessageW(hwnd, WM_SYSCOMMAND, SC_MAXIMIZE, 0)
        wait_for_zoomed(hwnd, True)
        time.sleep(0.5)
        assert_no_titlebar_overlay()
        assert_renderer_fills_window(
            visible_bounds(hwnd),
            wait_for_renderer_bounds(hwnd),
            "Maximised window",
        )

        user32.SendMessageW(hwnd, WM_SYSCOMMAND, SC_RESTORE, 0)
        wait_for_zoomed(hwnd, False)
        time.sleep(0.5)
        assert_no_titlebar_overlay()
        frame = visible_bounds(hwnd)
        assert_renderer_fills_window(
            frame, wait_for_renderer_bounds(hwnd), "Restored window"
        )

        raw = RECT()
        if not user32.GetWindowRect(hwnd, ctypes.byref(raw)):
            raise RuntimeError("Could not read Skript's raw window bounds.")
        old_width = raw.right - raw.left
        old_height = raw.bottom - raw.top
        resized_width = max(900, old_width - 320)
        if not user32.SetWindowPos(
            hwnd, 0, raw.left, raw.top, resized_width, old_height, 0x0004 | 0x0010
        ):
            raise RuntimeError("Windows rejected the Skript resize test.")
        time.sleep(0.7)
        resized_frame = visible_bounds(hwnd)
        if resized_frame[2] - resized_frame[0] > frame[2] - frame[0] - 200:
            raise RuntimeError("The native Skript window did not resize as expected.")
        assert_no_titlebar_overlay()
        assert_native_caption(hwnd)
        assert_renderer_fills_window(
            resized_frame, wait_for_renderer_bounds(hwnd), "Resized window"
        )

        probe = tk.Tk()
        try:
            probe.title("Skript background-window test")
            probe.geometry("360x180+30+30")
            probe.update_idletasks()
            probe.update()
            probe_widget = int(probe.winfo_id())
            probe_hwnd = int(user32.GetParent(probe_widget) or probe_widget)
            probe_rect = RECT()
            if not user32.GetWindowRect(probe_hwnd, ctypes.byref(probe_rect)):
                raise RuntimeError("Could not read the focus-test window bounds.")
            # Windows may reject a programmatic SetForegroundWindow request.
            # A physical click exercises the exact action reported by users.
            user32.SetCursorPos(
                (probe_rect.left + probe_rect.right) // 2,
                (probe_rect.top + probe_rect.bottom) // 2,
            )
            user32.mouse_event(MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0)
            user32.mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)
            deadline = time.time() + 2
            while time.time() < deadline:
                probe.update()
                foreground = int(user32.GetForegroundWindow())
                if window_process_id(foreground) == os.getpid():
                    break
                time.sleep(0.05)
            if window_process_id(int(user32.GetForegroundWindow())) != os.getpid():
                raise RuntimeError("Another application could not take focus from Skript.")
            time.sleep(0.4)
            probe.update()
            if window_process_id(int(user32.GetForegroundWindow())) != os.getpid():
                raise RuntimeError("Skript forced itself back into the foreground.")
            assert_no_titlebar_overlay()
        finally:
            probe.destroy()

        print(
            "Native WebView2 desktop-shell smoke test passed: Skript.exe owned "
            "the top-level window, no foreground overlay was created, Windows "
            "caption controls remained active, maximise/restore and resize kept "
            "the editor fitted, and another app could take focus."
        )
    finally:
        user32.SetCursorPos(original_cursor.x, original_cursor.y)
        if browser:
            user32.PostMessageW(browser["hwnd"], WM_CLOSE, 0, 0)
        try:
            process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            process.terminate()
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill()


if __name__ == "__main__":
    main()
