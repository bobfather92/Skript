"""Windows-only smoke test for the packaged Skript titlebar.

The test launches the supplied build, checks that its native overlay matches
the visible Edge frame, performs a real mouse drag, and restores the cursor.
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
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
DWMWA_EXTENDED_FRAME_BOUNDS = 9

user32 = ctypes.windll.user32
dwmapi = ctypes.windll.dwmapi


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
        if not user32.IsWindowVisible(hwnd):
            return True
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


def wait_for_windows(process_id, timeout):
    deadline = time.time() + timeout
    while time.time() < deadline:
        current = windows()
        overlay = next(
            (
                item
                for item in current
                if item["pid"] == process_id
                and item["class"].startswith("Tk")
                and item["title"] == "Skript titlebar"
            ),
            None,
        )
        browser = next(
            (
                item
                for item in current
                if item["class"].startswith("Chrome_WidgetWin")
                and item["title"].startswith("Skript")
            ),
            None,
        )
        if overlay and browser:
            return overlay, browser
        time.sleep(0.1)
    raise RuntimeError("The packaged Skript titlebar did not appear in time.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("app", type=Path)
    parser.add_argument("--timeout", type=float, default=30)
    args = parser.parse_args()
    app = args.app.resolve()
    if os.name != "nt":
        raise SystemExit("This smoke test requires Windows.")
    if not app.is_file():
        raise SystemExit(f"Skript executable not found: {app}")
    if any(item["title"] == "Skript titlebar" for item in windows()):
        raise SystemExit("Close the existing Skript window before running this test.")

    original_cursor = POINT()
    user32.GetCursorPos(ctypes.byref(original_cursor))
    process = subprocess.Popen([str(app)], env={**os.environ, "SKRIPT_DIAGNOSTIC": "1"})
    browser = None
    mouse_down = False
    try:
        overlay, browser = wait_for_windows(process.pid, args.timeout)
        frame_before = visible_bounds(browser["hwnd"])
        overlay_bounds = overlay["rect"]
        renderer_bounds = browser_renderer_bounds(browser["hwnd"])
        if abs(overlay_bounds[0] - frame_before[0]) > 2:
            raise RuntimeError("The titlebar left edge does not match the Skript window.")
        if abs(overlay_bounds[2] - frame_before[2]) > 2:
            raise RuntimeError("The titlebar right edge does not match the Skript window.")
        if renderer_bounds and overlay_bounds[3] < renderer_bounds[1] - 2:
            raise RuntimeError(
                "The titlebar does not fully cover Edge's own title strip "
                f"(overlay bottom {overlay_bounds[3]}, renderer top {renderer_bounds[1]})."
            )

        drag_x = overlay_bounds[0] + min(240, (overlay_bounds[2] - overlay_bounds[0]) // 2)
        drag_y = overlay_bounds[1] + max(2, (overlay_bounds[3] - overlay_bounds[1]) // 2)
        user32.SetCursorPos(drag_x, drag_y)
        hit_window = int(user32.WindowFromPoint(POINT(drag_x, drag_y)))
        hit_root = int(user32.GetAncestor(hit_window, 2))
        user32.mouse_event(MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0)
        mouse_down = True
        time.sleep(0.15)
        for step in range(1, 11):
            user32.SetCursorPos(drag_x + (step * 10), drag_y + (step * 6))
            time.sleep(0.025)
        user32.mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)
        mouse_down = False
        time.sleep(0.5)

        frame_after = visible_bounds(browser["hwnd"])
        moved_x = frame_after[0] - frame_before[0]
        moved_y = frame_after[1] - frame_before[1]
        if moved_x < 70 or moved_y < 35:
            direct_result = user32.SetWindowPos(
                browser["hwnd"], 0, frame_before[0] + 40, frame_before[1] + 40,
                0, 0, 0x0001 | 0x0004 | 0x0010,
            )
            time.sleep(0.3)
            direct_after = visible_bounds(browser["hwnd"])
            raise RuntimeError(
                "Holding the titlebar did not move Skript "
                f"(moved {moved_x}, {moved_y}; hit={hit_window}; root={hit_root}; "
                f"overlay={overlay['hwnd']}; direct={direct_result}; "
                f"direct-move={direct_after[0] - frame_before[0]},"
                f"{direct_after[1] - frame_before[1]})."
            )

        overlay_after, _browser_after = wait_for_windows(process.pid, 5)
        if abs(overlay_after["rect"][0] - frame_after[0]) > 2:
            raise RuntimeError("The titlebar did not follow the moved window.")
        if abs(overlay_after["rect"][2] - frame_after[2]) > 2:
            raise RuntimeError("The titlebar width changed after moving the window.")

        probe = tk.Tk()
        try:
            probe.title("Skript background-window test")
            probe.geometry("360x180+30+30")
            probe.update_idletasks()
            probe.update()
            probe_widget = int(probe.winfo_id())
            probe_hwnd = int(user32.GetParent(probe_widget) or probe_widget)
            user32.SetForegroundWindow(probe_hwnd)
            deadline = time.time() + 2
            while time.time() < deadline and user32.IsWindowVisible(overlay["hwnd"]):
                probe.update()
                time.sleep(0.05)
            if user32.IsWindowVisible(overlay["hwnd"]):
                raise RuntimeError(
                    "Skript's titlebar remained above another foreground application."
                )
            user32.SetForegroundWindow(browser["hwnd"])
            wait_for_windows(process.pid, 3)
        finally:
            probe.destroy()

        print(
            "Native titlebar smoke test passed: hold-drag moved Skript and "
            "the bar stayed aligned without covering another foreground app."
        )
    finally:
        if mouse_down:
            user32.mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)
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
