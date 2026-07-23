"""List Windows processes locking files beneath a folder without stopping them."""
from __future__ import annotations

import ctypes
from ctypes import wintypes
import pathlib
import sys


CCH_RM_SESSION_KEY = 32
CCH_RM_MAX_APP_NAME = 255
CCH_RM_MAX_SVC_NAME = 63
ERROR_MORE_DATA = 234


class RM_UNIQUE_PROCESS(ctypes.Structure):
    _fields_ = [('dwProcessId', wintypes.DWORD), ('ProcessStartTime', wintypes.FILETIME)]


class RM_PROCESS_INFO(ctypes.Structure):
    _fields_ = [
        ('Process', RM_UNIQUE_PROCESS),
        ('strAppName', wintypes.WCHAR * (CCH_RM_MAX_APP_NAME + 1)),
        ('strServiceShortName', wintypes.WCHAR * (CCH_RM_MAX_SVC_NAME + 1)),
        ('ApplicationType', ctypes.c_int),
        ('AppStatus', wintypes.ULONG),
        ('TSSessionId', wintypes.DWORD),
        ('bRestartable', wintypes.BOOL),
    ]


def locking_processes(folder: pathlib.Path):
    files = [str(path.resolve()) for path in folder.rglob('*') if path.is_file()]
    if not files:
        return []

    restart_manager = ctypes.WinDLL('rstrtmgr', use_last_error=True)
    restart_manager.RmStartSession.argtypes = [ctypes.POINTER(wintypes.DWORD), wintypes.DWORD, wintypes.LPWSTR]
    restart_manager.RmStartSession.restype = wintypes.DWORD
    restart_manager.RmRegisterResources.argtypes = [
        wintypes.DWORD, wintypes.UINT, ctypes.POINTER(wintypes.LPCWSTR),
        wintypes.UINT, ctypes.c_void_p, wintypes.UINT, ctypes.c_void_p,
    ]
    restart_manager.RmRegisterResources.restype = wintypes.DWORD
    restart_manager.RmGetList.argtypes = [
        wintypes.DWORD, ctypes.POINTER(wintypes.UINT), ctypes.POINTER(wintypes.UINT),
        ctypes.POINTER(RM_PROCESS_INFO), ctypes.POINTER(wintypes.DWORD),
    ]
    restart_manager.RmGetList.restype = wintypes.DWORD
    restart_manager.RmEndSession.argtypes = [wintypes.DWORD]
    restart_manager.RmEndSession.restype = wintypes.DWORD

    session = wintypes.DWORD()
    key = ctypes.create_unicode_buffer(CCH_RM_SESSION_KEY + 1)
    result = restart_manager.RmStartSession(ctypes.byref(session), 0, key)
    if result:
        raise OSError(result, 'RmStartSession failed')
    try:
        for offset in range(0, len(files), 100):
            chunk = files[offset:offset + 100]
            resources = (wintypes.LPCWSTR * len(chunk))(*chunk)
            result = restart_manager.RmRegisterResources(
                session.value, len(chunk), resources, 0, None, 0, None
            )
            if result:
                raise OSError(result, 'RmRegisterResources failed')

        needed = wintypes.UINT()
        count = wintypes.UINT()
        reasons = wintypes.DWORD()
        result = restart_manager.RmGetList(
            session.value, ctypes.byref(needed), ctypes.byref(count), None, ctypes.byref(reasons)
        )
        if result == 0:
            return []
        if result != ERROR_MORE_DATA:
            raise OSError(result, 'RmGetList failed')
        entries = (RM_PROCESS_INFO * needed.value)()
        count.value = needed.value
        result = restart_manager.RmGetList(
            session.value, ctypes.byref(needed), ctypes.byref(count), entries, ctypes.byref(reasons)
        )
        if result:
            raise OSError(result, 'RmGetList failed')
        return [
            {
                'pid': int(item.Process.dwProcessId),
                'name': item.strAppName,
                'service': item.strServiceShortName,
                'restartable': bool(item.bRestartable),
            }
            for item in entries[:count.value]
        ]
    finally:
        restart_manager.RmEndSession(session.value)


def main():
    if sys.platform != 'win32' or len(sys.argv) != 2:
        raise SystemExit('Usage: windows_lock_diagnostic.py <folder>')
    folder = pathlib.Path(sys.argv[1]).resolve()
    if not folder.is_dir():
        raise SystemExit(f'Folder not found: {folder}')
    locks = locking_processes(folder)
    if not locks:
        print('No Restart Manager file locks found.')
        return
    for lock in locks:
        service = f" service={lock['service']}" if lock['service'] else ''
        print(f"pid={lock['pid']} name={lock['name']}{service} restartable={lock['restartable']}")


if __name__ == '__main__':
    main()
