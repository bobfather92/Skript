#!/usr/bin/env python3
"""
Skript — Professional Screenwriting
Zero-dependency desktop app.  Works with Python 3.8 through 3.14+.
No pip installs required at runtime.

How it works:
  - The full Skript HTML/CSS/JS is compressed and embedded below.
  - A tiny stdlib HTTP server handles file dialogs and PDF decompression.
  - Microsoft Edge (built into every Windows 10/11 PC) opens in --app mode:
    no address bar, no tabs, looks and feels like a native application.
  - On macOS/Linux it opens in the default browser as fallback.

Run:   python skript.py
Build: python skript.py --build    (creates a standalone EXE via PyInstaller)
"""
import sys, os, gzip, base64, zlib, json, socket, threading, pathlib
import subprocess, tempfile, shutil, time, webbrowser, hashlib, secrets, uuid
import io, re, zipfile
import xml.etree.ElementTree as ET
from http.server import BaseHTTPRequestHandler, HTTPServer, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs


def _rolling_backup_path(path, index):
    return path.with_name(path.name + f'.bak{index}')


def _atomic_write_bytes(path, payload, backup_count=3):
    """Durably replace a file while retaining recent complete versions."""
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = payload.encode('utf-8') if isinstance(payload, str) else bytes(payload)

    if path.exists() and backup_count > 0:
        for index in range(backup_count, 1, -1):
            older = _rolling_backup_path(path, index - 1)
            newer = _rolling_backup_path(path, index)
            if older.exists():
                os.replace(older, newer)
        backup_tmp = path.with_name(f'.{path.name}.{uuid.uuid4().hex}.backup.tmp')
        try:
            shutil.copy2(path, backup_tmp)
            os.replace(backup_tmp, _rolling_backup_path(path, 1))
        finally:
            if backup_tmp.exists():
                backup_tmp.unlink()

    temp_path = path.with_name(f'.{path.name}.{uuid.uuid4().hex}.write.tmp')
    try:
        with temp_path.open('wb') as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_path, path)
    finally:
        if temp_path.exists():
            temp_path.unlink()


def _validate_project_bytes(payload):
    raw = payload.decode('utf-8') if isinstance(payload, bytes) else str(payload)
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError('Project data must be a JSON object')
    if data.get('schema') == 'com.skript.workspace-recovery':
        if not isinstance(data.get('projects'), list):
            raise ValueError('Recovery workspace does not contain projects')
    elif not isinstance(data.get('lines'), list):
        raise ValueError('Project does not contain a script line list')
    return raw, data


def _read_project_with_backups(path, backup_count=3):
    path = pathlib.Path(path)
    errors = []
    for candidate in [path] + [_rolling_backup_path(path, i) for i in range(1, backup_count + 1)]:
        if not candidate.exists():
            continue
        try:
            raw, data = _validate_project_bytes(candidate.read_bytes())
            return raw, data, (str(candidate) if candidate != path else '')
        except Exception as exc:
            errors.append(f'{candidate.name}: {exc}')
    if not path.exists() and not errors:
        raise FileNotFoundError(f'File not found: {path}')
    raise ValueError('No valid project copy was found. ' + '; '.join(errors))


def _remove_file_family(path, backup_count=3):
    path = pathlib.Path(path)
    for candidate in [path] + [_rolling_backup_path(path, i) for i in range(1, backup_count + 1)]:
        try:
            if candidate.exists():
                candidate.unlink()
        except OSError:
            pass


def _cleanup_obsolete_install_runtime():
    """Best-effort removal of setup leftovers after Windows releases them."""
    if not getattr(sys, 'frozen', False):
        return
    try:
        install_folder = pathlib.Path(sys.executable).resolve().parent
        if install_folder.name.casefold() != 'skript':
            return
        active_runtime = pathlib.Path(getattr(sys, '_MEIPASS', '')).resolve()
        candidates = []
        for child in install_folder.iterdir():
            if not child.is_dir() or child.resolve() == active_runtime:
                continue
            if child.name == '_internal' or child.name.startswith('_runtime_'):
                candidates.append(child)
        for prefix in (install_folder.name + '.previous',):
            candidates.extend(
                child for child in install_folder.parent.glob(prefix + '*')
                if child.is_dir() and child.parent.resolve() == install_folder.parent.resolve()
            )
    except OSError:
        return

    for _attempt in range(3):
        remaining = []
        for candidate in candidates:
            try:
                shutil.rmtree(candidate)
            except FileNotFoundError:
                continue
            except OSError:
                remaining.append(candidate)
        if not remaining:
            return
        candidates = remaining
        time.sleep(1)

# ── Collaboration state (in-memory + persisted to collab/ folder) ─────────
_COLLAB_SESSIONS = {}   # session_id -> { script, pw_hash, notes, title, created }
_COLLAB_SERVER   = None
_COLLAB_PORT_VAL = None
_COLLAB_LOCAL_ONLY = False
_COLLAB_LOCK     = threading.RLock()
_COLLAB_EVENTS   = {}   # session_id -> {seq, events}; never persisted or exposed directly
_COLLAB_EVENT_CONDITION = threading.Condition(_COLLAB_LOCK)
_MAIN_PORT_VAL   = None   # set in launch() so collab routes know it
_EDGE_PROC       = None   # Edge/Chrome subprocess — used for window control
_WINDOW_ICON_HANDLES = []  # Keep Win32 icon handles alive while Edge uses them
_NATIVE_HOST_ROOT = None   # Tk-owned outer window; Edge is clipped inside it
_NATIVE_HOST_HWND = None
_HOSTED_BROWSER_HWND = None
_HOSTED_BROWSER_INSETS = (0, 0, 0, 0)
_HOSTED_BROWSER_SIZE = None
_HOSTED_INSET_CHECK_AT = 0.0
_HOSTED_INSET_CANDIDATE = None
_HOSTED_INSET_CANDIDATE_COUNT = 0
_TITLEBAR_OVERLAY_ROOT = None
_TITLEBAR_OVERLAY_HWND = None
_TITLEBAR_OVERLAY_TARGET = None
_TITLEBAR_OVERLAY_GEOMETRY = None
_WINDOW_EVENT_LOCK = threading.Lock()
_WINDOW_EVENT_SEQ = 0
_WINDOW_EVENT_NAME = ''
_API_TOKEN       = None   # per-launch token for privileged localhost API routes
_SINGLE_INSTANCE_MUTEX = None  # Windows handle kept alive for this process
_SESSION_ACTIVE = False
_SESSION_STATE_LOCK = threading.RLock()
_PROCESS_SESSION_ID = uuid.uuid4().hex
_APP_SHUTDOWN_EVENT = threading.Event()
_PRESERVE_RECOVERY_ON_EXIT = False


def _publish_window_event(name):
    """Publish a small native-titlebar event for the local page to consume."""
    global _WINDOW_EVENT_SEQ, _WINDOW_EVENT_NAME
    with _WINDOW_EVENT_LOCK:
        _WINDOW_EVENT_SEQ += 1
        _WINDOW_EVENT_NAME = str(name or '')
        return _WINDOW_EVENT_SEQ


def _current_window_event():
    with _WINDOW_EVENT_LOCK:
        return _WINDOW_EVENT_SEQ, _WINDOW_EVENT_NAME


def _acquire_single_instance():
    """Allow only one Skript launcher process, preventing duplicate splashes."""
    global _SINGLE_INSTANCE_MUTEX
    if os.environ.get('SKRIPT_DIAGNOSTIC') == '1':
        return True
    if sys.platform != 'win32':
        return True
    try:
        import ctypes
        handle = ctypes.windll.kernel32.CreateMutexW(None, False, 'Local\\SkriptDesktopAppSingleton')
        if not handle:
            return True
        if ctypes.windll.kernel32.GetLastError() == 183:  # ERROR_ALREADY_EXISTS
            ctypes.windll.kernel32.CloseHandle(handle)
            return False
        _SINGLE_INSTANCE_MUTEX = handle
        return True
    except Exception:
        # Startup should remain available if a restricted Windows environment
        # does not permit named mutexes.
        return True

def _get_local_ips():
    """Return list of non-loopback IPv4 addresses for this machine."""
    ips = set()
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = info[4][0]
            if ip and not ip.startswith('127'):
                ips.add(ip)
    except Exception:
        pass
    if not ips:
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(('8.8.8.8', 80))
            ips.add(s.getsockname()[0])
            s.close()
        except Exception:
            pass
    return sorted(ips) or ['127.0.0.1']

def _collab_dir():
    ud, _ = _get_dirs()
    d = ud / 'collab'
    d.mkdir(exist_ok=True)
    return d

def _save_collab_session(session_id):
    sess = _COLLAB_SESSIONS.get(session_id)
    if not sess: return
    try:
        p = _collab_dir() / (session_id + '.json')
        p.write_text(json.dumps(sess, indent=2), encoding='utf-8')
    except Exception:
        pass

def _load_collab_sessions():
    try:
        for f in _collab_dir().glob('*.json'):
            try:
                data = json.loads(f.read_text('utf-8'))
                _COLLAB_SESSIONS[f.stem] = data
            except Exception:
                pass
    except Exception:
        pass


def _password_hash(password, iterations=210000):
    """Return a salted, deliberately slow password hash suitable for storage."""
    salt = secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, iterations)
    return f'pbkdf2_sha256${iterations}${salt.hex()}${digest.hex()}'


def _password_verify(password, encoded):
    """Verify current PBKDF2 hashes and legacy SHA-256 hashes in constant time."""
    try:
        if encoded.startswith('pbkdf2_sha256$'):
            _, rounds, salt_hex, expected = encoded.split('$', 3)
            actual = hashlib.pbkdf2_hmac(
                'sha256', password.encode('utf-8'), bytes.fromhex(salt_hex), int(rounds)
            ).hex()
        else:
            actual = hashlib.sha256(password.encode('utf-8')).hexdigest()
            expected = encoded
        return bool(expected) and secrets.compare_digest(actual, expected)
    except (TypeError, ValueError):
        return False

def _collab_html(session_id, collab_port, main_port):
    """Collaborator viewer page — security-hardened with rate limiting, lockout, expiry."""
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Skript — Collaborator View</title>
<style>
*{{box-sizing:border-box;margin:0;padding:0}}
:root{{
  --bg:#0f0f12;--sf:#1e1e22;--sf2:#26262c;--sf3:#2e2e36;
  --bd:rgba(255,255,255,0.08);--bd2:rgba(255,255,255,0.13);
  --tx:#f0eee8;--tx2:#a8a6a0;--tx3:#5a5856;
  --am:#d4a843;--gr:#4caf7a;--bl:#5b9bd5;--rd:#d95f5f;
}}
body{{background:var(--bg);font-family:system-ui,sans-serif;min-height:100vh;color:var(--tx)}}
#topbar{{
  position:sticky;top:0;z-index:40;
  background:#1a1a1e;border-bottom:1px solid var(--bd);
  padding:10px 20px;display:flex;align-items:center;gap:12px;
}}
#topbar h1{{font-size:13px;font-weight:600;color:var(--tx);flex:1}}
.badge{{font-size:10px;padding:3px 10px;border-radius:20px;font-weight:600;letter-spacing:.3px}}
.bv{{background:rgba(91,155,213,.15);border:1px solid rgba(91,155,213,.3);color:var(--bl)}}
.be{{background:rgba(76,175,122,.15);border:1px solid rgba(76,175,122,.3);color:var(--gr)}}
.bx{{background:rgba(217,95,95,.15);border:1px solid rgba(217,95,95,.3);color:var(--rd)}}

/* ── Auth card ── */
#auth-wrap{{display:flex;align-items:center;justify-content:center;min-height:calc(100vh - 52px);padding:20px}}
.card{{
  background:var(--sf);border:1px solid var(--bd2);border-radius:16px;
  padding:36px;width:100%;max-width:400px;
  box-shadow:0 24px 80px rgba(0,0,0,.8);
}}
.lock-icon{{
  width:54px;height:54px;margin:0 auto 22px;border-radius:50%;
  background:linear-gradient(135deg,rgba(212,168,67,.18),rgba(212,168,67,.04));
  border:1px solid rgba(212,168,67,.3);
  display:flex;align-items:center;justify-content:center;font-size:24px;
}}
.card h2{{font-size:18px;font-weight:700;text-align:center;margin-bottom:6px}}
.card .sub{{font-size:12px;color:var(--tx3);text-align:center;margin-bottom:24px;line-height:1.6}}
.lbl{{font-size:10px;color:var(--tx3);text-transform:uppercase;letter-spacing:.8px;margin-bottom:6px;display:block}}
.pw-row{{display:flex;gap:8px;margin-bottom:5px}}
.pw-inp{{
  flex:1;background:var(--sf2);border:1px solid var(--bd2);border-radius:8px;
  color:var(--tx);padding:11px 14px;font-size:14px;outline:none;
  transition:border-color .15s;letter-spacing:1.5px;font-family:'Courier New',monospace;
}}
.pw-inp:focus{{border-color:var(--am)}}
.pw-inp.err{{border-color:var(--rd);animation:shake .4s}}
@keyframes shake{{0%,100%{{transform:translateX(0)}}25%{{transform:translateX(-6px)}}75%{{transform:translateX(6px))}}}}
.eye-btn{{
  background:var(--sf2);border:1px solid var(--bd2);border-radius:8px;
  color:var(--tx3);padding:0 13px;cursor:pointer;font-size:16px;flex-shrink:0;
  transition:all .12s;
}}
.eye-btn:hover{{color:var(--tx);background:var(--sf3)}}
.hint{{font-size:11px;color:var(--tx3);min-height:17px;margin-bottom:14px}}
.hint.warn{{color:var(--am)}}.hint.bad{{color:var(--rd)}}
.bar-wrap{{height:3px;border-radius:2px;background:var(--sf3);margin-bottom:20px;overflow:hidden}}
.bar-fill{{height:100%;border-radius:2px;background:var(--gr);transition:width .35s,background .35s}}
.lockout-box{{
  background:rgba(217,95,95,.08);border:1px solid rgba(217,95,95,.22);
  border-radius:8px;padding:10px 14px;margin-bottom:16px;
  font-size:12px;color:var(--rd);display:none;align-items:center;gap:8px;
}}
.go-btn{{
  width:100%;background:var(--am);color:#1a1400;border:none;border-radius:8px;
  padding:12px;font-size:13px;font-weight:700;cursor:pointer;
  transition:background .15s;letter-spacing:.3px;
}}
.go-btn:hover{{background:#e0b845}}.go-btn:disabled{{background:var(--sf3);color:var(--tx3);cursor:not-allowed}}

/* ── Status screens ── */
#expired-wrap,#error-wrap{{
  display:none;align-items:center;justify-content:center;
  min-height:calc(100vh - 52px);padding:20px;
}}
.status-card{{
  background:var(--sf);border:1px solid var(--bd2);border-radius:16px;
  padding:36px;max-width:380px;width:100%;text-align:center;
  box-shadow:0 24px 80px rgba(0,0,0,.8);
}}
.status-icon{{font-size:42px;margin-bottom:16px}}
.status-card h2{{font-size:16px;font-weight:700;margin-bottom:8px}}
.status-card p{{font-size:12px;color:var(--tx3);line-height:1.6}}

/* ── Edit upgrade bar ── */
#upg-bar{{
  display:none;background:rgba(212,168,67,.06);
  border-bottom:1px solid rgba(212,168,67,.15);
  padding:7px 20px;font-size:12px;color:var(--tx3);
  align-items:center;gap:8px;flex-wrap:wrap;
}}
#upg-pw{{
  background:var(--sf2);border:1px solid var(--bd2);border-radius:5px;
  color:var(--tx);padding:5px 10px;font-size:12px;outline:none;
  letter-spacing:1px;font-family:'Courier New',monospace;
}}
#upg-pw:focus{{border-color:var(--am)}}
#upg-btn{{
  background:var(--am);color:#1a1400;border:none;border-radius:5px;
  padding:5px 14px;font-size:12px;font-weight:600;cursor:pointer;
}}
#edit-bar{{
  display:none;background:rgba(76,175,122,.08);
  border-bottom:1px solid rgba(76,175,122,.2);
  padding:8px 20px;font-size:12px;color:var(--gr);
  align-items:center;gap:8px;
}}

/* ── Script ── */
#page-wrap{{max-width:800px;margin:40px auto;padding:0 20px 80px;display:none}}
.script-page{{
  background:#f8f6f2;color:#1a1a1a;
  padding:80px 80px 100px 120px;border-radius:2px;
  box-shadow:0 2px 8px rgba(0,0,0,.15),0 20px 60px rgba(0,0,0,.4);
  position:relative;
}}
.sl{{
  font-family:'Courier New',monospace;font-size:12.5px;line-height:1.75;
  padding:2px 6px;border-radius:3px;cursor:pointer;position:relative;
  white-space:pre-wrap;word-break:break-word;
  border-left:2px solid transparent;transition:background .12s,border-color .12s;
}}
.sl:hover{{background:rgba(91,155,213,.09);border-left-color:#5b9bd5}}
.sl.hn{{border-left-color:#d4a843!important}}
.sl[data-type=scene]{{font-weight:700;text-transform:uppercase;margin-top:16px}}
.sl[data-type=character]{{margin-left:35%}}
.sl[data-type=dialogue]{{margin-left:25%;max-width:60%}}
.sl[data-type=transition]{{text-align:right;text-transform:uppercase}}
.npin{{
  position:absolute;right:-26px;top:50%;transform:translateY(-50%);
  width:18px;height:18px;border-radius:50%;background:#d4a843;
  color:#1a1400;font-size:9px;font-weight:700;
  display:flex;align-items:center;justify-content:center;
  cursor:pointer;box-shadow:0 1px 4px rgba(0,0,0,.3);transition:transform .1s;
}}
.npin:hover{{transform:translateY(-50%) scale(1.15)}}

/* ── Note popup ── */
#npop{{
  display:none;position:fixed;z-index:200;width:340px;
  background:var(--sf);border:1px solid var(--bd2);border-radius:12px;
  box-shadow:0 16px 60px rgba(0,0,0,.8);padding:18px;
}}
#npop h3{{font-size:13px;font-weight:700;color:var(--tx);margin-bottom:10px}}
.nctx{{
  font-size:10.5px;color:var(--tx3);margin-bottom:12px;font-style:italic;
  border-left:2px solid var(--bd2);padding-left:8px;
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap;
}}
.nf{{
  width:100%;background:var(--sf2);border:1px solid var(--bd2);border-radius:7px;
  color:var(--tx);padding:9px 11px;font-size:12px;outline:none;margin-bottom:8px;
  transition:border-color .15s;font-family:system-ui,sans-serif;
}}
.nf:focus{{border-color:var(--am)}}
textarea.nf{{resize:vertical;min-height:80px}}
.nbrow{{display:flex;gap:8px}}
.nb{{
  flex:1;padding:8px;border-radius:7px;border:1px solid var(--bd2);
  background:var(--sf2);color:var(--tx2);font-size:12px;cursor:pointer;
  font-family:system-ui,sans-serif;transition:all .12s;
}}
.nb:hover{{background:var(--sf3);color:var(--tx)}}
.nb.p{{background:var(--am);color:#1a1400;border-color:var(--am);font-weight:700}}
.nb.p:hover{{background:#e0b845}}

#toast{{
  display:none;position:fixed;bottom:28px;left:50%;transform:translateX(-50%);
  background:var(--sf);border:1px solid var(--bd2);color:var(--tx);
  padding:11px 22px;border-radius:10px;box-shadow:0 8px 30px rgba(0,0,0,.7);
  z-index:9999;white-space:nowrap;font-size:13px;
}}
</style>
</head>
<body>

<div id="topbar">
  <h1 id="stitle">Skript — Loading…</h1>
  <span id="rbadge" class="badge bv">👁 Viewer</span>
</div>
<div id="edit-bar">✓ Edit access granted</div>
<div id="upg-bar">
  <span style="color:var(--am)">🔒 Have an edit password?</span>
  <input type="password" id="upg-pw" placeholder="Edit password…">
  <button id="upg-btn" onclick="tryUpgrade()">Unlock</button>
  <span id="upg-err" style="color:var(--rd);font-size:11px;display:none">Incorrect</span>
</div>

<div id="auth-wrap">
  <div class="card">
    <div class="lock-icon">🔐</div>
    <h2>Protected Script</h2>
    <p class="sub">Enter the password provided by the script author to access this document.</p>
    <div class="lockout-box" id="lockout-box">
      🔒 <span id="lockout-msg">Too many attempts.</span>
    </div>
    <label class="lbl">Viewer Password</label>
    <div class="pw-row">
      <input type="password" id="vpw" class="pw-inp" placeholder="Word-Word-0000"
        onkeydown="if(event.key==='Enter')tryAuth()">
      <button class="eye-btn" onclick="document.getElementById('vpw').type=document.getElementById('vpw').type==='password'?'text':'password'">👁</button>
    </div>
    <div class="hint" id="hint">Ask the script author for the password.</div>
    <div class="bar-wrap"><div class="bar-fill" id="bfill" style="width:100%"></div></div>
    <button class="go-btn" id="go-btn" onclick="tryAuth()">View Script →</button>
  </div>
</div>

<div id="expired-wrap">
  <div class="status-card">
    <div class="status-icon">⏰</div>
    <h2>Link Expired</h2>
    <p>This collaboration link has expired. Contact the script author for a new link.</p>
  </div>
</div>

<div id="error-wrap">
  <div class="status-card">
    <div class="status-icon">🚫</div>
    <h2 id="err-title">Access Denied</h2>
    <p id="err-msg">This collaboration session is no longer available.</p>
  </div>
</div>

<div id="page-wrap">
  <div class="script-page" id="spage"></div>
</div>

<div id="npop">
  <h3 style="margin-bottom:12px;">💬 Leave a Note</h3>
  <div class="nctx" id="nctx"></div>
  <input id="nname" type="text" class="nf" placeholder="Your name…" autocomplete="name"
    oninput="if(this.value)localStorage.setItem('sf-collab-name',this.value)">
  <select id="ncat" class="nf" style="cursor:pointer;">
    <option value="">— Category (optional) —</option>
    <option value="plot">🔵 Plot</option>
    <option value="dialogue">🟢 Dialogue</option>
    <option value="character">🟣 Character</option>
    <option value="scene">🟡 Scene / Action</option>
    <option value="tone">🟠 Tone / Style</option>
    <option value="other">⚪ Other</option>
  </select>
  <textarea id="ntext" class="nf" placeholder="Your feedback or comment…"></textarea>
  <div class="nbrow">
    <button class="nb" onclick="closeNP()">Cancel</button>
    <button class="nb p" onclick="submitNote()">Send Note</button>
  </div>
</div>

<div id="toast"></div>

<script>
const SID  = '{session_id}';
const API  = 'http://' + location.hostname + ':{collab_port}';
let lines  = [], curIdx = -1, hasEdit = false, attempts = 5, ACCESS_TOKEN = '';
    let revision = 0, editTimer = null, liveTimer = null, streamAbort = null, lastEventId = 0;
const CLIENT_ID = 'guest-' + Math.random().toString(36).slice(2);

function collabHeaders(extra={{}}) {{
  const h = Object.assign({{'Content-Type':'application/json'}}, extra || {{}});
  if (ACCESS_TOKEN) h['X-Collab-Token'] = ACCESS_TOKEN;
  return h;
}}

function toast(m, d=3000) {{
  const t=document.getElementById('toast');
  t.textContent=m; t.style.display='block';
  clearTimeout(t._t); t._t=setTimeout(()=>{{t.style.display='none';}},d);
}}

function showExpired() {{
  document.getElementById('auth-wrap').style.display='none';
  document.getElementById('expired-wrap').style.display='flex';
  document.getElementById('rbadge').className='badge bx';
  document.getElementById('rbadge').textContent='⏰ Expired';
  document.getElementById('stitle').textContent='Link Expired';
}}

function showError(title, msg) {{
  document.getElementById('auth-wrap').style.display='none';
  document.getElementById('error-wrap').style.display='flex';
  document.getElementById('err-title').textContent=title;
  document.getElementById('err-msg').textContent=msg;
}}

function updateBar() {{
  const f=document.getElementById('bfill');
  const p=Math.max(0,(attempts/5)*100);
  f.style.width=p+'%';
  f.style.background=p>60?'var(--gr)':p>20?'var(--am)':'var(--rd)';
}}

async function tryAuth() {{
  const pw=document.getElementById('vpw').value.trim();
  const btn=document.getElementById('go-btn');
  const inp=document.getElementById('vpw');
  if (!pw) {{ inp.classList.add('err'); setTimeout(()=>inp.classList.remove('err'),500); return; }}
  btn.disabled=true; btn.textContent='Checking…';
  try {{
    const r=await fetch(API+'/api/collab/auth',{{
      method:'POST', headers:{{'Content-Type':'application/json'}},
      body:JSON.stringify({{session:SID,password:pw,role:'view'}})
    }});
    const d=await r.json();
    if (d.ok) {{
      ACCESS_TOKEN=d.access_token||'';
      document.getElementById('auth-wrap').style.display='none';
      await loadScript();
      pingPresence();
    }} else if (d.expired) {{
      showExpired();
    }} else if (d.rate_limited) {{
      const lb=document.getElementById('lockout-box');
      document.getElementById('lockout-msg').textContent=d.error||'Too many attempts. Try again later.';
      lb.style.display='flex'; btn.disabled=true; btn.textContent='Locked';
    }} else {{
      attempts=d.attempts_left??Math.max(0,attempts-1);
      updateBar();
      inp.classList.add('err'); setTimeout(()=>inp.classList.remove('err'),500);
      const h=document.getElementById('hint');
      h.textContent=attempts>0
        ? `Incorrect. ${{attempts}} attempt${{attempts!==1?'s':''}} remaining.`
        : 'Account temporarily locked. Try again later.';
      h.className='hint '+(attempts<=1?'bad':'warn');
      btn.disabled=attempts<=0; btn.textContent='View Script →';
    }}
  }} catch(e) {{
    document.getElementById('hint').textContent='Connection error. Is the host still running?';
    document.getElementById('hint').className='hint bad';
    btn.disabled=false; btn.textContent='View Script →';
  }}
}}

async function loadScript() {{
  try {{
    const r=await fetch(API+'/api/collab/script?session='+SID,{{
      headers: collabHeaders()
    }});
    const d=await r.json();
    if (d.expired) {{ showExpired(); return; }}
    if (!d.ok) {{ showError('Access Denied', d.error||'Session unavailable.'); return; }}
    lines=d.script.lines||[]; revision=d.revision||1;
    const t=d.script.title||'Untitled';
    document.getElementById('stitle').textContent=t;
    document.title='Skript — '+t;
    document.getElementById('page-wrap').style.display='block';
    if (d.has_password) document.getElementById('upg-bar').style.display='flex';
    renderScript(); loadNotes(); startLiveStream();
  }} catch(e) {{
    showError('Connection Error','Could not reach the script host.');
  }}
}}

async function tryUpgrade() {{
  const pw=document.getElementById('upg-pw').value;
  if (!pw) return;
  const r=await fetch(API+'/api/collab/auth',{{
    method:'POST', headers:{{'Content-Type':'application/json'}},
    body:JSON.stringify({{session:SID,password:pw,role:'edit'}})
  }});
  const d=await r.json();
  if (d.ok) {{
    ACCESS_TOKEN=d.access_token||ACCESS_TOKEN;
    hasEdit=true;
    document.getElementById('upg-bar').style.display='none';
    document.getElementById('edit-bar').style.display='flex';
    document.getElementById('rbadge').className='badge be';
    document.getElementById('rbadge').textContent='✏ Editor';
    renderScript(); startLiveStream();
    toast('✓ Edit access unlocked'+(d.recovery?' (via recovery key)':''));
  }} else if (d.rate_limited) {{
    document.getElementById('upg-err').textContent=d.error;
    document.getElementById('upg-err').style.display='inline';
  }} else {{
    document.getElementById('upg-err').style.display='inline';
    setTimeout(()=>{{document.getElementById('upg-err').style.display='none';}},2500);
  }}
}}

function renderScript() {{
  const pg=document.getElementById('spage');
  pg.innerHTML='';
  lines.forEach((line,i)=>{{
    const d=document.createElement('div');
    d.className='sl'; d.dataset.type=line.type||'action'; d.dataset.idx=i;
    d.dataset.lineId=line.lineId||('index-'+i); d.contentEditable=hasEdit?'true':'false';
    d.textContent=line.text||'';
    d.addEventListener('click',e=>{{if(!hasEdit||e.altKey)openNP(i,line.text);}});
    d.addEventListener('input',()=>{{line.text=d.innerText;queueLiveEdit();}});
    pg.appendChild(d);
  }});
}}

function queueLiveEdit() {{
  if (!hasEdit) return;
  clearTimeout(editTimer); editTimer=setTimeout(pushLiveEdit,450);
}}

async function pushLiveEdit() {{
  if (!hasEdit) return;
  editTimer=null;
  const author=localStorage.getItem('sf-collab-name')||'Editor';
  try {{
    const r=await fetch(API+'/api/collab/edit',{{method:'POST',headers:collabHeaders(),body:JSON.stringify({{
      session:SID,base_revision:revision,author,client_id:CLIENT_ID,
      script:{{title:document.getElementById('stitle').textContent||'Untitled',lines}}
    }})}});
    const d=await r.json();
    if(!d.ok){{toast(d.error||'Could not sync edits.');return;}}
    revision=d.revision||revision;
    if(d.conflicts?.length)toast('Your offline changes were merged; '+d.conflicts.length+' conflict(s) recorded.',6000);
  }} catch(e) {{ toast('Offline: edits will retry when the host reconnects.',5000); editTimer=setTimeout(pushLiveEdit,2500); }}
}}

async function startLiveStream() {{
  streamAbort?.abort();
  const controller=new AbortController(); streamAbort=controller;
  try {{
    const r=await fetch(API+'/api/collab/events?session='+encodeURIComponent(SID)+'&since='+lastEventId,{{
      headers:collabHeaders({{'Accept':'text/event-stream'}}),signal:controller.signal,cache:'no-store'
    }});
    if(!r.ok||!r.body)throw new Error('Live stream unavailable');
    const reader=r.body.getReader(),decoder=new TextDecoder(); let buffer='';
    while(!controller.signal.aborted){{
      const part=await reader.read(); if(part.done)break;
      buffer+=decoder.decode(part.value,{{stream:true}}).replace(/\\r\\n/g,'\\n');
      let boundary;
      while((boundary=buffer.indexOf('\\n\\n'))>=0){{
        const frame=buffer.slice(0,boundary);buffer=buffer.slice(boundary+2);
        let type='message',data='',id=0;
        frame.split('\\n').forEach(line=>{{
          if(line.startsWith('event:'))type=line.slice(6).trim();
          else if(line.startsWith('data:'))data+=line.slice(5).trim();
          else if(line.startsWith('id:'))id=Number(line.slice(3).trim())||0;
        }});
        if(id)lastEventId=Math.max(lastEventId,id);
        if(type==='closed'){{showError('Session Ended','This collaboration session has been closed.');return;}}
        if(!data)continue;
        const d=JSON.parse(data);
        if(d.ok&&(d.revision||0)>revision&&!editTimer){{
          revision=d.revision;lines=d.script.lines||[];renderScript();toast('Live changes received.');
        }}
        if(type==='notes')loadNotes(false);
      }}
    }}
  }} catch(e) {{ if(e.name==='AbortError')return; }}
  if(!controller.signal.aborted)liveTimer=setTimeout(startLiveStream,700);
}}

async function loadNotes(schedule=true) {{
  try {{
    const r=await fetch(API+'/api/collab/notes?session='+SID,{{
      headers: collabHeaders()
    }});
    const d=await r.json();
    if (!d.ok) return;
    document.querySelectorAll('.sl').forEach(el=>{{
      el.classList.remove('hn');
      el.querySelector('.npin')?.remove();
    }});
    const byLine={{}};
    (d.notes||[]).forEach(n=>{{ byLine[n.line_idx]=(byLine[n.line_idx]||0)+1; }});
    Object.entries(byLine).forEach(([i,c])=>{{
      const el=document.querySelector('.sl[data-idx="'+i+'"]');
      if (!el) return;
      el.classList.add('hn');
      const p=document.createElement('div'); p.className='npin';
      p.textContent=c; p.title=c+' note'+(c>1?'s':'');
      el.appendChild(p);
    }});
  }} catch(e) {{}}
  if(schedule) setTimeout(loadNotes,8000);
}}
async function pingPresence() {{
  try {{ await fetch(API+'/api/collab/ping',{{
    method:'POST',headers:collabHeaders(),
    body:JSON.stringify({{session:SID,client_id:CLIENT_ID,name:localStorage.getItem('sf-collab-name')||'Viewer',color:'#5b9bd5'}})
  }}); }} catch(e) {{}}
  setTimeout(pingPresence,30000);
}}

function openNP(i,txt) {{
  curIdx=i;
  const pop=document.getElementById('npop');
  document.getElementById('nctx').textContent=
    txt ? '"'+txt.slice(0,60)+(txt.length>60?'…':'')+'"' : '(blank line)';
  document.getElementById('ntext').value='';
  // Restore saved name from localStorage
  const saved=localStorage.getItem('sf-collab-name')||'';
  document.getElementById('nname').value=saved;
  const el=document.querySelector('.sl[data-idx="'+i+'"]');
  const r=el?el.getBoundingClientRect():{{bottom:200,left:200}};
  pop.style.display='block';
  pop.style.top =Math.max(8,Math.min(r.bottom+8,window.innerHeight-300))+'px';
  pop.style.left=Math.max(8,Math.min(r.left,window.innerWidth-360))+'px';
  // Focus name if empty, otherwise text
  (saved?document.getElementById('ntext'):document.getElementById('nname')).focus();
}}
function closeNP() {{ document.getElementById('npop').style.display='none'; curIdx=-1; }}

async function submitNote() {{
  const name=document.getElementById('nname').value.trim()||'Anonymous';
  const text=document.getElementById('ntext').value.trim();
  const cat =document.getElementById('ncat')?.value||'';
  if (!text) {{ toast('Write a note first.'); return; }}
  if (name) localStorage.setItem('sf-collab-name', name);
  try {{
    const r=await fetch(API+'/api/collab/note',{{
      method:'POST', headers:collabHeaders(),
      body:JSON.stringify({{
        session:SID,line_idx:curIdx,
        line_text:(lines[curIdx]||{{}}).text||'',
        author:name,text,category:cat
      }})
    }});
    const d=await r.json();
    if (d.ok) {{ toast('✓ Note sent!'); closeNP(); loadNotes(); }}
    else       {{ toast('Error: '+(d.error||'Try again.')); }}
  }} catch(e) {{ toast('Connection error.'); }}
}}

document.addEventListener('click',e=>{{
  const p=document.getElementById('npop');
  if (p.style.display!=='none'&&!p.contains(e.target)&&!e.target.closest('.sl'))
    closeNP();
}});

// On load — probe session before showing auth
(async()=>{{
  try {{
    const r=await fetch(API+'/api/collab/status?session='+SID);
    const d=await r.json();
    if (d.expired) {{ showExpired(); return; }}
    if (!d.ok&&d.error==='Access denied')     {{ showError('Access Denied','Your access has been revoked by the author.'); return; }}
    if (!d.ok&&d.error==='Session not found or ended') {{ showError('Session Ended','This collaboration session has been closed.'); return; }}
  }} catch(e) {{}}
  document.getElementById('auth-wrap').style.display='flex';
}})();
</script>
</body>
</html>"""


# ── Hide console window on Windows (runs immediately at import) ──
# IMPORTANT: Do NOT hide the console when running in --build mode —
# the user needs to see PyInstaller output and any error messages.
# FreeConsole() is called later inside launch() for normal app mode.
if sys.platform == 'win32' and '--build' not in sys.argv:
    try:
        import ctypes as _ct
        _hwnd = _ct.windll.kernel32.GetConsoleWindow()
        if _hwnd: _ct.windll.user32.ShowWindow(_hwnd, 0)  # SW_HIDE instantly
    except Exception:
        pass

# ═══════════════════════════════════════════════════════════════════
#  EMBEDDED HTML  (gzip-compressed + base64, ~96 KB as text)
#  Decompresses to the full Skript application at runtime.
# ═══════════════════════════════════════════════════════════════════
_HTML_B64 = (
    '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'
    'HjiTXlZTKf9hVZVRVpcfM5sRrQv2sPdgaZE14BPLQpJfTm5r86NLt2yhk2l5sQnwkBEpUSyk2cmrIBOjdaSG7NWRiWV1pBDUV7Lj'
    'tcSHLsRCQCEp1dcoAFWG1leWKA9tlRrFm9Y6mJxkw5JqgLgowVQ/UFscp6JI44qOM234c0rLZL5CMRp8zZgamE6rWEOZRwabEaWE'
    'az3z6zuZJTDAKBbUhcRonZ3MZzWREi/tW438un5+HBJyoF9dsmW0Dhp+/DoyAEq8jjH/BBVNTrS2tfd4lW1GaV2uXZMerWkNPl5V'
    'm1Fel5pyOBA0vxQSL7pJTmltXniTnHhtZbrxq6rkaD1lpvGqqdTSWuE8UKleLV+/r3fRyLjGRhy2tO8u9ZnBy9+O56u6VhO+8wwl'
    'aV14MLGX6btHBIA07AQQZHn3jho+pcg1r8L229qqrIPAZIzPg9SqX/iNZxdZj6spRRmpCQWpUyJaot7hRhNen/yhs/dpf3/m26e9'
    '5svl5uzLT/0Z8eNTR/xtvWx9a+41Hu63mpD38v6nbmvvH58+7X/79KnTevSyJb7FR/PlKtYQID6Joubntx8etFpzx7TpzaKXnmUb'
    'QgBC458+NT99ar2kRaQ6sTt6n+K1fBvhg6R31cuPrgHlKB8XwAmGrOZ9yHk/JMMgjZScXXDuuyuQuB1HX3useF9+R66IEYHZbOhn'
    'S3PjyCxjB7fBT1IspVk/6Q1GBTws/NsPv7E2C4mrRUHidLc4jM6yYYjDPSbShA11oJnf0M7yVdt6S56CLa6twjy2k39ORxORXUwP'
    'd7wRTFQbe/IPiQ2DdZKXpEFdu+0wlJBAD+BN5mUdVPLbtwSbt4/IrNyLRqm4cpwI11M8fDTO5/Q2g5MnLXntRMy80fnbvCgCtjRk'
    'VzOOvjgk3/zJUyfAiZSCTdck0nbhOI80IAQB2a2x51SgwV48hICvZiQQuAc5AwlctDWFl7XzlOFkLJqiAWIZiuIkX/WeStuX8b7g'
    'bVPS1NV0G4+9HW3fX56GB8XwxgA/cvF7n3YaAdnQXidIJuZSXoDL7OF0AvdB8UrN1zQf4AMbyftBJrhGzN1BBjdtRGvT7H6j7L0y'
    'igiODQ15Aq0uu9Rv+4QKA25c3asSFGzP+qNM9ge7aLC+Mvel2Ini3AkpmyNkkNTbXeSleYhHJhLpa+/z1VdzbUcQon35fjgazmYY'
    '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'
    'OYZAnDFgZ66+vJRVs5+sY1c/mDQj7mVAMqPVOpf+wRaHJrX+3gLRyn9H3TDerF/QQyf1JlL5PTYAHY24+SybWoTGIyFTpISXoTmT'
    'mn8vl3ArsIQVW0NXxApcnHIeu+nqQVK24jxF9rYdrZfp39fJ4azZ8hbxzbhTBYeqxaUkp/IG2a3iXZp/uUOG1ECRKzL9KoAQeWHv'
    '9ouCDlj2UWYc+zVZrZdU5Wnvd6CwLKZ5uio7HOjuMuskn0BTlZadeHmx0VtvQCnuXJ2Zc+6e/ipVgMjB9ekMuK+30v1V4FnIOptM'
    'kDdaUc8qAp45Ty6Am7TUBtQlI6DBSIyYqNTlMhK+PhrJ87mqIXgao5aZt7h044FbCVfCWpgS+4/62si7NrzExkzkodV9uL8tz15P'
    'A/0RRHYrKueXlyjn4XOqBhPvuquMnf2ueFjO/WBFhXQ/glYVMBg2hU2nKd/OgRuamt2GOPdaEpVYcSpq+207B8RUXwCSr9ubmypg'
    'vFsMiXaK7xClHPF7GKUdR49HVNyn5tl4VyTa05yf0k95JO0oqvQOLZ2o48asixla3oh4Ut60Lv4cBHm2Yq67+J/JUbxyEU84hm9R'
    'Gjd/sagNjq+V6m30n7xepnXXy/TnWS9VVFBBAwqH3dTY/j8LCaiqG1Rz8D/q0T9emx/85fjg9YuHz25Z5KGtvyXDd+fY8A0iZ0bO'
    'CRmi0NJ7fOGWNhekd8p4nK3nM/6Yn60ipchH4QCXbaPlqmQ8XzhNt8V21MCFc3eFzkgb8Jczw7WK/7hKsDz+fbMKrld+skA1C/x1'
    'neKMF0Nx+Os6xYsPZ3dgesGx6wc1gKtbroM1mE7ULtfQijI6cqlNuXYps78s5s0PlmYO/K0BGfAdgvsYfVOe7klfLiG5wG3X1Qfq'
    'TtgtmK0T/JO71+fuztrmtiIc6HHRq4u6UqIJzip9Dt4WVVIWcGGPc/yhh3v18bP6mqvwNCec/Vhe2Nh8yitLdkoPO/UxnLD9WAzA'
    'TksU0YdcpbrDQ+1T1nyT4QyrFNbN8KkEkru/bX73RbxY7f9jXu7/44z9+fs6Y/+PV1mx37p7xmj6t5DdMIp8w5NZATP1W556Zqc2'
    'eCpWaqZ/JaqGZqTTdTgHTYtVMp+PAcNFBLnUM2fSIxG9yQFaTXNbMgIC7V4GLCH5/PW7vYb57MCJkmC9W7AjYthyRvuWY+Nwyw3j'
    '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'
    '6nBycnVdPeTUcJR2j2GpbL9qqs0CsWN712BN+d/iTNPjjnhfjoOzVeSrr3TI8g0XeZY8WZZo9yhhohw3ZlmSMHmqk64q7woOXG3O'
    'Wm546F5sbXJyy++e5ey4w828okrYjYEQyStb/7dNcd1TrSExdvd0Hz3x96rcf8xMSe9vv/tcm9xTAkkL8yXT3I46/pmsroWoJ0cp'
    'orBolMVQVlg5FUrn3c54wcwCYyG3mobmx3R7Bd1u61ec57bPdQhV+15lvp13h2eclG+l11TWZJqt2o46zkr0Xbir7cJdYchkvIhA'
    'g8RAQAy0I5vkYhRn5FmU4u85pwi2pYDhD7TSXnOYUIEVoBFec1CKW0ux0N238o/u1csHXyQrlnvwtB0ePFs7Tj6xXlpvdP9yTkGa'
    'JTHiapdDbu3ucH8orSKuI0sdd1LFG0n/U7ubdMVQIVPn7xi7vWw+pNJV1VWi30vxgxZXIhYmk3dtE228c7itWPSwnpeAHogm10u7'
    'nLDqmATcg/EaCbxYSnb+FAehMUZWCHDEbH3mxMmnrDZEqG3Oov5rujnSDMFW3ygCHPYkP03MF7Vskqy6a5yBLmysPeBIjdMgBEw/'
    'IdVzD+2b+FMVqFQ1X8I75vAejINcC2Q213ZMRzFxsYtPIDrf58brwLKl98BdykyPqdAYhgqqtQvZP5qi7bytxOjtHph+LcYO0Bj5'
    'rgjgLYTJf2v1yAF+mAuRs1HtXu8V9DpXInhUkG69teiGo6uFm7izt6tuYCTffFSAGPZtIyuchnBYHLhSeJHaXuN5m8IdxBLEdWpv'
    'qW9KkgwU2BpwdVyw7jVIY9fY32i0dFJGbZgiW4b+tBQE2BngIcNXoDIu0ACyj0ET8xXd59n9kIqJD62IylK2sNN2IShuW1WOuiri'
    'tk6t9qzSM6UwA69vH1QND+DnQfpJ24y8ObqcLKMKC1iuB0QkaoDKWHrkiqeKp0WGlprDKNvg56u7A14HcMbWtaljLQifwNI7q+hg'
    'acf1oIqdT2t9tKWBorftgMau09Itq2HOJN+umifR0gCo7gFVky+pLTOHHpI/4IoP5YlUieEzoXyWn7EHXo5TY8TuFwkbNdjMCnKr'
    'c86ZViyajsIkygRxYQMw1Dg52zUOZmmIK4C/GfPZ2slnlFWUjSrd54zemf7GxVESShvq3GcD9d7ZrcEYSeWc6FUWywMsIoxyuWDb'
    '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'
    'p/KLOmcUFoAWKX0LOIMcbMLsIvJGefCAtKddITCtb3Vpbgb34/m55aA/5Jomovr4/9SCBVNzec7U3HOCzI6p+UzXXFhaMDWNeUOw'
    'Ma7hWrBYnVM1l21vD2yOv/G9fY41n0LNxWfYZhAUnYiwJQa1j+90pFNUpuaBeqG7v7SoBs7zpy60iC6GYa8TDsytyVMMwYUhxtpo'
    'Q02SWVH9RQMHoAjuwV/KkpPyTDRsDjtvWXVdzB6SaFnQVRQi1qLRWWlDjhkB9DPCpJpmpQi1Ykj6HCmbPufN0gm3mg4p7bWeahFA'
    'FtfHVwynVKaewdKZCb7/3d/5C00sMA3TLigXJqwcF+aChqlraAi0sLK9whXkQnimIThLUYPBVZYzOFxOLhhYaQzGWZcajF1yDhhc'
    'Wy6Y5xqMWKTkJqMh0YprIPNyIOHSciG90OPKrFEOJeWcweMUJOSdpGc6D31XSaaFrPxglnI3oCt12eqwDlVM+1k4KxUqBf8zJljG'
    'L4GNUfWYY347BoRM5Hgt1E46eInTxhAJiKOLPjyRe2lycYG3tGhfwe/JdTnqxMNkEGMExGgYosWjvniFk+7RYfF4XcWHLq7XVHBo'
    'eHyGj4fV2jF9fHZfWj88Oi4dr1PcaQzOX397t/e2VFo3KZfdLMT65jCnncOj2SqcqDNPC+XFex3WWgSszrSouzJVyxiZduttY2N3'
    's9Fcp5jYAEw8UYRs+0U/btYPxGPpqFX9amJzKtUW5UUNgEGR2wtn3sSoM2YK0vNEWdCk5B6ctNuj/o1NfgXkqO7pWdinqJeOp7HJ'
    '3YJhKVEhb6LrhCYWvRz9Rv1tY79+t1ffgYedrZ1vSut3H95s7QXw5m7vXfMNhmxtltYxsvjeu+1teMQn+POqvvHt3e67g9LdX+/u'
    'vuX3gKftA/1zHwrg7zuGurm7vf3d3cZ+fadx9wakozeN7c275kGjvrkFnbjD0sHr3Y13zbuN7d0mRjCvrL/bKyFJBbs72K2tTXwb'
    'NN/sHtzxq/rON9sN+Hm3t/semmk29g/uNt4d1D/Uv7vDuXu1vdV8A81znXpjf6u+zb933zf230Db/PQahLS/bgSv9wEbd83t3Q/B'
    '213MI0zzfhhUjte363vNRgmJrXUHM39Yq1aOSw9POe/mFUoRpCd2pILk6+v7cHCD6SWv1DoFGkiGlEWNDHpSZ7qQzlU4d/5b3+a4'
    '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'
    '9+f9RcX6j7tPuosK7R4dPjzY34XGOseLyn71uNNv7j9c3OSTY46e6y0qerzf330s9rq7P1vYKMCms9sHKD7YxxywC4p/ebS/24VK'
    'FVp+8HTvUbcvur3+/pMqqH1wtMt3Xnf2vtzvHS1eVhg22MsnT3f7T0+6COfj7kkJSDq7+4ePxONup49LUlgOk+B2ZEqy3u4RtFyM'
    'L7tAtuL46cnxUa8rOk/39vuLCgNa9PcPn/JEi6m8+yVSunlmJnVra/cQhvbo6f5eyQD3D/eeAoS+RrfC4V7nZK9XNu8e6C2ANYUl'
    'DjtP5NKXwZnuaEUnxkn3+OikBCB/8hQPBR10+/10cwUs72T/0eN+cxeoCnCve/i0jOKPDvY4nXFh90fH3UNEiLV2cZnu4R4W6Rx2'
    'Dr7u7ZcA78n+3vHR/iHhY7fXA/O1VzLz45Ojvae7MGu63b2EL5zsA2x64uTo6ElJ391DpK5V0TvaxVvjd8vWpsltFhfBnHwwj92j'
    'ThkqKE550l3U3pOjwyNevuIu907Ew4POoxJI9B4fAWyfPnpUCtfe0dPDPSCe3v6jEuLa7QBHglUtLPAQWdaXwHpgMTv97qMSKuz1'
    'vwae+RCa654cnyACFC9mt/OzQ8SNvW6/u5sKwM9jFX2SbcU84qTzsE8yoVPGo2J5+fjpA/nuh/C/PEovK54n9qt2UrGL472HYv8J'
    '8azdxyTmqnWgm0HhqYrcoJO/o1/YvG3EXnJUoUG9nRT45RbGbLx2nFlHttmVjveevAA155iFGkxOMAfeg3gbbyJtDG1vWFtrt9+c'
    'iyYlH63X885hxG0p8071m0SQhgVhPtow9IMMmYMaRRdisB5/K3uZ4IZufPRpm5P2ukMRnfvJzbDyDuz8FeE4CXUdg7wCW5tTS9AN'
    'ypjeLm7xfqztl5/diCdeHuWUwAd9qeYmRIwREwcQIb32NUqNBR/4wplZgUu3pD+h/2jGZlTBIBbhH4FKQWmJW0bJWhidNt0JXWs5'
    'HGM6e0VI+aFSeQT0y6Y7HYFlvg7ovFXt5C8Z03Ge/zvGMeCcg0R3zHNEd2R+/1//r2Kfhi6DZXBIHDuWPSistUadV7KTH/vnMigG'
    'w2NUYMws8PHkNu/wQ3f3Fx/6jXNnpw4j39FCu1JWHKyLXJBQHppN+0GMNI82/NfJSee5bsN/ndTlLIZ1ztej0n0t5oUq2dN/RZfb'
    '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'
    'wMF7q+oI+r1VDEPHv3R+8pP/Dx8RWuDvXiQA'
)

def _get_html(port: int, low_perf: bool = False, api_token: str = '') -> bytes:
    """Decompress the embedded HTML and inject runtime config variables."""
    html = gzip.decompress(base64.b64decode(_HTML_B64)).decode('utf-8')
    lp   = 'true' if low_perf else 'false'
    injection = (
        f'<script>'
        f'window._SF_PORT={port};'
        f'window._SF_TOKEN={json.dumps(api_token)};'
        f'window._SF_LOW_PERF={lp};'
        f'if(window._SF_LOW_PERF)'
        f'  document.documentElement.classList.add("sf-low-perf");'
        f'(function(){{'
        f'const nativeFetch=window.fetch.bind(window);'
        f'window.fetch=function(input,init){{'
        f'const raw=(input&&input.url)?input.url:String(input);'
        f'let u;try{{u=new URL(raw,location.href);}}catch(e){{return nativeFetch(input,init);}}'
        f'const local=(u.hostname==="127.0.0.1"||u.hostname==="localhost"||u.origin===location.origin);'
        f'if(window._SF_TOKEN&&local&&u.pathname.startsWith("/api/")){{'
        f'const next=Object.assign({{}},init||{{}});'
        f'const h=new Headers((init&&init.headers)||((input&&input.headers)||{{}}));'
        f'h.set("X-Skript-Token",window._SF_TOKEN);'
        f'next.headers=h;return nativeFetch(input,next);'
        f'}}'
        f'return nativeFetch(input,init);'
        f'}};'
        f'}})();'
        f'</script>'
    )
    if low_perf:
        injection += """
<style>
/* ── Low-performance device overrides (Surface Go, Atom, Celeron) ──
   Removes GPU-intensive CSS effects that cause compositing stalls on
   integrated graphics (Intel UHD 615, HD 400/500 series, GMA).
   All layout and functionality is preserved; only visual effects change. */
html.sf-low-perf *,
html.sf-low-perf *::before,
html.sf-low-perf *::after {
  backdrop-filter: none !important;
  -webkit-backdrop-filter: none !important;
}
html.sf-low-perf .modal-overlay,
html.sf-low-perf .sf-modal {
  background: rgba(0,0,0,0.80) !important;
}
html.sf-low-perf .modal,
html.sf-low-perf .sf-modal-box {
  background: #1a1a26 !important;
}
html.sf-low-perf * {
  box-shadow: none !important;
  text-shadow: none !important;
  filter: none !important;
}
html.sf-low-perf .modal,
html.sf-low-perf .sf-modal-box {
  outline: 1px solid #2a2a3a !important;
}
html.sf-low-perf * {
  animation-duration: 0.001ms !important;
  animation-iteration-count: 1 !important;
  transition-duration: 0.001ms !important;
}
html.sf-low-perf button,
html.sf-low-perf .btn,
html.sf-low-perf .ribbon-btn {
  transition: background 60ms linear !important;
}

/* ── In-browser boot loading screen ─────────────────────────────────
   Shown from first pixel-paint while the browser parses and executes
   the 625 KB JS block.  Removed automatically on DOMContentLoaded.  */
#sf-boot-screen {
  position: fixed; inset: 0; z-index: 999999;
  background: #0d0d18;
  display: flex; flex-direction: column;
  align-items: center; justify-content: center;
  font-family: 'Segoe UI', system-ui, sans-serif;
  transition: opacity 0.45s ease;
}
#sf-boot-logo {
  width: 62px; height: 62px; margin-bottom: 22px;
}
#sf-boot-title {
  font-size: 26px; font-weight: 700;
  color: #e8e8f0; letter-spacing: -0.3px;
  margin-bottom: 6px;
}
#sf-boot-sub {
  font-size: 12px; color: #6060a0; margin-bottom: 32px;
}
#sf-boot-track {
  width: 280px; height: 3px;
  background: #1a1a2e; border-radius: 2px; overflow: hidden;
}
#sf-boot-fill {
  height: 100%; width: 4%; background: #7b5ef8; border-radius: 2px;
  transition: width 0.4s ease;
}
#sf-boot-status {
  font-size: 10px; color: #3a3a5a;
  margin-top: 14px; letter-spacing: 0.5px;
}
/* The native splash already covers startup. Keeping this second composited
   layer hidden prevents stale rectangular paint tiles on integrated GPUs. */
#sf-boot-screen { display: none !important; }
</style>

<!-- ══ IN-BROWSER BOOT SCREEN (low-perf devices only) ══════════════
     Visible from first paint until DOMContentLoaded fires.
     The SVG logo is a simplified diamond-aperture matching the splash. -->
<div id="sf-boot-screen">
  <svg id="sf-boot-logo" viewBox="0 0 62 62" xmlns="http://www.w3.org/2000/svg">
    <polygon points="31,2 60,31 31,60 2,31" fill="#7b5ef8"/>
    <polygon points="31,10 52,31 31,52 10,31" fill="#5a42d6"/>
    <g opacity="0.85">
      <polygon points="31,15 44,24 38,38 24,38 18,24" fill="#9b7fff" opacity="0.0"/>
      <path d="M31 20 L40 26 L37 36 L25 36 L22 26 Z" fill="none"/>
      <!-- 6 aperture blades -->
      <polygon points="31,14 35,22 31,20" fill="#c0b0ff"/>
      <polygon points="14,23 22,26 18,23" fill="#c0b0ff"/>
      <polygon points="14,39 22,36 18,39" fill="#c0b0ff"/>
      <polygon points="31,48 35,40 31,42" fill="#c0b0ff"/>
      <polygon points="48,39 40,36 44,39" fill="#c0b0ff"/>
      <polygon points="48,23 40,26 44,23" fill="#c0b0ff"/>
    </g>
    <circle cx="31" cy="31" r="6" fill="#0d0d18"/>
    <circle cx="31" cy="31" r="3.5" fill="#9b7fff"/>
  </svg>
  <div id="sf-boot-title">Skript</div>
  <div id="sf-boot-sub">Professional Screenwriting</div>
  <div id="sf-boot-track"><div id="sf-boot-fill"></div></div>
  <div id="sf-boot-status">LOADING</div>
</div>
<script>
(function(){
  var fill   = document.getElementById('sf-boot-fill');
  var status = document.getElementById('sf-boot-status');
  var msgs   = ['LOADING','INITIALISING','PREPARING WORKSPACE','STARTING ENGINE','ALMOST READY'];
  var pct = 4, step = 0;
  var iv = setInterval(function(){
    pct  = Math.min(88, pct + (Math.random() * 6 + 2));
    step = Math.min(msgs.length - 1, Math.floor(pct / 20));
    if (fill)   fill.style.width   = pct + '%';
    if (status) status.textContent = msgs[step];
  }, 380);
  document.addEventListener('DOMContentLoaded', function(){
    clearInterval(iv);
    if (fill)   fill.style.width   = '100%';
    if (status) status.textContent = 'READY';
    setTimeout(function(){
      var s = document.getElementById('sf-boot-screen');
      if (!s) return;
      s.style.opacity = '0';
      setTimeout(function(){ try{ s.parentNode.removeChild(s); }catch(e){} }, 480);
    }, 250);
  });
})();
</script>"""
        # The native Tk splash is the sole startup screen. The former browser
        # boot overlay faded a fixed compositor layer immediately before the
        # Welcome screen and could leave a rectangular stale tile on low-end
        # Intel graphics. Strip that redundant layer before serving the page.
        boot_start = injection.find('#sf-boot-screen {')
        boot_end = injection.rfind('</script>')
        if boot_start >= 0 and boot_end > boot_start:
            injection = injection[:boot_start] + '</style>'
    html = html.replace('</head>', injection + '\n</head>', 1)
    return html.encode('utf-8')

# ═══════════════════════════════════════════════════════════════════
#  HTTP API SERVER  (127.0.0.1 only — not visible on network)
# ═══════════════════════════════════════════════════════════════════
# ── App data directories ─────────────────────────────────────────────────
def _copy_legacy_tree(source, destination):
    """Copy a legacy data tree without deleting or overwriting user files."""
    source, destination = pathlib.Path(source), pathlib.Path(destination)
    if not source.is_dir():
        return True, set()
    success = True
    copied = set()
    try:
        entries = list(source.rglob('*'))
    except OSError:
        return False, copied
    for item in entries:
        try:
            if item.is_symlink():
                continue
            relative = item.relative_to(source)
            target = destination / relative
            if item.is_dir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if not item.is_file() or target.exists():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            temporary = target.with_name(f'.{target.name}.{uuid.uuid4().hex}.migrate.tmp')
            try:
                shutil.copy2(item, temporary)
                if not target.exists():
                    os.replace(temporary, target)
                    copied.add(relative)
            finally:
                if temporary.exists():
                    temporary.unlink()
        except OSError:
            success = False
    return success, copied


def _rewrite_migrated_recent_paths(legacy_scripts, scripts, userdata, copied_scripts):
    """Point a copied recent-project list at safely migrated Skript copies."""
    recent = pathlib.Path(userdata) / 'recent_scripts.json'
    if not recent.is_file():
        return
    try:
        items = json.loads(recent.read_text('utf-8'))
        if not isinstance(items, list):
            return
        legacy_root = pathlib.Path(legacy_scripts).resolve()
        changed = False
        for item in items:
            if not isinstance(item, dict) or not item.get('path'):
                continue
            old_path = pathlib.Path(item['path'])
            try:
                relative = old_path.resolve().relative_to(legacy_root)
            except (OSError, ValueError):
                continue
            if relative not in copied_scripts:
                continue
            migrated = pathlib.Path(scripts) / relative
            if migrated.is_file():
                item['path'] = str(migrated)
                changed = True
        if changed:
            _atomic_write_bytes(recent, json.dumps(items, indent=2), backup_count=1)
    except (OSError, ValueError, TypeError, json.JSONDecodeError):
        pass


def _migrate_legacy_documents(legacy_base, base):
    """Safely copy projects and recovery data from the earlier app folder."""
    legacy_base, base = pathlib.Path(legacy_base), pathlib.Path(base)
    if not legacy_base.is_dir() or legacy_base.resolve() == base.resolve():
        return
    userdata = base / 'userdata'
    marker = userdata / '.skript-migration-complete'
    if marker.exists():
        return
    scripts = base / 'scripts'
    scripts_ok, copied_scripts = _copy_legacy_tree(legacy_base / 'scripts', scripts)
    userdata_ok, _copied_userdata = _copy_legacy_tree(legacy_base / 'userdata', userdata)
    _rewrite_migrated_recent_paths(
        legacy_base / 'scripts', scripts, userdata, copied_scripts
    )
    if scripts_ok and userdata_ok:
        try:
            _atomic_write_bytes(marker, b'Earlier app data copied without deleting originals.\n', backup_count=0)
        except OSError:
            pass


def _app_dirs(home=None):
    """Return Skript's data folders and preserve content from the earlier app folder."""
    documents = pathlib.Path(home or pathlib.Path.home()) / 'Documents'
    base = documents / 'Skript'
    userdata = base / 'userdata'
    scripts = base / 'scripts'
    userdata.mkdir(parents=True, exist_ok=True)
    scripts.mkdir(parents=True, exist_ok=True)
    _migrate_legacy_documents(documents / ('Script' + 'Forge'), base)
    return userdata, scripts

USERDATA_DIR, SCRIPTS_DIR = None, None   # set on first use

def _get_dirs():
    global USERDATA_DIR, SCRIPTS_DIR
    if USERDATA_DIR is None:
        USERDATA_DIR, SCRIPTS_DIR = _app_dirs()
    return USERDATA_DIR, SCRIPTS_DIR


_RECOVERY_HISTORY_LIMIT = 30


def _recovery_history_dir(userdata_dir, create=True):
    folder = pathlib.Path(userdata_dir) / 'recovery_history'
    if create:
        folder.mkdir(parents=True, exist_ok=True)
    return folder


def _archive_recovery_snapshot(userdata_dir, payload=None, reason='automatic'):
    """Keep a dated recovery copy without ever writing into a project folder."""
    userdata_dir = pathlib.Path(userdata_dir)
    if payload is None:
        live = userdata_dir / 'recovery.recover'
        if not live.exists():
            return None
        payload = live.read_bytes()
    payload = payload.encode('utf-8') if isinstance(payload, str) else bytes(payload)
    _validate_project_bytes(payload)
    history = _recovery_history_dir(userdata_dir)
    digest = hashlib.sha256(payload).hexdigest()
    newest = max(history.glob('*.recover'), key=lambda item: item.stat().st_mtime, default=None)
    if newest is not None:
        try:
            if hashlib.sha256(newest.read_bytes()).hexdigest() == digest:
                return newest
        except OSError:
            pass
    stamp = time.strftime('%Y%m%d-%H%M%S')
    safe_reason = re.sub(r'[^a-z0-9-]+', '-', str(reason).lower()).strip('-') or 'automatic'
    destination = history / f'{stamp}-{safe_reason}-{uuid.uuid4().hex[:8]}.recover'
    _atomic_write_bytes(destination, payload, backup_count=0)
    snapshots = sorted(history.glob('*.recover'), key=lambda item: item.stat().st_mtime, reverse=True)
    for expired in snapshots[_RECOVERY_HISTORY_LIMIT:]:
        try:
            expired.unlink()
        except OSError:
            pass
    return destination


def _recovery_candidate_paths(userdata_dir, scripts_dir):
    userdata_dir, scripts_dir = pathlib.Path(userdata_dir), pathlib.Path(scripts_dir)
    candidates = []
    live = userdata_dir / 'recovery.recover'
    for index, path in enumerate([live] + [_rolling_backup_path(live, i) for i in range(1, 11)]):
        if path.exists():
            candidates.append((path, 'Crash recovery' if index == 0 else 'Recent automatic recovery'))
    # Browsing recovery must remain read-only. A locked or unavailable history
    # folder must not hide otherwise valid crash snapshots and project backups.
    history = _recovery_history_dir(userdata_dir, create=False)
    try:
        if history.is_dir():
            candidates.extend((path, 'Recovery history') for path in history.glob('*.recover'))
    except OSError:
        pass
    try:
        if scripts_dir.is_dir():
            candidates.extend((path, 'Saved project backup') for path in scripts_dir.glob('*.script.bak*'))
    except OSError:
        pass
    try:
        for item in _load_recent(userdata_dir):
            project_path = pathlib.Path(item.get('path', ''))
            for index in range(1, 4):
                backup = _rolling_backup_path(project_path, index)
                if backup.exists():
                    candidates.append((backup, 'Saved project backup'))
    except Exception:
        pass
    unique = {}
    for path, source in candidates:
        try:
            unique[str(path.resolve())] = (path, source)
        except OSError:
            continue
    return list(unique.values())


def _recovery_entries(userdata_dir, scripts_dir):
    entries = []
    for path, source in _recovery_candidate_paths(userdata_dir, scripts_dir):
        try:
            raw, data = _validate_project_bytes(path.read_bytes())
            projects = data.get('projects') if data.get('schema') == 'com.skript.workspace-recovery' else [data]
            projects = [item for item in projects if isinstance(item, dict)]
            titles = [str(item.get('title') or 'Untitled')[:120] for item in projects]
            captured = data.get('capturedAt') or data.get('savedAt') or data.get('updatedAt')
            entries.append({
                'id': hashlib.sha256(str(path.resolve()).encode('utf-8')).hexdigest(),
                'source': source,
                'capturedAt': captured or time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(path.stat().st_mtime)),
                'titles': titles,
                'projectCount': len(projects),
                'lineCount': sum(len(item.get('lines') or []) for item in projects),
                'size': len(raw.encode('utf-8')),
            })
        except Exception:
            continue
    entries.sort(key=lambda item: item.get('capturedAt') or '', reverse=True)
    return entries


def _load_recovery_entry(userdata_dir, scripts_dir, entry_id):
    for path, _source in _recovery_candidate_paths(userdata_dir, scripts_dir):
        try:
            candidate_id = hashlib.sha256(str(path.resolve()).encode('utf-8')).hexdigest()
            if secrets.compare_digest(candidate_id, str(entry_id or '')):
                raw, _data = _validate_project_bytes(path.read_bytes())
                return raw
        except Exception:
            continue
    raise FileNotFoundError('That recovery copy is no longer available. Refresh the Recovery Centre and try again.')


def _powershell_file_dialog(filetypes, title, save=False, initial_name='', initial_dir=None):
    """Windows Forms fallback for Python builds that do not include Tk."""
    if sys.platform != 'win32':
        return False

    def ps_quote(value):
        return "'" + str(value or '').replace("'", "''") + "'"

    _, scripts_dir = _get_dirs()
    dialog_type = 'SaveFileDialog' if save else 'OpenFileDialog'
    filter_parts = []
    for label, pattern in filetypes:
        filter_parts.extend([f'{label} ({pattern})', pattern])
    filter_value = '|'.join(filter_parts)
    commands = [
        'Add-Type -AssemblyName System.Windows.Forms',
        f'$dialog = New-Object System.Windows.Forms.{dialog_type}',
        f'$dialog.Title = {ps_quote(title)}',
        f'$dialog.InitialDirectory = {ps_quote(initial_dir or scripts_dir)}',
        f'$dialog.Filter = {ps_quote(filter_value)}',
    ]
    if save:
        commands.extend([
            "$dialog.DefaultExt = 'script'",
            "$dialog.AddExtension = $true",
            f'$dialog.FileName = {ps_quote(initial_name)}',
        ])
    commands.append("if ($dialog.ShowDialog() -eq [System.Windows.Forms.DialogResult]::OK) { $dialog.FileName }")
    encoded = base64.b64encode('\n'.join(commands).encode('utf-16le')).decode('ascii')
    try:
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        result = subprocess.run(
            ['powershell.exe', '-NoProfile', '-STA', '-EncodedCommand', encoded],
            capture_output=True, text=True, timeout=120,
            startupinfo=si, creationflags=subprocess.CREATE_NO_WINDOW,
        )
        if result.returncode != 0:
            return False
        return result.stdout.strip() or None
    except Exception:
        return False


def _open_file_dialog(filetypes, title, save=False, initial_name='', initial_dir=None):
    """Open a native file dialog using tkinter (stdlib)."""
    try:
        import tkinter as tk
        from tkinter import filedialog
        root = tk.Tk()
        root.withdraw()
        root.attributes('-topmost', True)
        root.update()
        _, scripts_dir = _get_dirs()
        kw = dict(parent=root, title=title,
                  initialdir=str(initial_dir or scripts_dir),
                  filetypes=filetypes)
        if save:
            kw['defaultextension'] = '.script'
            kw['initialfile'] = initial_name
            path = filedialog.asksaveasfilename(**kw)
        else:
            path = filedialog.askopenfilename(**kw)
        root.destroy()
        return path or None
    except Exception:
        return _powershell_file_dialog(filetypes, title, save, initial_name, initial_dir)


def _powershell_folder_dialog(title, initial_dir=None):
    """Windows Forms folder-picker fallback for packaged or restricted Tk builds."""
    if sys.platform != 'win32':
        return False

    def ps_quote(value):
        return "'" + str(value or '').replace("'", "''") + "'"

    _, scripts_dir = _get_dirs()
    commands = [
        'Add-Type -AssemblyName System.Windows.Forms',
        '$dialog = New-Object System.Windows.Forms.FolderBrowserDialog',
        f'$dialog.Description = {ps_quote(title)}',
        f'$dialog.SelectedPath = {ps_quote(initial_dir or scripts_dir)}',
        '$dialog.ShowNewFolderButton = $true',
        "if ($dialog.ShowDialog() -eq [System.Windows.Forms.DialogResult]::OK) { $dialog.SelectedPath }",
    ]
    encoded = base64.b64encode('\n'.join(commands).encode('utf-16le')).decode('ascii')
    try:
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        result = subprocess.run(
            ['powershell.exe', '-NoProfile', '-STA', '-EncodedCommand', encoded],
            capture_output=True, text=True, timeout=120,
            startupinfo=si, creationflags=subprocess.CREATE_NO_WINDOW,
        )
        if result.returncode != 0:
            return False
        return result.stdout.strip() or None
    except Exception:
        return False


def _open_folder_dialog(title='Select Folder', initial_dir=None):
    """Open a native folder dialog with the same packaged fallback as file dialogs."""
    root = None
    try:
        import tkinter as tk
        from tkinter import filedialog
        root = tk.Tk()
        root.withdraw()
        root.attributes('-topmost', True)
        root.update_idletasks()
        _, scripts_dir = _get_dirs()
        path = filedialog.askdirectory(
            parent=root,
            title=title,
            initialdir=str(initial_dir or scripts_dir),
            mustexist=False,
        )
        return path or None
    except Exception:
        return _powershell_folder_dialog(title, initial_dir)
    finally:
        if root is not None:
            try:
                root.destroy()
            except Exception:
                pass


_COLLAB_GUEST_ROUTES = {
    '/api/collab/auth',
    '/api/collab/status',
    '/api/collab/script',
    '/api/collab/notes',
    '/api/collab/note',
    '/api/collab/reply',
    '/api/collab/ping',
    '/api/collab/edit',
    '/api/collab/events',
}

def _request_ip(handler):
    # This service is not behind a trusted proxy. Accepting X-Forwarded-For
    # would let a LAN client evade token binding, lockouts, and IP revocation.
    return (handler.client_address[0] or '?').strip()

def _origin_allowed(origin):
    if not origin:
        return None
    try:
        p = urlparse(origin)
        host = p.hostname or ''
        port = p.port
        # Privileged routes still require the per-launch API token. Allowing a
        # loopback-hosted app window on a different local port lets stale or
        # restored Edge windows reconnect without weakening API authorization.
        if host in ('127.0.0.1', 'localhost'):
            return origin
        if port == _COLLAB_PORT_VAL and host in _get_local_ips():
            return origin
    except Exception:
        pass
    return None

def _requires_api_token(path):
    if not path.startswith('/api/'):
        return False
    if path in ('/api/version',):
        return False
    if path in _COLLAB_GUEST_ROUTES:
        return False
    return True

def _check_api_token(handler):
    if not _API_TOKEN:
        return False
    token = handler.headers.get('X-Skript-Token', '')
    try:
        return secrets.compare_digest(token, _API_TOKEN)
    except Exception:
        return False

def _new_collab_access(sess, role, ip):
    token = secrets.token_urlsafe(24)
    token_hash = hashlib.sha256(token.encode('utf-8')).hexdigest()
    sess.setdefault('access_tokens', {})[token_hash] = {
        'role': role,
        'ip': ip,
        'ts': time.time(),
    }
    return token

def _check_collab_access(handler, sess, allow_owner=True):
    if not sess.get('active'):
        return False
    dur = sess.get('duration_secs', 0)
    if dur and (time.time() - sess.get('created', 0)) > dur:
        sess['active'] = False
        return False
    if allow_owner and _check_api_token(handler):
        return True
    token = handler.headers.get('X-Collab-Token', '')
    if not token:
        return False
    token_hash = hashlib.sha256(token.encode('utf-8')).hexdigest()
    tokens = sess.get('access_tokens', {})
    info = tokens.get(token_hash)
    if not info and token in tokens:
        # Transparently migrate bearer tokens persisted by older versions.
        info = tokens.pop(token)
        tokens[token_hash] = info
    if not info:
        return False
    ip = _request_ip(handler)
    if info.get('ip') and info.get('ip') != ip:
        return False
    info['seen'] = time.time()
    return True

def _collab_access_role(handler, sess):
    """Return owner/edit/view for an authenticated collaboration request."""
    if _check_api_token(handler):
        return 'owner'
    token = handler.headers.get('X-Collab-Token', '')
    token_hash = hashlib.sha256(token.encode('utf-8')).hexdigest()
    tokens = sess.get('access_tokens', {})
    info = tokens.get(token_hash) or tokens.get(token, {})
    if not info or not _check_collab_access(handler, sess, allow_owner=False):
        return ''
    return info.get('role', 'view')


def _collab_public_notes(sess):
    """Strip network identifiers from comments before sending them to guests."""
    result = []
    for item in sess.get('notes', []):
        note = {key: value for key, value in item.items() if key != 'ip'}
        note['replies'] = [
            {key: value for key, value in reply.items() if key != 'ip'}
            for reply in item.get('replies', [])
        ]
        result.append(note)
    return result


def _collab_active_viewers(sess):
    now = time.time()
    active = []
    for ip, viewer in sess.get('viewers', {}).items():
        info = viewer if isinstance(viewer, dict) else {
            'seen': viewer, 'name': 'Viewer', 'role': 'view'
        }
        if info.get('ip') not in sess.get('revoked_ips', []) and now - info.get('seen', 0) < 60:
            active.append({
                'id': info.get('client_id', ip),
                'name': info.get('name', 'Viewer'),
                'role': info.get('role', 'view'),
                'color': info.get('color', ''),
            })
    return active


def _collab_public_state(sess):
    viewers = _collab_active_viewers(sess)
    return {
        'ok': True,
        'script': sess.get('script', {}),
        'revision': sess.get('revision', 1),
        'notes': _collab_public_notes(sess),
        'viewer_count': len(viewers),
        'viewers': viewers,
        'edits': sess.get('edit_log', [])[-30:],
        'conflicts': sess.get('conflicts', [])[-20:],
        'active': bool(sess.get('active')),
    }


def _collab_emit(sess, event_type='state'):
    """Publish a bounded, secret-free event and wake connected SSE clients."""
    sid = sess.get('session_id', '')
    if not sid:
        return 0
    with _COLLAB_EVENT_CONDITION:
        state = _COLLAB_EVENTS.setdefault(sid, {'seq': 0, 'events': []})
        state['seq'] += 1
        event = {
            'id': state['seq'],
            'event': event_type,
            'data': _collab_public_state(sess),
        }
        state['events'].append(event)
        state['events'] = state['events'][-128:]
        _COLLAB_EVENT_CONDITION.notify_all()
        return state['seq']

def _collab_merge_script(base, server, incoming):
    """Three-way, line-id-aware merge that records rather than loses conflicts."""
    def keyed(script):
        result, order = {}, []
        for index, line in enumerate((script or {}).get('lines', [])):
            item = dict(line)
            key = item.get('lineId') or f'index-{index}'
            item['lineId'] = key
            result[key] = item
            order.append(key)
        return result, order
    base_map, _ = keyed(base)
    server_map, server_order = keyed(server)
    incoming_map, incoming_order = keyed(incoming)
    order = list(dict.fromkeys(incoming_order + server_order))
    merged, conflicts = [], []
    for key in order:
        before, current, proposed = base_map.get(key), server_map.get(key), incoming_map.get(key)
        if proposed == before:
            chosen = current
        elif current == before or current == proposed:
            chosen = proposed
        elif proposed is None and current is not None and before == current:
            chosen = None
        elif current is None and proposed is not None and before is None:
            chosen = proposed
        else:
            chosen = proposed or current
            conflicts.append({'lineId': key, 'base': before, 'server': current,
                              'incoming': proposed, 'resolved': 'incoming'})
        if chosen is not None:
            merged.append(chosen)
    return {
        'title': (incoming or {}).get('title') or (server or {}).get('title') or 'Untitled',
        'lines': merged,
    }, conflicts


def _collab_apply_edit(sess, incoming, base_revision, author, role):
    """Atomically merge, version, persist, and broadcast one document edit."""
    if not isinstance(incoming, dict) or not isinstance(incoming.get('lines', []), list):
        raise ValueError('Invalid script payload')
    if len(incoming.get('lines', [])) > 20000:
        raise ValueError('Script has too many lines')
    with _COLLAB_LOCK:
        current_revision = int(sess.get('revision', 1))
        conflicts = []
        if base_revision != current_revision:
            base = sess.get('history', {}).get(str(base_revision), sess.get('script', {}))
            incoming, conflicts = _collab_merge_script(base, sess.get('script', {}), incoming)
        sess['script'] = incoming
        sess['revision'] = current_revision + 1
        sess.setdefault('history', {})[str(sess['revision'])] = incoming
        sess['history'] = dict(list(sess['history'].items())[-25:])
        entry = {'revision': sess['revision'], 'author': author, 'role': role,
                 'ts': time.time(), 'conflicts': len(conflicts)}
        sess.setdefault('edit_log', []).append(entry)
        sess['edit_log'] = sess['edit_log'][-200:]
        if conflicts:
            for conflict in conflicts:
                conflict.update({'revision': sess['revision'], 'author': author,
                                 'ts': time.time()})
            sess.setdefault('conflicts', []).extend(conflicts)
            sess['conflicts'] = sess['conflicts'][-100:]
        _save_collab_session(sess['session_id'])
        _collab_emit(sess, 'script')
        return sess['revision'], sess['script'], conflicts


def _get_favicon(prefer_ico=False):
    """Return the packaged Skript icon, with the legacy SVG as fallback."""
    try:
        if prefer_ico:
            return _resource_path('assets', 'skript.ico').read_bytes(), 'image/x-icon'
        return _resource_path('assets', 'skript-icon.png').read_bytes(), 'image/png'
    except Exception:
        return base64.b64decode(
        'PHN2ZyB4bWxucz0naHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmcnIHZpZXdCb3g9JzAgMCA2NCA2NCc+'
        'PHJlY3Qgd2lkdGg9JzY0JyBoZWlnaHQ9JzY0JyByeD0nMTInIGZpbGw9JyMxYTFhMmUnLz48cmVjdCB4PScx'
        'MicgeT0nMTAnIHdpZHRoPSc0MCcgaGVpZ2h0PSc1JyByeD0nMicgZmlsbD0nI2Q0YTg0MycvPjxyZWN0IHg9'
        'JzEyJyB5PScyMCcgd2lkdGg9JzMwJyBoZWlnaHQ9JzMnIHJ4PScxLjUnIGZpbGw9JyNmZmZmZmYnIG9wYWNp'
        'dHk9JzAuNicvPjxyZWN0IHg9JzEyJyB5PScyNycgd2lkdGg9JzQwJyBoZWlnaHQ9JzMnIHJ4PScxLjUnIGZp'
        'bGw9JyNmZmZmZmYnIG9wYWNpdHk9JzAuNicvPjxyZWN0IHg9JzEyJyB5PSczNCcgd2lkdGg9JzM1JyBoZWln'
        'aHQ9JzMnIHJ4PScxLjUnIGZpbGw9JyNmZmZmZmYnIG9wYWNpdHk9JzAuNicvPjxyZWN0IHg9JzIyJyB5PSc0'
        'Mycgd2lkdGg9JzIwJyBoZWlnaHQ9JzMnIHJ4PScxLjUnIGZpbGw9JyM1YjliZDUnIG9wYWNpdHk9JzAuOCcv'
        'PjxyZWN0IHg9JzE4JyB5PSc1MCcgd2lkdGg9JzI4JyBoZWlnaHQ9JzMnIHJ4PScxLjUnIGZpbGw9JyM1Yjli'
        'ZDUnIG9wYWNpdHk9JzAuNicvPjwvc3ZnPg=='
        ), 'image/svg+xml'

def _resource_path(*parts):
    """Resolve bundled/static files from source, PyInstaller one-dir, or one-file."""
    bases = []
    frozen_base = getattr(sys, '_MEIPASS', None)
    if frozen_base:
        bases.append(pathlib.Path(frozen_base))
    if getattr(sys, 'frozen', False):
        bases.append(pathlib.Path(sys.executable).parent)
    bases.append(pathlib.Path(__file__).parent)
    for base in bases:
        candidate = base.joinpath(*parts)
        if candidate.exists():
            return candidate
    return bases[0].joinpath(*parts)


_WORD_NS = 'http://schemas.openxmlformats.org/wordprocessingml/2006/main'
_DC_NS = 'http://purl.org/dc/elements/1.1/'


def _word_qn(name):
    return f'{{{_WORD_NS}}}{name}'


def _docx_paragraphs(payload):
    """Extract styled paragraphs from DOCX using only the standard library."""
    with zipfile.ZipFile(io.BytesIO(payload)) as archive:
        infos = archive.infolist()
        if len(infos) > 5000 or sum(item.file_size for item in infos) > 50 * 1024 * 1024:
            raise ValueError('The Word document is too large to import safely')
        if 'word/document.xml' not in archive.namelist():
            raise ValueError('This file is not a valid Word DOCX document')

        style_names, style_layouts = {}, {}
        if 'word/styles.xml' in archive.namelist():
            try:
                styles_root = ET.fromstring(archive.read('word/styles.xml'))
                for style in styles_root.iter(_word_qn('style')):
                    style_id = style.get(_word_qn('styleId'), '')
                    name_node = style.find(_word_qn('name'))
                    style_names[style_id] = (name_node.get(_word_qn('val'), '') if name_node is not None else style_id)
                    style_ppr = style.find(_word_qn('pPr'))
                    style_ind = style_ppr.find(_word_qn('ind')) if style_ppr is not None else None
                    style_jc = style_ppr.find(_word_qn('jc')) if style_ppr is not None else None
                    left_raw = ((style_ind.get(_word_qn('start')) or style_ind.get(_word_qn('left')))
                                if style_ind is not None else '')
                    style_layouts[style_id] = {
                        'left': int(left_raw) if re.fullmatch(r'-?\d+', left_raw or '') else None,
                        'alignment': (style_jc.get(_word_qn('val'), '') if style_jc is not None else '').lower(),
                    }
            except ET.ParseError:
                pass

        document_root = ET.fromstring(archive.read('word/document.xml'))
        paragraphs, page, pending_paragraph_break = [], 1, False
        for paragraph in document_root.iter(_word_qn('p')):
            ppr = paragraph.find(_word_qn('pPr'))
            style_id = ''
            page_break_before = False
            if ppr is not None:
                style_node = ppr.find(_word_qn('pStyle'))
                if style_node is not None:
                    style_id = style_node.get(_word_qn('val'), '')
                page_break_before = ppr.find(_word_qn('pageBreakBefore')) is not None
            style_layout = style_layouts.get(style_id, {})
            direct_ind = ppr.find(_word_qn('ind')) if ppr is not None else None
            direct_jc = ppr.find(_word_qn('jc')) if ppr is not None else None
            direct_left_raw = ((direct_ind.get(_word_qn('start')) or direct_ind.get(_word_qn('left')))
                               if direct_ind is not None else '')
            left = (int(direct_left_raw) if re.fullmatch(r'-?\d+', direct_left_raw or '')
                    else style_layout.get('left'))
            alignment = ((direct_jc.get(_word_qn('val'), '') if direct_jc is not None else '')
                         or style_layout.get('alignment', '')).lower()
            if page_break_before and paragraphs:
                page += 1

            pieces, has_page_break, bold_chars, total_chars = [], False, 0, 0
            for node in paragraph.iter():
                if node.tag == _word_qn('t'):
                    value = node.text or ''
                    pieces.append(value)
                    total_chars += len(value)
                    run = next((candidate for candidate in paragraph.iter(_word_qn('r')) if node in list(candidate)), None)
                    if run is not None:
                        rpr = run.find(_word_qn('rPr'))
                        if rpr is not None and rpr.find(_word_qn('b')) is not None:
                            bold_chars += len(value)
                elif node.tag == _word_qn('tab'):
                    pieces.append('\t')
                elif node.tag == _word_qn('br'):
                    if node.get(_word_qn('type'), '') == 'page':
                        has_page_break = True
                    else:
                        pieces.append(' ')
                elif node.tag == _word_qn('lastRenderedPageBreak'):
                    has_page_break = True

            style_name = style_names.get(style_id, style_id)
            text = re.sub(r'\s+', ' ', ''.join(pieces).replace('\u00a0', ' ')).strip()
            if text:
                paragraphs.append({
                    'text': text, 'style': style_name,
                    'bold': bool(total_chars and bold_chars >= total_chars * .6),
                    'page': page, 'left': left, 'alignment': alignment,
                    'breakBefore': bool(pending_paragraph_break),
                })
                pending_paragraph_break = False
            else:
                pending_paragraph_break = True
            if has_page_break:
                page += 1

        title = ''
        if 'docProps/core.xml' in archive.namelist():
            try:
                core = ET.fromstring(archive.read('docProps/core.xml'))
                title_node = core.find(f'{{{_DC_NS}}}title')
                title = (title_node.text or '').strip() if title_node is not None else ''
            except ET.ParseError:
                pass
        return paragraphs, title


def _rtf_to_paragraphs(payload):
    text = payload.decode('latin-1', errors='ignore')
    text = re.sub(r"\\'([0-9a-fA-F]{2})", lambda match: bytes.fromhex(match.group(1)).decode('cp1252', 'replace'), text)
    text = re.sub(r'\\u(-?\d+)\??', lambda match: chr(int(match.group(1)) % 65536), text)
    text = re.sub(r'\\line\b ?', ' ', text)
    text = re.sub(r'\\par\b ?', '\n', text)
    text = re.sub(r'\\tab\b ?', '\t', text)
    text = re.sub(r'\\[a-zA-Z]+-?\d* ?|\\[^a-zA-Z]', '', text)
    text = text.replace('{', '').replace('}', '')
    return [{'text': re.sub(r'\s+', ' ', line).strip(), 'style': '', 'bold': False, 'page': 1}
            for line in text.splitlines() if re.sub(r'\s+', ' ', line).strip()]


def _convert_legacy_doc_to_docx(payload):
    """Use an installed office suite for user-initiated legacy DOC conversion."""
    with tempfile.TemporaryDirectory(prefix='SkriptWordImport_') as temp_name:
        temp_dir = pathlib.Path(temp_name)
        source = temp_dir / 'source.doc'
        target = temp_dir / 'source.docx'
        source.write_bytes(payload)

        candidates = [
            shutil.which('soffice'),
            r'C:\Program Files\LibreOffice\program\soffice.exe',
            r'C:\Program Files (x86)\LibreOffice\program\soffice.exe',
        ]
        for candidate in filter(None, candidates):
            try:
                subprocess.run(
                    [str(candidate), '--headless', '--convert-to', 'docx', '--outdir', str(temp_dir), str(source)],
                    check=False, capture_output=True, timeout=45,
                    creationflags=(subprocess.CREATE_NO_WINDOW if sys.platform == 'win32' else 0),
                )
                if target.exists() and target.stat().st_size > 200:
                    return target.read_bytes(), 'LibreOffice'
            except (OSError, subprocess.TimeoutExpired):
                pass

        if sys.platform == 'win32':
            ps_script = (
                "$InputPath=[Environment]::GetEnvironmentVariable('SKRIPT_WORD_INPUT')\n"
                "$OutputPath=[Environment]::GetEnvironmentVariable('SKRIPT_WORD_OUTPUT')\n"
                "$word=$null;$doc=$null\n"
                "try{$word=New-Object -ComObject Word.Application;$word.Visible=$false;"
                "$word.DisplayAlerts=0;$doc=$word.Documents.Open($InputPath,$false,$true);"
                "$doc.SaveAs2($OutputPath,16)}finally{if($doc){$doc.Close($false)};"
                "if($word){$word.Quit()}}\n"
            )
            try:
                conversion_env = os.environ.copy()
                conversion_env['SKRIPT_WORD_INPUT'] = str(source)
                conversion_env['SKRIPT_WORD_OUTPUT'] = str(target)
                subprocess.run(
                    ['powershell.exe', '-NoLogo', '-NoProfile', '-NonInteractive', '-WindowStyle', 'Hidden', '-Command', '-'],
                    input=ps_script, text=True, env=conversion_env,
                    check=False, capture_output=True, timeout=60,
                    creationflags=subprocess.CREATE_NO_WINDOW,
                )
                if target.exists() and target.stat().st_size > 200:
                    return target.read_bytes(), 'Microsoft Word'
            except (OSError, subprocess.TimeoutExpired):
                pass
    raise ValueError('Legacy .doc import needs Microsoft Word or LibreOffice. Open the file there, save it as .docx, then import it again.')


def _word_cover_and_script(paragraphs, fallback_title):
    cover, script_paragraphs = {}, list(paragraphs)
    first_page = [item for item in paragraphs if item.get('page') == 1]
    later_pages = [item for item in paragraphs if item.get('page', 1) > 1]
    has_byline = any(re.match(r'^(?:written by|screenplay by|story by|by)$', item['text'], re.I) for item in first_page)
    styled_title = next((item['text'] for item in first_page if 'title' in item.get('style', '').lower()), '')
    if later_pages and len(first_page) <= 18 and (has_byline or styled_title):
        cover['title'] = styled_title or (first_page[0]['text'] if first_page else fallback_title)
        for index, item in enumerate(first_page):
            if re.match(r'^(?:written by|screenplay by|story by|by)$', item['text'], re.I) and index + 1 < len(first_page):
                cover['author'] = first_page[index + 1]['text']
                break
        script_paragraphs = later_pages
    return cover, script_paragraphs


def _classify_word_paragraphs(paragraphs):
    lines = []
    texts = [item.get('text', '').strip() for item in paragraphs]
    def decorate(line, item):
        line['_wordLeft'] = item.get('left') if isinstance(item.get('left'), (int, float)) else None
        line['_wordAlign'] = str(item.get('alignment') or '')
        line['_wordBreakBefore'] = bool(item.get('breakBefore'))
        line['_bold'] = bool(item.get('bold'))
        return line

    for index, item in enumerate(paragraphs):
        text = item.get('text', '').strip()
        if not text:
            continue
        upper, style = text.upper(), item.get('style', '').lower()
        next_text = texts[index + 1].strip() if index + 1 < len(texts) else ''
        inline = re.match(r"^([^:\n]{2,36}):\s+(.+)$", text)
        inline_name = inline.group(1).strip() if inline else ''
        inline_valid = (inline and inline_name[:1].isupper()
                        and not re.match(r'^(?:NOTE|TITLE|SUPER|CARD|CUT|FADE|DISSOLVE)$', inline_name, re.I)
                        and len(inline_name.split()) <= 7
                        and all(ch.isalnum() or ch in " .#&'’`-/" for ch in inline_name))
        if inline_valid:
            lines.extend([
                decorate({'type': 'character', 'text': inline_name,
                          'importMeta': {'source': 'word', 'detectedType': 'character', 'confidence': 96,
                                         'needsReview': False, 'reviewed': False,
                                         'reason': 'Explicit NAME: dialogue structure.'}}, item),
                decorate({'type': 'dialogue', 'text': inline.group(2).strip(),
                          'importMeta': {'source': 'word', 'detectedType': 'dialogue', 'confidence': 96,
                                         'needsReview': False, 'reviewed': False,
                                         'reason': 'Explicit NAME: dialogue structure.'}}, item),
            ])
            continue
        if 'parenth' in style or (text.startswith('(') and text.endswith(')')):
            line_type = 'parenthetical'
        elif 'character' in style or 'speaker' in style:
            line_type = 'character'
        elif 'dialog' in style:
            line_type = 'dialogue'
        elif ('transition' in style or re.search(
                r'(?:(?:CUT|HARD CUT|JUMP CUT|SMASH CUT|MATCH CUT|FLASH CUT|TIME CUT|WIPE|DISSOLVE|MATCH DISSOLVE) TO:|CUT BACK TO:|BACK TO:|FADE (?:IN|OUT)[:.]?|FADE TO (?:BLACK|WHITE):?|IRIS (?:IN|OUT):?)$', upper)):
            line_type = 'transition'
        elif 'stage direction' in style or 'stage-direction' in style:
            line_type = 'stage-direction'
        elif re.match(r'^ACT\s+(?:[IVX]+|ONE|TWO|THREE|FOUR|FIVE|\d+)\b', upper):
            line_type = 'act'
        elif ('scene' in style or 'slug' in style or
              re.match(r'^(?:INT\.?|EXT\.?|INT\.?/EXT\.?|EXT\.?/INT\.?)\s', upper) or
              re.match(r'^SCENE\s+\d+\b', upper)):
            line_type = 'scene'
        elif (text == upper and 1 <= len(text.split()) <= 6 and len(text) <= 40 and
              next_text and next_text != next_text.upper() and not re.match(r'^(?:THE END|END OF|CONTINUED)', upper)):
            line_type = 'character'
        elif lines and lines[-1]['type'] in ('character', 'parenthetical'):
            line_type = 'dialogue'
        else:
            line_type = 'action'
        style_evidence = re.search(r'(?:parenth|character|speaker|dialog|transition|stage direction|stage-direction|scene|slug)', style)
        result_line = {'type': line_type, 'text': text}
        if style_evidence:
            result_line['importMeta'] = {
                'source': 'word', 'detectedType': line_type, 'confidence': 98,
                'needsReview': False, 'reviewed': False,
                'reason': f'Word paragraph style “{item.get("style", "")}”.',
            }
        lines.append(decorate(result_line, item))
    return lines


def _import_word_bytes(payload, suffix, fallback_title='Imported Word Script'):
    converter = ''
    if suffix == '.docx':
        paragraphs, document_title = _docx_paragraphs(payload)
    elif suffix == '.doc':
        if payload.lstrip().startswith(b'{\\rtf'):
            paragraphs, document_title = _rtf_to_paragraphs(payload), ''
            converter = 'RTF reader'
        else:
            converted, converter = _convert_legacy_doc_to_docx(payload)
            paragraphs, document_title = _docx_paragraphs(converted)
    else:
        raise ValueError('Choose a .doc or .docx Word document')
    if not paragraphs:
        raise ValueError('No readable text was found in this Word document')
    title = document_title or fallback_title
    cover, script_paragraphs = _word_cover_and_script(paragraphs, title)
    lines = _classify_word_paragraphs(script_paragraphs)
    if not lines:
        raise ValueError('No script paragraphs were found in this Word document')
    return {'lines': lines, 'coverData': cover, 'titleHint': cover.get('title') or title,
            'paragraphCount': len(paragraphs), 'converter': converter}


class SFHandler(BaseHTTPRequestHandler):
    html_bytes = b''
    # Keep the browser's loopback connections alive. The editor makes frequent
    # small API calls; forcing a new TCP connection for every one can exhaust
    # the Windows ephemeral-port pool during long sessions and release tests.
    protocol_version = 'HTTP/1.1'

    def handle(self):
        try:
            super().handle()
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            # Browsers routinely close an idle keep-alive socket while a tab or
            # test context is shutting down. This is not an application error.
            pass

    def log_message(self, *a): pass

    def _cors(self):
        allowed = _origin_allowed(self.headers.get('Origin', ''))
        if allowed:
            self.send_header('Access-Control-Allow-Origin', allowed)
            self.send_header('Vary', 'Origin')
        self.send_header('Access-Control-Allow-Methods', 'GET,POST,OPTIONS')
        self.send_header('Access-Control-Allow-Headers',
                         'Content-Type, X-Skript-Token, X-Collab-Token, '
                         'X-Skript-Preserve-Recovery')

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header('Content-Length', '0')
        self._cors()
        self.end_headers()

    def _json(self, obj, status=200):
        body = json.dumps(obj).encode()
        self.send_response(status)
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', len(body))
        self._cors(); self.end_headers(); self.wfile.write(body)

    def _bytes(self, data, ct='application/octet-stream', status=200):
        self.send_response(status)
        self.send_header('Content-Type', ct)
        self.send_header('Content-Length', len(data))
        self._cors(); self.end_headers(); self.wfile.write(data)

    def do_GET(self):
        path = urlparse(self.path).path
        qs   = parse_qs(urlparse(self.path).query)
        origin = self.headers.get('Origin', '')
        if path in _COLLAB_GUEST_ROUTES and origin and not _origin_allowed(origin):
            self._json({'ok': False, 'error': 'Origin not allowed'}, 403)
            return
        if _requires_api_token(path) and not _check_api_token(self):
            self._json({'ok': False, 'error': 'Unauthorized'}, 403)
            return
        if path in ('/', '/index.html', ''):
            self._bytes(SFHandler.html_bytes, 'text/html; charset=utf-8')

        elif path in ('/favicon.ico', '/favicon.png'):
            favicon, content_type = _get_favicon(prefer_ico=path.endswith('.ico'))
            self._bytes(favicon, content_type)

        elif path.startswith('/vendor/pdfjs/'):
            name = pathlib.PurePosixPath(path).name
            if name not in ('pdf.min.mjs', 'pdf.worker.min.mjs'):
                self._json({'ok': False, 'error': 'Not found'}, 404)
                return
            vendor_path = _resource_path('vendor', 'pdfjs', name)
            try:
                self._bytes(vendor_path.read_bytes(), 'text/javascript; charset=utf-8')
            except Exception as exc:
                self._json({'ok': False, 'error': f'PDF.js asset unavailable: {exc}'}, 404)

        elif path.startswith('/vendor/ocr/'):
            relative = path.removeprefix('/vendor/ocr/').replace('\\', '/')
            allowed = {
                'tesseract.min.js': 'text/javascript; charset=utf-8',
                'worker.min.js': 'text/javascript; charset=utf-8',
                'lang/eng.traineddata.gz': 'application/gzip',
                'core/tesseract-core.wasm.js': 'text/javascript; charset=utf-8',
                'core/tesseract-core-lstm.wasm.js': 'text/javascript; charset=utf-8',
                'core/tesseract-core-simd.wasm.js': 'text/javascript; charset=utf-8',
                'core/tesseract-core-simd-lstm.wasm.js': 'text/javascript; charset=utf-8',
                'core/tesseract-core-relaxedsimd.wasm.js': 'text/javascript; charset=utf-8',
                'core/tesseract-core-relaxedsimd-lstm.wasm.js': 'text/javascript; charset=utf-8',
            }
            content_type = allowed.get(relative)
            if not content_type:
                self._json({'ok': False, 'error': 'Not found'}, 404)
                return
            asset = _resource_path('vendor', 'ocr', *pathlib.PurePosixPath(relative).parts)
            try:
                self._bytes(asset.read_bytes(), content_type)
            except Exception as exc:
                self._json({'ok': False, 'error': f'OCR asset unavailable: {exc}'}, 404)

        # ── User prefs (GET) ─────────────────────────────────────────
        elif path == '/api/prefs':
            try:
                userdata_dir, _ = _get_dirs()
                prefs = _load_prefs(userdata_dir)
                self._json({'ok': True, 'prefs': prefs})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})

        # ── Version ──────────────────────────────────────────────────
        elif path == '/api/version':
            try:
                vf = _resource_path('VERSION.txt')
                ver = vf.read_text('utf-8').strip() if vf.exists() else '1.0.0'
                self._json({'ok': True, 'version': ver})
            except Exception:
                self._json({'ok': True, 'version': '1.0.0'})

        # Recovery history stays inside Skript's private application-data
        # folder. Only opaque IDs are accepted by the restore endpoint.
        elif path == '/api/recovery/list':
            try:
                userdata_dir, scripts_dir = _get_dirs()
                self._json({'ok': True, 'entries': _recovery_entries(userdata_dir, scripts_dir)})
            except Exception as exc:
                self._json({'ok': False, 'error': str(exc)})

        # Privacy-safe support facts: no project content, titles, recent paths,
        # usernames, or environment variables are included.
        elif path == '/api/diagnostics':
            try:
                userdata_dir, scripts_dir = _get_dirs()
                vf = _resource_path('VERSION.txt')
                version = vf.read_text('utf-8').strip() if vf.exists() else 'unknown'
                self._json({'ok': True, 'diagnostics': {
                    'appVersion': version,
                    'pythonVersion': '.'.join(map(str, sys.version_info[:3])),
                    'operatingSystem': 'Windows' if sys.platform == 'win32' else sys.platform,
                    'serviceAvailable': True,
                    'recoveryCopies': len(_recovery_entries(userdata_dir, scripts_dir)),
                    'applicationDataWritable': os.access(userdata_dir, os.W_OK),
                    'projectsFolderWritable': os.access(scripts_dir, os.W_OK),
                    'capturedAt': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                }})
            except Exception as exc:
                self._json({'ok': False, 'error': str(exc)})

        # ── Serve collaborator viewer page ───────────────────────────
        elif path == '/collab':
            session_id = qs.get('session', [''])[0]
            if not session_id or session_id not in _COLLAB_SESSIONS:
                self._bytes(b'<h2>Invalid or expired collaboration link.</h2>', 'text/html')
            else:
                cport = _COLLAB_PORT_VAL or 0
                mport = _MAIN_PORT_VAL or 0
                html  = _collab_html(session_id, cport, mport).encode('utf-8')
                self._bytes(html, 'text/html; charset=utf-8')

        # ── Return local IPs for invite link construction ────────────
        elif path == '/api/collab/ips':
            self._json({
                'ok': True,
                'ips': ['127.0.0.1'] if _COLLAB_LOCAL_ONLY else _get_local_ips(),
                'collab_port': _COLLAB_PORT_VAL,
                'local_only': _COLLAB_LOCAL_ONLY,
            })

        # ── Public collaboration status probe (no script payload) ─────
        elif path == '/api/collab/status':
            session_id = qs.get('session', [''])[0]
            sess = _COLLAB_SESSIONS.get(session_id)
            if not sess or not sess.get('active'):
                self._json({'ok': False, 'error': 'Session not found or ended'})
            else:
                dur = sess.get('duration_secs', 0)
                if dur and (time.time() - sess.get('created', 0)) > dur:
                    self._json({'ok': False, 'expired': True,
                                'error': 'This collaboration link has expired'})
                else:
                    ip = _request_ip(self)
                    if ip in sess.get('revoked_ips', []):
                        self._json({'ok': False, 'error': 'Access denied'})
                    else:
                        self._json({
                            'ok': True,
                            'has_password': bool(sess.get('edit_pw_hash')),
                            'requires_view_pw': bool(sess.get('view_pw_hash')),
                        })

        # ── Get script for a session (collaborator) ──────────────────
        elif path == '/api/collab/script':
            session_id = qs.get('session', [''])[0]
            sess = _COLLAB_SESSIONS.get(session_id)
            if not sess or not sess.get('active'):
                self._json({'ok': False, 'error': 'Session not found or ended'})
            else:
                # Expiry check
                dur = sess.get('duration_secs', 0)
                if dur and (time.time() - sess.get('created', 0)) > dur:
                    self._json({'ok': False, 'expired': True,
                                'error': 'This collaboration link has expired'})
                else:
                    ip = _request_ip(self)
                    if ip in sess.get('revoked_ips', []):
                        self._json({'ok': False, 'error': 'Access denied'})
                    elif not _check_collab_access(self, sess):
                        self._json({'ok': False, 'auth_required': True,
                                    'error': 'Authentication required'})
                    else:
                        # Script is always password-protected now
                        self._json({'ok': True, 'script': sess['script'],
                                    'revision': sess.get('revision', 1),
                                    'conflicts': sess.get('conflicts', [])[-20:],
                                    'has_password': bool(sess.get('edit_pw_hash')),
                                    'requires_view_pw': bool(sess.get('view_pw_hash'))})

        # ── Get notes for a session ──────────────────────────────────
        elif path == '/api/collab/notes':
            session_id = qs.get('session', [''])[0]
            sess = _COLLAB_SESSIONS.get(session_id)
            if not sess:
                self._json({'ok': False, 'error': 'Session not found'})
            elif not _check_collab_access(self, sess):
                self._json({'ok': False, 'auth_required': True,
                            'error': 'Authentication required'})
            else:
                self._json(_collab_public_state(sess))

        # Authenticated server-sent event stream. Tokens remain in request headers.
        elif path == '/api/collab/events':
            session_id = qs.get('session', [''])[0]
            sess = _COLLAB_SESSIONS.get(session_id)
            if not sess or not sess.get('active'):
                self._json({'ok': False, 'error': 'Session not found or ended'}, 404)
            elif not _check_collab_access(self, sess):
                self._json({'ok': False, 'auth_required': True,
                            'error': 'Authentication required'}, 403)
            else:
                try:
                    since = max(0, int(qs.get('since', ['0'])[0]))
                except ValueError:
                    since = 0
                self.send_response(200)
                self.send_header('Content-Type', 'text/event-stream; charset=utf-8')
                self.send_header('Cache-Control', 'no-store, no-transform')
                self.send_header('Connection', 'close')
                self.send_header('X-Accel-Buffering', 'no')
                self.send_header('X-Content-Type-Options', 'nosniff')
                self._cors()
                self.end_headers()
                deadline = time.time() + 25
                last_heartbeat = 0
                try:
                    # Every connection receives a current snapshot before deltas.
                    initial = json.dumps(_collab_public_state(sess), separators=(',', ':'))
                    self.wfile.write(f'event: state\ndata: {initial}\n\n'.encode('utf-8'))
                    self.wfile.flush()
                    while time.time() < deadline:
                        with _COLLAB_EVENT_CONDITION:
                            state = _COLLAB_EVENTS.setdefault(session_id, {'seq': 0, 'events': []})
                            pending = [event for event in state['events'] if event['id'] > since]
                            if not pending:
                                _COLLAB_EVENT_CONDITION.wait(timeout=3)
                                pending = [event for event in state['events'] if event['id'] > since]
                        for event in pending:
                            payload = json.dumps(event['data'], separators=(',', ':'))
                            frame = (f"id: {event['id']}\nevent: {event['event']}\n"
                                     f'data: {payload}\n\n')
                            self.wfile.write(frame.encode('utf-8'))
                            since = event['id']
                        if pending or time.time() - last_heartbeat >= 10:
                            if not pending:
                                self.wfile.write(b': keep-alive\n\n')
                            self.wfile.flush()
                            last_heartbeat = time.time()
                        if not sess.get('active'):
                            break
                except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
                    pass
                finally:
                    self.close_connection = True

        # ── Check recovery: did the previous session crash? ──────────
        elif path == '/api/check-recovery':
            try:
                userdata_dir, _ = _get_dirs()
                lp = userdata_dir / 'session.lock'
                rp = userdata_dir / 'recovery.recover'
                # A crash is: lock file still exists (session didn't exit cleanly)
                # AND a recovery snapshot was saved
                prior_session = lp.read_text('utf-8').strip() if lp.exists() else ''
                crashed = (bool(prior_session) and prior_session != _PROCESS_SESSION_ID
                           and (rp.exists() or _rolling_backup_path(rp, 1).exists()))
                if crashed:
                    content, recovery_data, recovered_from = _read_project_with_backups(rp)
                    self._json({'crashed': True, 'content': content,
                                'recoveredFrom': recovered_from})
                else:
                    self._json({'crashed': False})
            except Exception as e:
                self._json({'crashed': False, 'error': str(e)})

        else:
            body = b'ok'
            self.send_response(200)
            self.send_header('Content-Type', 'text/plain; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self._cors()
            self.end_headers()
            self.wfile.write(body)

    def do_POST(self):
        global _SESSION_ACTIVE, _PRESERVE_RECOVERY_ON_EXIT
        path = urlparse(self.path).path
        origin = self.headers.get('Origin', '')
        if path in _COLLAB_GUEST_ROUTES and origin and not _origin_allowed(origin):
            self._json({'ok': False, 'error': 'Origin not allowed'}, 403)
            return
        try:
            length = int(self.headers.get('Content-Length', 0))
        except ValueError:
            self._json({'ok': False, 'error': 'Invalid content length'}, 400)
            return
        collab_limits = {
            '/api/collab/auth': 16384,
            '/api/collab/ping': 16384,
            '/api/collab/note': 65536,
            '/api/collab/reply': 65536,
            '/api/collab/edit': 4 * 1024 * 1024,
            '/api/collab/update': 4 * 1024 * 1024,
            '/api/collab/create': 4 * 1024 * 1024,
        }
        limit = collab_limits.get(path)
        if limit is not None and (length < 0 or length > limit):
            self._json({'ok': False, 'error': 'Collaboration payload is too large'}, 413)
            return
        if path == '/api/import-word' and (length < 0 or length > 30 * 1024 * 1024):
            self._json({'ok': False, 'error': 'The Word document is too large to import'}, 413)
            return
        body = self.rfile.read(length) if length else b''
        userdata_dir, scripts_dir = _get_dirs()
        if _requires_api_token(path) and not _check_api_token(self):
            self._json({'ok': False, 'error': 'Unauthorized'}, 403)
            return

        # ── Window control (minimize / maximize / close) ─────────────
        if path == '/api/window':
            try:
                action = json.loads(body).get('action', '')
                _window_control(action)
                self._json({'ok': True})
            except Exception as ex:
                self._json({'ok': False, 'error': str(ex)})
            return

        # ── Save user profile ────────────────────────────────────────
        if path == '/api/save-profile':
            try:
                profile_path = userdata_dir / 'profile.json'
                profile_path.write_bytes(body)
                self._json({'ok': True, 'path': str(profile_path)})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Load user profile ────────────────────────────────────────
        if path == '/api/load-profile':
            try:
                profile_path = userdata_dir / 'profile.json'
                if profile_path.exists():
                    data = json.loads(profile_path.read_text('utf-8'))
                    self._json({'ok': True, 'profile': data})
                else:
                    self._json({'ok': False, 'notFound': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Save script (auto-save to scripts dir, no dialog) ────────
        if path == '/api/save-auto':
            try:
                data = json.loads(body)
                content = data.get('content', '')
                content, project = _validate_project_bytes(content)
                title   = data.get('title', 'Untitled')
                safe    = ''.join(c for c in title if c.isalnum() or c in ' -_').strip() or 'Untitled'
                requested_path = str(data.get('path') or '').strip()
                fpath = pathlib.Path(requested_path) if requested_path else scripts_dir / (safe + '.script')
                if fpath.suffix.lower() != '.script':
                    raise ValueError('Skript projects must use the .script extension')
                _atomic_write_bytes(fpath, content)
                # Update recent scripts list
                _update_recent(str(fpath), title, userdata_dir)
                self._json({'ok': True, 'path': str(fpath)})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Save script (native dialog) ──────────────────────────────
        if path == '/api/save':
            try:
                data    = json.loads(body)
                content = data.get('content', '')
                content, project = _validate_project_bytes(content)
                title   = data.get('title', 'Untitled')
                safe    = ''.join(c for c in title if c.isalnum() or c in ' -_').strip() or 'Untitled'
                fpath   = _open_file_dialog(
                    [('Skript', '*.script'), ('All', '*.*')],
                    'Save Script', save=True, initial_name=safe + '.script'
                )
                if fpath is False:
                    self._json({'ok': False, 'dialogUnavailable': True,
                                'error': 'Native save dialog is unavailable'}); return
                if not fpath:
                    self._json({'ok': False, 'cancelled': True}); return
                fpath = pathlib.Path(fpath)
                if fpath.suffix.lower() != '.script':
                    fpath = fpath.with_suffix('.script')
                _atomic_write_bytes(fpath, content)
                _update_recent(str(fpath), title, userdata_dir)
                self._json({'ok': True, 'path': str(fpath)})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Open script (native dialog) ──────────────────────────────
        if path == '/api/open':
            try:
                fpath = _open_file_dialog(
                    [('Skript', '*.script'), ('All', '*.*')],
                    'Open Script'
                )
                if fpath is False:
                    self._json({'ok': False, 'dialogUnavailable': True,
                                'error': 'Native open dialog is unavailable'}); return
                if not fpath:
                    self._json({'ok': False, 'cancelled': True}); return
                content, data, recovered_from = _read_project_with_backups(fpath)
                title   = data.get('title', pathlib.Path(fpath).stem)
                _update_recent(fpath, title, userdata_dir)
                self._json({'ok': True, 'content': content, 'path': fpath,
                            'recoveredFrom': recovered_from})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Import Word document (.docx / legacy .doc) ──────────────
        if path == '/api/import-word':
            try:
                data = json.loads(body)
                filename = pathlib.Path(str(data.get('filename') or 'Imported.docx')).name
                suffix = pathlib.Path(filename).suffix.lower()
                encoded = str(data.get('content') or '')
                payload = base64.b64decode(encoded, validate=True)
                if not payload:
                    raise ValueError('The selected Word document is empty')
                if len(payload) > 20 * 1024 * 1024:
                    raise ValueError('The Word document is larger than the 20 MB import limit')
                result = _import_word_bytes(payload, suffix, pathlib.Path(filename).stem)
                self._json({'ok': True, **result})
            except (ValueError, zipfile.BadZipFile, ET.ParseError) as exc:
                self._json({'ok': False, 'error': str(exc)}, 400)
            except Exception as exc:
                self._json({'ok': False, 'error': f'Word import failed: {exc}'}, 500)
            return

        # ── Pick folder (for Cloud Sync folder browser) ──────────────
        if path == '/api/pick-folder':
            try:
                folder = _open_folder_dialog('Select Backup Folder')
                if folder is False:
                    self._json({'ok': False, 'dialogUnavailable': True,
                                'error': 'Native folder dialog is unavailable'})
                    return
                if folder:
                    self._json({'ok': True, 'path': str(folder)})
                else:
                    self._json({'ok': False, 'cancelled': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── List recent scripts ──────────────────────────────────────
        if path == '/api/recent-scripts':
            try:
                recent = _load_recent(userdata_dir)
                self._json({'ok': True, 'scripts': recent})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Clear recent scripts list ──────────────────────────────────────
        if path == '/api/clear-recent':
            try:
                rp = _recent_path(userdata_dir)
                rp.write_text('[]', encoding='utf-8')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Save user prefs ───────────────────────────────────────────
        if path == '/api/prefs':
            try:
                data = json.loads(body)
                _save_prefs(data.get('prefs', {}), userdata_dir)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Load a specific script by path ───────────────────────────
        if path == '/api/load-script':
            try:
                data  = json.loads(body)
                fpath = pathlib.Path(data.get('path', ''))
                content, project, recovered_from = _read_project_with_backups(fpath)
                self._json({'ok': True, 'content': content, 'path': str(fpath),
                            'recoveredFrom': recovered_from})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Autosave ─────────────────────────────────────────────────
        if path == '/api/autosave':
            try:
                ap = userdata_dir / 'autosave.json'
                _validate_project_bytes(body)
                _atomic_write_bytes(ap, body)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Get app data paths (for display in UI) ───────────────────
        if path == '/api/paths':
            ud, sd = _get_dirs()
            self._json({'userdata': str(ud), 'scripts': str(sd)})
            return

        # ── Heartbeat: JS sends project snapshot every 10s ─────────
        if path == '/api/heartbeat':
            try:
                userdata_dir, _ = _get_dirs()
                with _SESSION_STATE_LOCK:
                    if not _SESSION_ACTIVE:
                        self._json({'ok': True, 'ignored': True})
                        return
                    rp = userdata_dir / 'recovery.recover'
                    _validate_project_bytes(body)
                    _atomic_write_bytes(rp, body, backup_count=10)
                    _atomic_write_bytes(userdata_dir / 'session.lock', _PROCESS_SESSION_ID, backup_count=0)
                    history_dir = _recovery_history_dir(userdata_dir)
                    newest = max(history_dir.glob('*.recover'),
                                 key=lambda item: item.stat().st_mtime,
                                 default=None)
                    if newest is None or time.time() - newest.stat().st_mtime >= 300:
                        _archive_recovery_snapshot(userdata_dir, body, reason='automatic')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Clear recovery file (clean exit) ─────────────────────────
        if path == '/api/clear-recovery':
            try:
                userdata_dir, _ = _get_dirs()
                rp = userdata_dir / 'recovery.recover'
                _archive_recovery_snapshot(userdata_dir, reason='resolved')
                _remove_file_family(rp, backup_count=10)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        if path == '/api/start-session':
            try:
                userdata_dir, _ = _get_dirs()
                with _SESSION_STATE_LOCK:
                    _SESSION_ACTIVE = True
                    _atomic_write_bytes(userdata_dir / 'session.lock', _PROCESS_SESSION_ID, backup_count=0)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        if path == '/api/recovery/load':
            try:
                request = json.loads(body or b'{}')
                content = _load_recovery_entry(userdata_dir, scripts_dir, request.get('id'))
                self._json({'ok': True, 'content': content})
            except Exception as exc:
                self._json({'ok': False, 'error': str(exc)}, 404)
            return

        if path == '/api/recovery/archive-current':
            try:
                rp = userdata_dir / 'recovery.recover'
                archived = _archive_recovery_snapshot(userdata_dir, reason='kept-for-later')
                _remove_file_family(rp, backup_count=10)
                self._json({'ok': True, 'archived': bool(archived)})
            except Exception as exc:
                self._json({'ok': False, 'error': str(exc)})
            return

        # Shut down the local service only when the browser really closes.
        # Unsaved closes preserve both the latest snapshot and crash marker.
        if path == '/api/end-session':
            try:
                userdata_dir, _ = _get_dirs()
                preserve_recovery = self.headers.get(
                    'X-Skript-Preserve-Recovery', ''
                ).strip() == '1'
                with _SESSION_STATE_LOCK:
                    _SESSION_ACTIVE = False
                    lp = userdata_dir / 'session.lock'
                    rp = userdata_dir / 'recovery.recover'
                    if preserve_recovery:
                        # pagehide keepalive requests have a small browser
                        # payload limit.  An empty object means "keep the most
                        # recent heartbeat" for larger projects.
                        if body and body.strip() != b'{}':
                            _validate_project_bytes(body)
                            _atomic_write_bytes(rp, body, backup_count=10)
                        _atomic_write_bytes(lp, _PROCESS_SESSION_ID, backup_count=0)
                        try:
                            _archive_recovery_snapshot(
                                userdata_dir, reason='unsaved-window-close'
                            )
                        except Exception:
                            pass
                    else:
                        try:
                            _archive_recovery_snapshot(userdata_dir, reason='clean-close')
                        except Exception:
                            pass
                        _remove_file_family(rp, backup_count=10)
                        if lp.exists():
                            lp.unlink()
                    _PRESERVE_RECOVERY_ON_EXIT = preserve_recovery
                self._json({'ok': True, 'recoveryPreserved': preserve_recovery})
            except Exception as e:
                try:
                    self._json({'ok': False, 'error': str(e)})
                except OSError:
                    pass
            finally:
                # Set this even if the unloading browser disconnects before it
                # reads the response; the hidden service must still terminate.
                _APP_SHUTDOWN_EVENT.set()
            return

        # Match native window sizing to the app's actual Desktop/Touch mode.
        if path == '/api/window-layout':
            try:
                mode = json.loads(body).get('mode', 'desktop')
                if mode not in ('desktop', 'touch'):
                    raise ValueError('Unknown window layout mode')
                threading.Thread(
                    target=_force_centred_browser_window,
                    args=(_EDGE_PROC,),
                    kwargs={'timeout': 3.0, 'touch_mode': mode == 'touch'},
                    daemon=True,
                ).start()
                self._json({'ok': True, 'mode': mode})
            except Exception as ex:
                self._json({'ok': False, 'error': str(ex)})
            return

        # ── Create collaboration session ─────────────────────────────
        if path == '/api/collab/create':
            try:
                data        = json.loads(body)
                session_id  = secrets.token_urlsafe(16)   # URL-safe session token
                # Auto-generate viewer password if none provided (always required now)
                view_pw_raw = data.get('view_password', '') or _gen_viewer_password()
                edit_pw_raw = data.get('edit_password', '')
                # 64-char recovery key — owner must keep this safe
                recovery_key = secrets.token_hex(32)
                # Duration in seconds
                dur_map = {'24h': 86400, '7d': 604800, '30d': 2592000, 'indef': 0}
                dur_secs = dur_map.get(data.get('duration', '24h'), 86400)

                sess = {
                    'session_id':     session_id,
                    'title':          data.get('title', 'Untitled'),
                    'script':         data.get('script', {}),
                    'view_pw_hash':   _password_hash(view_pw_raw),
                    'edit_pw_hash':   _password_hash(edit_pw_raw) if edit_pw_raw else '',
                    'recovery_hash':  _password_hash(recovery_key),
                    'notes':          [],
                    'created':        time.time(),
                    'duration_secs':  dur_secs,
                    'active':         True,
                    # Security
                    'access_log':     [],           # { ip, ts, role, success }
                    'rate_limit':     {},           # ip -> { count, locked_until }
                    'revoked_ips':    [],           # permanently banned IPs
                    'max_note_len':   800,
                    'max_notes_per_ip': 20,
                    'viewers':          {},   # ip -> last_seen timestamp
                    'revision':         1,
                    'history':          {'1': data.get('script', {})},
                    'edit_log':         [],
                    'conflicts':        [],
                }
                _COLLAB_SESSIONS[session_id] = sess
                _save_collab_session(session_id)
                _ensure_collab_server()
                _collab_emit(sess, 'state')
                self._json({
                    'ok':            True,
                    'session_id':    session_id,
                    'collab_port':   _COLLAB_PORT_VAL,
                    'ips':           ['127.0.0.1'] if _COLLAB_LOCAL_ONLY else _get_local_ips(),
                    'local_only':    _COLLAB_LOCAL_ONLY,
                    'view_password': view_pw_raw,     # shown to owner once
                    'recovery_key':  recovery_key,     # shown to owner once — save it!
                    'has_edit_pw':   bool(edit_pw_raw),
                })
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Update script in an active session ───────────────────────
        if path == '/api/collab/update':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                if sid in _COLLAB_SESSIONS:
                    sess = _COLLAB_SESSIONS[sid]
                    revision, script, conflicts = _collab_apply_edit(
                        sess, data.get('script', {}),
                        int(data.get('base_revision', sess.get('revision', 1))),
                        'Owner', 'owner'
                    )
                    self._json({'ok': True, 'revision': revision, 'script': script,
                                'conflicts': conflicts})
                else:
                    self._json({'ok': False, 'error': 'Session not found'})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Close / stop a session ───────────────────────────────────
        if path == '/api/collab/close':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                if sid in _COLLAB_SESSIONS:
                    _COLLAB_SESSIONS[sid]['active'] = False
                    _save_collab_session(sid)
                    _collab_emit(_COLLAB_SESSIONS[sid], 'closed')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Authenticate (collaborator entering password) ────────────
        if path == '/api/collab/auth':
            try:
                data    = json.loads(body)
                sid     = data.get('session', '')
                pw      = data.get('password', '')
                role    = data.get('role', 'view')
                sess    = _COLLAB_SESSIONS.get(sid)
                if not sess or not sess.get('active'):
                    self._json({'ok': False, 'error': 'Session not found or ended'}); return

                # ── Expiry check ──────────────────────────────────────
                dur = sess.get('duration_secs', 0)
                if dur and (time.time() - sess.get('created', 0)) > dur:
                    self._json({'ok': False, 'expired': True,
                                'error': 'This collaboration link has expired'}); return

                # ── IP extraction ─────────────────────────────────────
                ip = _request_ip(self)

                # ── Revoked IP check ──────────────────────────────────
                if ip in sess.get('revoked_ips', []):
                    self._json({'ok': False, 'error': 'Access denied'}); return

                # ── Rate limit check ──────────────────────────────────
                rl   = sess.setdefault('rate_limit', {})
                now  = time.time()
                info = rl.get(ip, {'count': 0, 'locked_until': 0})
                if info.get('locked_until', 0) > now:
                    wait = int(info['locked_until'] - now)
                    self._json({'ok': False, 'rate_limited': True,
                                'error': f'Too many attempts. Try again in {wait}s'}); return

                # ── Password verification ─────────────────────────────
                # Recovery key bypasses all passwords
                is_recovery = _password_verify(pw, sess.get('recovery_hash', ''))

                if role == 'edit':
                    ok = is_recovery or (
                        bool(sess.get('edit_pw_hash')) and
                        _password_verify(pw, sess['edit_pw_hash'])
                    )
                else:
                    ok = is_recovery or _password_verify(pw, sess.get('view_pw_hash', ''))

                # ── Log the attempt ───────────────────────────────────
                log_entry = {
                    'ip': ip, 'ts': now, 'role': role,
                    'success': ok, 'recovery': is_recovery
                }
                sess.setdefault('access_log', []).append(log_entry)
                # Keep last 200 entries
                if len(sess['access_log']) > 200:
                    sess['access_log'] = sess['access_log'][-200:]

                # ── Rate limit increment / reset ──────────────────────
                if ok:
                    rl[ip] = {'count': 0, 'locked_until': 0}
                else:
                    info['count'] = info.get('count', 0) + 1
                    if info['count'] >= 5:
                        info['locked_until'] = now + 900  # 15 min lockout
                    rl[ip] = info

                _save_collab_session(sid)
                if ok:
                    # Transparently strengthen sessions created by older versions.
                    hash_key = 'recovery_hash' if is_recovery else (
                        'edit_pw_hash' if role == 'edit' else 'view_pw_hash'
                    )
                    if not sess.get(hash_key, '').startswith('pbkdf2_sha256$'):
                        sess[hash_key] = _password_hash(pw)
                    access_token = _new_collab_access(
                        sess, 'edit' if role == 'edit' else 'view', ip
                    )
                    _save_collab_session(sid)
                    self._json({'ok': True, 'edit': role == 'edit',
                                'recovery': is_recovery,
                                'access_token': access_token})
                else:
                    attempts_left = max(0, 5 - info.get('count', 0))
                    self._json({'ok': False,
                                'attempts_left': attempts_left,
                                'error': f'Incorrect password ({attempts_left} attempts remaining)'})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Collaborator submits live edits ──────────────────────────
        if path == '/api/collab/edit':
            try:
                data = json.loads(body)
                sid = data.get('session', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess or not sess.get('active'):
                    self._json({'ok': False, 'error': 'Session not found'}); return
                if _collab_access_role(self, sess) != 'edit':
                    self._json({'ok': False, 'error': 'Editor access required'}); return
                author = str(data.get('author') or 'Editor')[:80]
                revision, script, conflicts = _collab_apply_edit(
                    sess, data.get('script', {}), int(data.get('base_revision', 0)),
                    author, 'edit'
                )
                self._json({'ok': True, 'revision': revision, 'script': script,
                            'conflicts': conflicts})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Collaborator posts a note ────────────────────────────────
        if path == '/api/collab/note':
            try:
                data = json.loads(body)
                sid  = data.get('session', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess or not sess.get('active'):
                    self._json({'ok': False, 'error': 'Session not found'}); return
                if not _check_collab_access(self, sess):
                    self._json({'ok': False, 'auth_required': True,
                                'error': 'Authentication required'}); return

                # Expiry
                dur = sess.get('duration_secs', 0)
                if dur and (time.time() - sess.get('created', 0)) > dur:
                    self._json({'ok': False, 'expired': True}); return

                ip = _request_ip(self)
                if ip in sess.get('revoked_ips', []):
                    self._json({'ok': False, 'error': 'Access denied'}); return

                # Per-IP note throttle
                ip_notes = sum(1 for n in sess.get('notes', []) if n.get('ip') == ip)
                if ip_notes >= sess.get('max_notes_per_ip', 20):
                    self._json({'ok': False, 'error': 'Note limit reached'}); return

                note = {
                    'id':        str(uuid.uuid4())[:8],
                    'line_idx':  int(data.get('line_idx', 0)),
                    'line_text': str(data.get('line_text', ''))[:120],
                    'author':    str(data.get('author', 'Anonymous'))[:40],
                    'text':      str(data.get('text', ''))[:sess.get('max_note_len', 800)],
                    'category':  str(data.get('category', ''))[:30],
                    'replies':   [],
                    'ts':        time.time(),
                    'resolved':  False,
                    'ip':        ip,
                }
                sess.setdefault('notes', []).append(note)
                _save_collab_session(sid)
                _collab_emit(sess, 'notes')
                self._json({'ok': True, 'note_id': note['id']})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Owner resolves/deletes a note ────────────────────────────
        if path == '/api/collab/resolve':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                nid  = data.get('note_id', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if sess:
                    for n in sess.get('notes', []):
                        if n['id'] == nid:
                            n['resolved'] = True; break
                    _save_collab_session(sid)
                    _collab_emit(sess, 'notes')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Reply to a note ─────────────────────────────────────────
        if path == '/api/collab/reply':
            try:
                data = json.loads(body)
                sid  = data.get('session', '')
                nid  = data.get('note_id', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess or not sess.get('active'):
                    self._json({'ok': False, 'error': 'Session not found'}); return
                if not _check_collab_access(self, sess):
                    self._json({'ok': False, 'auth_required': True,
                                'error': 'Authentication required'}); return
                ip = _request_ip(self)
                if ip in sess.get('revoked_ips', []):
                    self._json({'ok': False, 'error': 'Access denied'}); return
                for n in sess.get('notes', []):
                    if n['id'] == nid:
                        reply = {
                            'id':     str(uuid.uuid4())[:8],
                            'author': str(data.get('author', 'Anonymous'))[:40],
                            'text':   str(data.get('text', ''))[:400],
                            'ts':     time.time(),
                            'ip':     ip,
                        }
                        n.setdefault('replies', []).append(reply)
                        _save_collab_session(sid)
                        _collab_emit(sess, 'notes')
                        self._json({'ok': True}); return
                self._json({'ok': False, 'error': 'Note not found'})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Viewer ping (presence tracking) ──────────────────────────
        if path == '/api/collab/ping':
            try:
                data = json.loads(body)
                sid  = data.get('session', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if sess and sess.get('active'):
                    if not _check_collab_access(self, sess):
                        self._json({'ok': False, 'auth_required': True}); return
                    ip = _request_ip(self)
                    role = _collab_access_role(self, sess) or 'view'
                    client_id = str(data.get('client_id') or ip)[:100]
                    sess.setdefault('viewers', {})[client_id] = {
                        'seen': time.time(), 'name': str(data.get('name') or 'Viewer')[:80],
                        'role': role, 'client_id': client_id, 'ip': ip,
                        'color': str(data.get('color') or '')[:20],
                    }
                    _collab_emit(sess, 'presence')
                    self._json({'ok': True, 'revision': sess.get('revision', 1)})
                else:
                    self._json({'ok': False})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

                # ── Get access log for a session ─────────────────────────────
        if path == '/api/collab/access-log':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess:
                    self._json({'ok': False, 'error': 'Session not found'}); return
                # Return log newest-first, plus rate_limit status and revoked IPs
                log  = list(reversed(sess.get('access_log', [])))[:100]
                self._json({
                    'ok':          True,
                    'log':         log,
                    'rate_limits': sess.get('rate_limit', {}),
                    'revoked_ips': sess.get('revoked_ips', []),
                    'note_count':  len(sess.get('notes', [])),
                    'created':     sess.get('created', 0),
                    'duration_secs': sess.get('duration_secs', 0),
                })
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Revoke an IP address ──────────────────────────────────────
        if path == '/api/collab/revoke-ip':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                ip   = data.get('ip', '').strip()
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess:
                    self._json({'ok': False, 'error': 'Session not found'}); return
                revoked = sess.setdefault('revoked_ips', [])
                if ip and ip not in revoked:
                    revoked.append(ip)
                _save_collab_session(sid)
                _collab_emit(sess, 'presence')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Unrevoke an IP ────────────────────────────────────────────
        if path == '/api/collab/unrevoke-ip':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                ip   = data.get('ip', '').strip()
                sess = _COLLAB_SESSIONS.get(sid)
                if sess:
                    sess['revoked_ips'] = [r for r in sess.get('revoked_ips', []) if r != ip]
                    # Also clear rate limit for this IP
                    sess.get('rate_limit', {}).pop(ip, None)
                    _save_collab_session(sid)
                    _collab_emit(sess, 'presence')
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Update session settings ───────────────────────────────────
        if path == '/api/collab/update-settings':
            try:
                data = json.loads(body)
                sid  = data.get('session_id', '')
                sess = _COLLAB_SESSIONS.get(sid)
                if not sess:
                    self._json({'ok': False, 'error': 'Session not found'}); return
                # Allow updating duration
                if 'duration' in data:
                    dur_map = {'24h': 86400, '7d': 604800, '30d': 2592000, 'indef': 0}
                    sess['duration_secs'] = dur_map.get(data['duration'], sess['duration_secs'])
                _save_collab_session(sid)
                self._json({'ok': True})
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return

        # ── Export to PDF (headless Edge/Chrome render) ──────────────────
        elif path == '/api/export-pdf':
            try:
                import tempfile
                data       = json.loads(body)
                title      = data.get('title', 'Untitled')
                cover      = data.get('cover', {})
                lines      = data.get('lines', [])
                layout     = data.get('layout') if data.get('layoutVersion') == 1 else None
                fmt        = data.get('format', 'film')
                inc_cover  = data.get('includeCover', True)
                inc_script = data.get('includeScript', True)
                open_pdf   = data.get('openPdf', True)

                html_src   = _build_pdf_html(title, cover, lines, fmt, inc_cover, inc_script, layout)

                tmp_dir    = pathlib.Path(tempfile.gettempdir()) / 'Skript'
                tmp_dir.mkdir(exist_ok=True)
                safe       = ''.join(c for c in title if c.isalnum() or c in ' -_').strip() or 'Script'
                html_path  = tmp_dir / f'{safe}_print.html'
                pdf_path   = tmp_dir / f'{safe}.pdf'
                profile_dir = tmp_dir / f'{safe}_pdf_profile_{uuid.uuid4().hex}'
                html_path.write_text(html_src, encoding='utf-8')
                try:
                    pdf_path.unlink(missing_ok=True)
                except TypeError:  # Python 3.7 compatibility
                    if pdf_path.exists():
                        pdf_path.unlink()

                if getattr(sys, 'frozen', False):
                    pdf_path.write_bytes(_build_basic_pdf_bytes(title, cover, lines, fmt, inc_cover, inc_script, layout))
                    rendered = pdf_path.exists() and pdf_path.stat().st_size > 500
                    if rendered:
                        if sys.platform == 'win32' and open_pdf:
                            os.startfile(str(pdf_path))
                        self._json({'ok': True, 'path': str(pdf_path)})
                    else:
                        self._json({'ok': False, 'error': 'pdf_fallback_failed'})
                    return

                browser_paths = [
                    r'C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe',
                    r'C:\Program Files\Microsoft\Edge\Application\msedge.exe',
                    'msedge',
                    r'C:\Program Files\Google\Chrome\Application\chrome.exe',
                    r'C:\Program Files (x86)\Google\Chrome\Application\chrome.exe',
                    'google-chrome-stable', 'google-chrome',
                ]
                rendered = False
                for ep in browser_paths:
                    try:
                        si = None; cf = 0
                        if sys.platform == 'win32':
                            si = subprocess.STARTUPINFO()
                            si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                            si.wShowWindow = 0
                            cf = subprocess.CREATE_NO_WINDOW
                        file_url = 'file:///' + str(html_path).replace('\\', '/')
                        subprocess.run([
                            ep,
                            '--headless=new',
                            f'--print-to-pdf={pdf_path}',
                            f'--user-data-dir={profile_dir}',
                            '--no-pdf-header-footer',
                            '--print-to-pdf-no-header',
                            '--disable-extensions',
                            '--no-first-run',
                            '--disable-background-networking',
                            '--disable-gpu',
                            '--run-all-compositor-stages-before-draw',
                            '--disable-software-rasterizer',
                            file_url,
                        ], startupinfo=si, creationflags=cf,
                           capture_output=True, timeout=30)
                        if pdf_path.exists() and pdf_path.stat().st_size > 500:
                            rendered = True
                            break
                    except (FileNotFoundError, OSError, subprocess.TimeoutExpired):
                        continue

                if rendered:
                    if sys.platform == 'win32' and open_pdf:
                        os.startfile(str(pdf_path))
                    self._json({'ok': True, 'path': str(pdf_path)})
                else:
                    self._json({'ok': False, 'error': 'edge_not_found'})
                try:
                    shutil.rmtree(profile_dir, ignore_errors=True)
                except Exception:
                    pass
            except Exception as e:
                self._json({'ok': False, 'error': str(e)})
            return


        # ── Molly AI proxy ───────────────────────────────────────────
        if path == '/api/molly':
            try:
                import urllib.request as _ur, ssl as _ssl
                payload = json.loads(body)
                userdata_dir2, _ = _get_dirs()
                prefs2 = _load_prefs(userdata_dir2)
                api_key = prefs2.get('mollyApiKey', '')
                if not api_key:
                    self._json({'ok': False, 'error': 'no_key',
                                'message': 'No API key set. Add your Anthropic API key in Options → Molly AI.'}, 401)
                    return
                req_body = json.dumps(payload).encode('utf-8')
                req = _ur.Request(
                    'https://api.anthropic.com/v1/messages',
                    data=req_body,
                    headers={
                        'Content-Type': 'application/json',
                        'x-api-key': api_key,
                        'anthropic-version': '2023-06-01',
                    },
                    method='POST'
                )
                ctx = _ssl.create_default_context()
                with _ur.urlopen(req, context=ctx, timeout=60) as resp:
                    resp_body = resp.read()
                data2 = json.loads(resp_body)
                self._json({'ok': True, 'data': data2})
            except Exception as ex:
                err_str = str(ex)
                # Try to extract Anthropic error message
                try:
                    import re as _re
                    m = _re.search(r'\{.*\}', err_str, _re.DOTALL)
                    if m:
                        anthropic_err = json.loads(m.group(0))
                        err_str = anthropic_err.get('error', {}).get('message', err_str)
                except Exception:
                    pass
                self._json({'ok': False, 'error': err_str}, 500)
            return


        self.send_response(404)
        self.send_header('Content-Length', '0')
        self.end_headers()


def _pdf_escape_text(value):
    return str(value or '').replace('\\', '\\\\').replace('(', '\\(').replace(')', '\\)')


def _build_basic_pdf_bytes(title, cover, lines, fmt, inc_cover, inc_script, layout=None):
    """Dependency-free A4 PDF renderer used by the packaged application."""
    import textwrap

    page_w, page_h = 595.28, 841.89
    left_default, top, bottom = 108, 770, 72
    leading = 12
    source_lines = layout if isinstance(layout, list) and layout else lines
    pages, ops = [], []
    y = top

    def add_at(text, x, at_y, bold=False, size=12):
        text = str(text or '').strip()
        if not text:
            return
        font = 'F2' if bold else 'F1'
        ops.append(f'BT /{font} {size} Tf {x:.2f} {at_y:.2f} Td ({_pdf_escape_text(text)}) Tj ET')

    def new_page():
        nonlocal ops, y
        pages.append(ops)
        ops = []
        y = top

    def draw(text, x=left_default, bold=False, size=12, cols=58):
        nonlocal y
        text = str(text or '').strip()
        wrapped = textwrap.wrap(text, width=cols, break_long_words=True, break_on_hyphens=False) if text else ['']
        for row in wrapped:
            if y < bottom:
                new_page()
            if row:
                add_at(row, x, y, bold, size)
            y -= leading

    if inc_cover:
        cv = cover or {}
        cover_title = cv.get('title') or title or 'Untitled'
        title_rows = textwrap.wrap(str(cover_title).upper(), 36, break_long_words=True) or ['UNTITLED']
        title_size = max(10, 18 - max(0, len(title_rows) - 2) * 2)
        title_y = 625
        for row in title_rows:
            add_at(row, max(72, (page_w - len(row) * title_size * .6) / 2), title_y, True, title_size)
            title_y -= title_size + 4
        author = cv.get('author') or cv.get('writtenBy') or ''
        if author:
            add_at('Written by', 250, title_y - 20, False, 12)
            title_y -= 38
            for row in textwrap.wrap(str(author), 52, break_long_words=True) or ['']:
                add_at(row, max(72, (page_w - len(row) * 7.2) / 2), title_y, False, 12)
                title_y -= 14
        based_on = cv.get('basedOn') or ''
        if based_on:
            title_y -= 8
            for row in textwrap.wrap(str(based_on), 52, break_long_words=True) or ['']:
                add_at(row, max(72, (page_w - len(row) * 7.2) / 2), title_y, False, 12)
                title_y -= 14
        draft_line = ' | '.join(filter(None, [str(cv.get('draft') or ''), str(cv.get('date') or '')]))
        if draft_line:
            title_y -= 8
            for row in textwrap.wrap(draft_line, 62, break_long_words=True) or ['']:
                add_at(row, max(72, (page_w - len(row) * 6) / 2), title_y, False, 10)
                title_y -= 12

        contact = [str(cv.get(f'contact{i}') or '') for i in range(1, 5)]
        rights = [str(cv.get(f'rights{i}') or '') for i in range(1, 3)]
        contact = [row for row in contact if row]
        rights = [row for row in rights if row]

        def fit_cover_rows(values, width, start_size=9):
            size = start_size
            while True:
                cols = max(12, int(width / (size * .6)))
                rows = []
                for value in values:
                    rows.extend(textwrap.wrap(value, cols, break_long_words=True) or [''])
                line_height = size * 1.2
                if size <= 5 or len(rows) * line_height <= 105:
                    return rows, size, line_height
                size -= 1

        contact_rows, contact_size, contact_leading = fit_cover_rows(contact, 210)
        rights_rows, rights_size, rights_leading = fit_cover_rows(rights, 125)
        contact_height = len(contact_rows) * contact_leading
        rights_height = len(rights_rows) * rights_leading
        heading_y = 75 + max(contact_height, rights_height) + 14
        if contact:
            add_at('CONTACT', 108, heading_y, True, 9)
            row_y = heading_y - 13
            for row in contact_rows:
                add_at(row, 108, row_y, False, contact_size)
                row_y -= contact_leading
        if rights:
            add_at('RIGHTS', 380, heading_y, True, 9)
            row_y = heading_y - 13
            for row in rights_rows:
                add_at(row, 380, row_y, False, rights_size)
                row_y -= rights_leading
        if inc_script:
            new_page()

    if inc_script:
        for item in source_lines or []:
            typ = str(item.get('type', 'action') if isinstance(item, dict) else 'action')
            text = item.get('text', '') if isinstance(item, dict) else str(item)
            is_play = fmt == 'play'
            if typ == 'scene':
                y -= 12 if is_play else 6
                draw(text.upper(), left_default, True, cols=58)
            elif typ == 'character':
                y -= 6
                draw(text.upper(), 252 if is_play else 252, True, cols=32)
            elif typ == 'dialogue':
                draw(text, 180, cols=35)
            elif typ == 'parenthetical':
                draw(text, 216 if not is_play else 180, cols=28 if not is_play else 35)
            elif typ == 'transition':
                if not is_play:
                    y -= 6
                    draw(text.upper(), left_default, True, cols=58)
            elif typ == 'act':
                if is_play and ops and y != top:
                    new_page()
                y -= 12
                draw(text.upper(), left_default if is_play else 250, True, cols=45)
                y -= 6
            elif typ in ('act-break', 'cold-open', 'tag'):
                y -= 12
                draw(text.upper(), 250, True, cols=35)
                y -= 6
            elif typ == 'notes':
                continue
            elif is_play and typ in ('action', 'stage-direction'):
                direction = str(text or '').strip()
                if direction and not (direction.startswith('(') and direction.endswith(')')):
                    direction = f'({direction})'
                draw(direction, left_default, cols=58)
                y -= 6
            else:
                draw(text, left_default, cols=58)
    if ops or not pages:
        pages.append(ops)

    objects = []

    def add_obj(body):
        objects.append(body)
        return len(objects)

    catalog_id = add_obj('<< /Type /Catalog /Pages 2 0 R >>')
    pages_id = add_obj('')
    font_regular_id = add_obj('<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>')
    font_bold_id = add_obj('<< /Type /Font /Subtype /Type1 /BaseFont /Courier-Bold >>')
    page_ids = []
    for page_ops in pages:
        stream = '\n'.join(page_ops).encode('latin-1', errors='replace')
        content_id = add_obj(f'<< /Length {len(stream)} >>\nstream\n' + stream.decode('latin-1') + '\nendstream')
        page_id = add_obj(
            f'<< /Type /Page /Parent {pages_id} 0 R /MediaBox [0 0 {page_w} {page_h}] '
            f'/Resources << /Font << /F1 {font_regular_id} 0 R /F2 {font_bold_id} 0 R >> >> '
            f'/Contents {content_id} 0 R >>'
        )
        page_ids.append(page_id)
    objects[pages_id - 1] = f'<< /Type /Pages /Kids [{" ".join(f"{pid} 0 R" for pid in page_ids)}] /Count {len(page_ids)} >>'

    out = bytearray(b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n')
    offsets = [0]
    for i, body in enumerate(objects, start=1):
        offsets.append(len(out))
        out.extend(f'{i} 0 obj\n{body}\nendobj\n'.encode('latin-1', errors='replace'))
    xref = len(out)
    out.extend(f'xref\n0 {len(objects)+1}\n0000000000 65535 f \n'.encode('ascii'))
    for offset in offsets[1:]:
        out.extend(f'{offset:010d} 00000 n \n'.encode('ascii'))
    out.extend(
        f'trailer\n<< /Size {len(objects)+1} /Root {catalog_id} 0 R >>\nstartxref\n{xref}\n%%EOF\n'.encode('ascii')
    )
    return bytes(out)


def _build_pdf_html(title, cover, lines, fmt, inc_cover, inc_script, layout=None):
    """Build a standalone HTML for Edge --print-to-pdf.

    BBC A4 layout | 1.5in left, 0.75in right, 1in top/bottom margins
    All indents are relative to the text-area left edge (inside @page margin).
    Courier New 12pt, line-height 1.0 (= 12pt = ~4.23 mm = ~0.167in).
    A4 printable height  ≈ 297 - 25.4 - 25.4 = 246 mm  ≈ 58 lines.
    We use 58 single-spaced lines per page.

    (MORE) / (CONT'D) are injected in Python so they appear even when
    Edge headless ignores page-break-inside:avoid on tall speech blocks.
    """
    import math, html as _h

    def esc(s): return _h.escape(str(s or ''))

    # ── Layout constants ──────────────────────────────────────────────
    # Courier New is a fixed-pitch font: exactly 0.6em per character at 12pt
    # = 7.2pt per char.  A4 text width (8.27 - 1.5 - 1.0 = 5.77in = 415pt)
    # → 415 / 7.2 ≈ 57 chars.  Dialogue column (5.77 - 1.0 - 1.3 = 3.47in
    # = 250pt) → 34 chars.
    LPP          = 58       # A4 body between 1in top/bottom margins
    ACT_COLS     = 60       # BBC action / scene column on A4
    DLG_COLS     = 35       # dialogue chars per line (3.5in column)
    PAR_COLS     = 25       # parenthetical column from 3.0in to 5.5in

    def _wrap_lines(text, cols):
        """Count wrapped lines for a given column width."""
        if not text:
            return 1
        words  = text.split()
        count  = 1
        cur    = 0
        for w in words:
            if cur + len(w) + (1 if cur else 0) <= cols:
                cur += len(w) + (1 if cur else 0)
            else:
                count += 1
                cur    = len(w)
        return count

    def _height(ltype, text):
        """Estimated line units (12pt lines) this element occupies on the page."""
        t = text or ''
        if ltype == 'scene':
            return 2 + _wrap_lines(t, ACT_COLS)       # triple-spaced from prior text
        if ltype == 'action':
            return _wrap_lines(t, ACT_COLS) + 1        # text + gap
        if ltype == 'character':
            return 2                                    # top gap + text
        if ltype == 'dialogue':
            return _wrap_lines(t, DLG_COLS)
        if ltype == 'parenthetical':
            return _wrap_lines(t, PAR_COLS)
        if ltype == 'transition':
            return 3
        return 1

    # ── Inject (MORE) / (CONT'D) at page breaks ──────────────────────
    def _inject(raw):
        out      = []
        pos      = 0
        last_ch  = ''

        for line in raw:
            lt   = line.get('type', 'action')
            txt  = line.get('text', '')
            h    = _height(lt, txt)

            if lt == 'character':
                import re
                last_ch = re.sub(r"\s*\(CONT'?D\)\s*$", '', txt, flags=re.I).strip()

            # Would this element overflow the current page?
            if pos > 0 and pos + h > LPP:

                # Dialogue split → emit partial, (MORE), page break, (CONT'D)
                if lt == 'dialogue' and last_ch:
                    room = LPP - pos
                    if room >= 2:
                        # Fit as many words as possible in the remaining room
                        words  = txt.split()
                        filled = []
                        col    = 0
                        ln     = 0
                        for w in words:
                            if col + len(w) + (1 if col else 0) <= DLG_COLS:
                                filled.append(w)
                                col += len(w) + (1 if col else 0)
                            else:
                                ln  += 1
                                if ln >= room - 1:
                                    break
                                filled.append(w)
                                col = len(w)
                        rest = txt[len(' '.join(filled)):].strip()
                        if filled:
                            out.append({'type': 'dialogue',   'text': ' '.join(filled)})
                        out.append(    {'type': '_more',      'text': '(MORE)'})
                        out.append(    {'type': '_break',     'text': ''})
                        out.append(    {'type': 'character',  'text': f"{last_ch} (CONT'D)"})
                        pos = 2
                        if rest:
                            out.append({'type': 'dialogue',   'text': rest})
                            pos += _height('dialogue', rest)
                        continue
                    else:
                        # No room at all — just break
                        out.append({'type': '_break', 'text': ''})
                        pos = 0

                # Character cue near page bottom — push to next page
                elif lt == 'character' and pos + h + 2 > LPP:
                    out.append({'type': '_break', 'text': ''})
                    pos = 0

                # Scene / action near page bottom
                elif lt in ('scene', 'action') and pos + h > LPP:
                    out.append({'type': '_break', 'text': ''})
                    pos = 0

            out.append(line)
            pos += h
            if pos >= LPP:
                pos = 0

        return out

    # ── CSS ───────────────────────────────────────────────────────────
    CSS = r"""
    @page {
      size: A4 portrait;
      /* WGA-style margins on A4 (210mm × 297mm):
         Left 1.5in gutter (binding), all others 1in
         Text area = 8.27 - 1.5 - 1.0 = 5.77in wide           */
      margin: 1in 0.75in 1in 1.5in;
    }
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    html, body {
      font-family: 'Courier New', Courier, monospace;
      font-size: 12pt;
      line-height: 1.0;   /* 1 line = 12pt */
      color: #000;
      background: #fff !important;
      -webkit-print-color-adjust: exact;
      print-color-adjust: exact;
    }

    /* ── Cover ──────────────────────────────────────────────── */
    .cover-page {
      width: 100%;
      /* Deliberately below the 246.2mm printable area to avoid rounding spills. */
      height: 238mm;
      max-height: 238mm;
      page-break-after: always;
      break-after: page;
      page-break-inside: avoid;
      break-inside: avoid;
      overflow: hidden;
      display: block;
      position: relative;
      box-sizing: border-box;
    }
    /* Top zone: title, author, draft — vertically centred in upper 2/3 */
    .cv-top {
      position: absolute;
      inset: 0 0 42mm 0;
      min-height: 0;
      overflow: hidden;
      display: flex;
      flex-direction: column;
      align-items: center;
      justify-content: center;
      padding-top: 0.75in;
      padding-bottom: 0.25in;
    }
    .cv-title { font-size: 14pt; font-weight: bold; text-transform: uppercase;
                text-align: center; margin-bottom: 12pt; }
    .cv-based { font-size: 12pt; text-align: center; margin-bottom: 4pt; }
    .cv-author{ font-size: 12pt; text-align: center; margin-bottom: 4pt; }
    .cv-draft { font-size: 10pt; text-align: center; margin-top: 4pt; color: #444; }
    /* Bottom zone: contact + rights — pinned to page bottom, never overflows */
    .cv-bottom{
      position: absolute;
      left: 0;
      right: 0;
      bottom: 0;
      height: 38mm;
      max-height: 38mm;
      overflow: hidden;
      padding: 0.2in 0;
      border-top: 0.5pt solid #ccc;
      margin: 0;
      display: grid;
      grid-template-columns: minmax(0, 1fr) minmax(0, 1fr);
      column-gap: 0.3in;
      page-break-inside: avoid;
      break-inside: avoid;
    }
    .cv-contact{ font-size: 8.5pt; line-height: 1.12; overflow-wrap: anywhere; }
    .cv-rights { font-size: 8.5pt; line-height: 1.12; text-align: right; overflow-wrap: anywhere; }

    /* ── Script body ─────────────────────────────────────────── */
    /* @page already provides margins; element indents are from text-area edge */
    .script-body { width: 100%; }

    /* Scene heading: keep glued to following action (page-break-after:avoid) */
    .el-scene {
      text-transform: uppercase;
      margin-top: 24pt;
      margin-bottom: 0;
      page-break-after: avoid;
      page-break-inside: avoid;
    }
    .el-scene + .el-action { margin-top: 12pt; }

    /* Subheading — inline scene continuation, same style but smaller top gap */
    .el-subheading {
      text-transform: uppercase;
      font-weight: bold;
      margin-top: 12pt;
      margin-bottom: 0;
      page-break-after: avoid;
    }

    /* Action: orphan/widow control; short blocks avoid breaking */
    .el-action {
      margin-top: 0;
      margin-bottom: 12pt;
      orphans: 3;
      widows: 3;
    }
    .el-action.no-break { page-break-inside: avoid; }

    /* Speech block wrapper — keeps char+dialogue together unless very long */
    .speech { margin-top: 12pt; page-break-inside: avoid; }
    .speech.long { page-break-inside: auto; }
    .speech + .el-action { margin-top: 12pt; }

    /* Character cue — 3.7in from page left (spec) = 2.2in from text-area left */
    .el-character {
      margin-left: 2.0in;
      margin-bottom: 0;
      text-transform: uppercase;
    }
    /* Dialogue — 2.5in from page left (1.0in from text-area left), 2.0in from page right */
    .el-dialogue {
      margin-left: 1.0in;
      margin-right: 1.25in;
      margin-bottom: 0;
      orphans: 2;
      widows: 2;
    }
    /* Parenthetical — 3.0in from page left = 1.5in from text-area left */
    .el-parenthetical {
      margin-left: 1.5in;
      margin-right: 2.0in;
      margin-bottom: 0;
      font-style: italic;
      color: #333;
    }
    /* (MORE) label — same indent as dialogue, right-aligned within column */
    .el-more {
      margin-left: 2.0in;
      text-align: left;
    }
    .el-contd {
      margin-left: 2.0in;
      text-transform: uppercase;
    }
    .page-num-stamp {
      display: block;
      font: 12pt/12pt 'Courier New', Courier, monospace;
      text-align: right;
      height: 12pt;
      margin: 0 0 12pt;
    }
    .el-transition {
      text-align: left;
      margin-top: 12pt;
      margin-bottom: 12pt;
      text-transform: uppercase;
    }
    /* Hard page break injected by Python */
    .pg-break {
      display: block;
      height: 0;
      break-after: page;
      page-break-after: always;
    }
    .page-leading { margin-top: 0 !important; }
    .explicit-layout .el-scene,
    .explicit-layout .el-action,
    .explicit-layout .speech,
    .explicit-layout .el-character {
      page-break-before: auto;
      page-break-after: auto;
      page-break-inside: auto;
      break-before: auto;
      break-after: auto;
      break-inside: auto;
    }
    .explicit-layout > .el-character { margin-top: 12pt; }
    .explicit-layout > .el-dialogue + .el-action,
    .explicit-layout > .dual-dialogue-wrap + .el-action { margin-top: 12pt; }
    .dual-dialogue-wrap {
      display: flex;
      align-items: flex-start;
      gap: 0.25in;
      width: 100%;
      margin-top: 12pt;
    }
    .dual-col { flex: 1; min-width: 0; }
    .dual-col .el-character { margin: 0; text-align: center; }
    .dual-col .el-dialogue { margin: 0; padding: 0 9pt; }
    .dual-col .el-parenthetical { margin: 0; padding: 0 15pt; }

    /* Misc elements */
    .el-act-break   { text-align: center; font-weight: bold;
                      text-transform: uppercase; margin: 24pt 0; }
    .el-cold-open   { text-align: center; font-weight: bold;
                      text-transform: uppercase; margin-bottom: 12pt; }
    .el-notes       { color: #555; font-size: 10pt; margin-bottom: 12pt;
                      padding-left: 0.25in; border-left: 2pt solid #aaa; }
    .el-act         { text-transform: uppercase; font-weight: bold;
                      margin-top: 24pt; margin-bottom: 12pt; }
    .el-stage-direction { margin-left: 1.0in; margin-right: 1.3in;
                          margin-bottom: 12pt; font-style: italic; }
    .el-tag         { text-align: center; text-transform: uppercase;
                      font-weight: bold; margin: 12pt 0; }

    /* BBC stage-play conventions: cue around the middle (not centred),
       dialogue directly beneath, and mixed-case bracketed directions. */
    .format-play .el-character {
      margin-left: 2.0in;
      text-align: left;
      font-weight: bold;
    }
    .format-play .el-dialogue {
      margin-left: 1.0in;
      margin-right: 1.25in;
    }
    .format-play .el-parenthetical {
      margin-left: 1.5in;
      margin-right: 1.5in;
      font-style: normal;
    }
    .format-play .el-action,
    .format-play .el-stage-direction {
      margin-left: 0;
      margin-right: 0;
      font-style: normal;
      text-transform: none;
    }
    .format-play .el-act {
      text-align: left;
      break-before: page;
      page-break-before: always;
    }
    .format-play .el-act:first-child {
      break-before: auto;
      page-break-before: auto;
    }
    .format-play .el-scene { text-align: left; }
    .format-play .el-transition { display: none; }
    """

    TYPE_CLS = {
        'scene':           'el-scene',
        'action':          'el-action',
        'character':       'el-character',
        'dialogue':        'el-dialogue',
        'subheading':      'el-subheading',
        'parenthetical':   'el-parenthetical',
        '_more':           'el-more',
        '_contd':          'el-contd',
        'transition':      'el-transition',
        'act-break':       'el-act-break',
        'cold-open':       'el-cold-open',
        'notes':           'el-notes',
        'act':             'el-act',
        'stage-direction': 'el-stage-direction',
        'tag':             'el-tag',
        'dual-dialogue':   'el-action',
    }

    parts = [
        '<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8">',
        f'<title>{esc(title)}</title>',
        f'<style>{CSS}</style></head><body class="format-{esc(fmt)}">',
    ]

    # ── Cover page ────────────────────────────────────────────────────
    if inc_cover:
        cv = {
            'title':    esc(cover.get('title')    or title),
            'author':   esc(cover.get('author',   '')),
            'basedOn':  esc(cover.get('basedOn',  '')),
            'draft':    esc(cover.get('draft',    '')),
            'date':     esc(cover.get('date',     '')),
            'contact':  '<br>'.join(filter(None, [
                            esc(cover.get('contact1', '')), esc(cover.get('contact2', '')),
                            esc(cover.get('contact3', '')), esc(cover.get('contact4', '')),
                        ])),
            'rights':   '<br>'.join(filter(None, [
                            esc(cover.get('rights1', '')), esc(cover.get('rights2', '')),
                        ])),
        }
        parts += ['<div class="cover-page"><div class="cv-top">']
        if cv['title']:   parts.append(f'<div class="cv-title">{cv["title"]}</div>')
        if cv['author']:  parts.append(f'<div class="cv-author">Written by<br>{cv["author"]}</div>')
        if cv['basedOn']: parts.append(f'<div class="cv-based">{cv["basedOn"]}</div>')
        dd = ' | '.join(filter(None, [cv['draft'], cv['date']]))
        if dd:            parts.append(f'<div class="cv-draft">{dd}</div>')
        parts.append('</div>')   # cv-top
        if cv['contact'] or cv['rights']:
            parts += ['<div class="cv-bottom">']
            if cv['contact']: parts.append(f'<div class="cv-contact">{cv["contact"]}</div>')
            if cv['rights']:  parts.append(f'<div class="cv-rights">{cv["rights"]}</div>')
            parts.append('</div>')
        parts.append('</div>')   # cover-page

    # ── Script body ───────────────────────────────────────────────────
    if inc_script and (layout or lines):
        explicit_layout = isinstance(layout, list)
        processed = layout if explicit_layout else _inject(lines)
        parts.append('<div class="script-body explicit-layout">' if explicit_layout else '<div class="script-body">')

        i = 0
        page_counter = 1
        while i < len(processed):
            line  = processed[i]
            lt    = line.get('type', 'action')
            txt   = line.get('text', '')

            def render_text(kind, value):
                value = str(value or '').strip()
                if fmt == 'play' and kind in ('action', 'stage-direction') and value:
                    if not (value.startswith('(') and value.endswith(')')):
                        value = f'({value})'
                return esc(value)

            # Hard page break
            if lt == '_break':
                parts.append('<div class="pg-break"></div>')
                if not explicit_layout:
                    page_counter += 1
                    parts.append(f'<div class="page-num-stamp">{page_counter}.</div>')
                i += 1; continue

            if lt == '_page-num':
                parts.append(f'<div class="page-num-stamp">{esc(txt)}</div>')
                i += 1; continue

            if lt == 'dual-dialogue':
                columns = line.get('columns', [])
                dual_cls = 'dual-dialogue-wrap page-leading' if line.get('pageLeading') else 'dual-dialogue-wrap'
                parts.append(f'<div class="{dual_cls}">')
                for column in columns[:2]:
                    parts.append('<div class="dual-col">')
                    for item in (column if isinstance(column, list) else []):
                        item_type = item.get('type', 'dialogue') if isinstance(item, dict) else 'dialogue'
                        item_text = item.get('text', '') if isinstance(item, dict) else ''
                        item_cls = TYPE_CLS.get(item_type, 'el-dialogue')
                        parts.append(f'<div class="{item_cls}">{render_text(item_type, item_text) or "&nbsp;"}</div>')
                    parts.append('</div>')
                parts.append('</div>')
                i += 1; continue

            if explicit_layout:
                cls = TYPE_CLS.get(lt, 'el-action')
                if line.get('pageLeading'):
                    cls += ' page-leading'
                parts.append(f'<div class="{cls}">{render_text(lt, txt) or "&nbsp;"}</div>')
                i += 1; continue

            # Speech block: character + its dialogue/paren/more run
            if lt == 'character':
                blk  = [line]
                j    = i + 1
                while j < len(processed):
                    nt = processed[j].get('type')
                    if nt in ('dialogue', 'parenthetical', '_more'):
                        blk.append(processed[j]); j += 1
                    else:
                        break
                total_h = sum(_height(b.get('type','dialogue'), b.get('text','')) for b in blk)
                cls = 'speech' + (' long' if total_h > 10 else '')
                parts.append(f'<div class="{cls}">')
                for b in blk:
                    bt   = b.get('type', 'dialogue')
                    btxt = render_text(bt, b.get('text', ''))
                    bcls = TYPE_CLS.get(bt, 'el-dialogue')
                    parts.append(f'<div class="{bcls}">{btxt or "&nbsp;"}</div>')
                parts.append('</div>')
                i = j; continue

            # Action: short ones (≤3 wrapped lines) avoid page break
            if lt == 'action':
                h   = _wrap_lines(txt, ACT_COLS)
                cls = 'el-action' + (' no-break' if h <= 3 else '')
                parts.append(f'<div class="{cls}">{render_text(lt, txt) or "&nbsp;"}</div>')
                i += 1; continue

            # All other elements
            cls = TYPE_CLS.get(lt, 'el-action')
            parts.append(f'<div class="{cls}">{render_text(lt, txt) or "&nbsp;"}</div>')
            i += 1

        parts.append('</div>')   # script-body

    parts.append('</body></html>')
    return '\n'.join(parts)

def _recent_path(userdata_dir):
    return userdata_dir / 'recent_scripts.json'

def _prefs_path(userdata_dir):
    # prefs.json lives in the installed Skript application folder,
    # not in the user's Documents — so the preference persists even if the
    # user moves their Documents folder, and is tied to this installation.
    return _get_install_dir() / 'prefs.json'

def _get_install_dir():
    """Return the folder that contains Skript.exe (or skript.py in development).
    Works both when run as a PyInstaller EXE (sys.frozen) and in plain Python."""
    if getattr(sys, 'frozen', False):
        # PyInstaller sets sys.executable to the EXE path
        return pathlib.Path(sys.executable).parent
    # Dev / plain Python: use the directory of this .py file
    return pathlib.Path(__file__).parent

def _load_prefs(userdata_dir):
    p = _prefs_path(userdata_dir)
    if not p.exists(): return {}
    try:
        return json.loads(p.read_text('utf-8'))
    except Exception:
        return {}

def _save_prefs(prefs, userdata_dir):
    p = _prefs_path(userdata_dir)
    p.write_text(json.dumps(prefs, indent=2), 'utf-8')


def _ensure_collab_server():
    """Start the collaboration server on 0.0.0.0 if not already running."""
    global _COLLAB_SERVER, _COLLAB_PORT_VAL, _COLLAB_LOCAL_ONLY
    if _COLLAB_SERVER is not None:
        return True
    try:
        # Port 0 reserves an available port atomically, avoiding a race between
        # probing for a port and starting the collaboration listener.
        try:
            srv = ThreadingHTTPServer(('0.0.0.0', 0), SFHandler)
            _COLLAB_LOCAL_ONLY = False
        except OSError:
            # Some managed Windows/firewall configurations deny listeners on
            # every network interface. Still create a working same-device link.
            srv = ThreadingHTTPServer(('127.0.0.1', 0), SFHandler)
            _COLLAB_LOCAL_ONLY = True
        _COLLAB_PORT_VAL = int(srv.server_address[1])
        t   = threading.Thread(target=srv.serve_forever, daemon=True)
        t.start()
        _COLLAB_SERVER = srv
        return True
    except Exception as exc:
        _COLLAB_SERVER = None
        _COLLAB_PORT_VAL = None
        _COLLAB_LOCAL_ONLY = False
        raise RuntimeError(f'Could not start secure sharing service: {exc}') from exc


def _gen_viewer_password():
    """Generate a memorable but secure viewer password: WORD-WORD-NNNN."""
    words = [
        'amber','azure','black','bloom','cedar','chase','cloud','coral','crisp',
        'delta','dusk','eagle','ember','first','flame','forge','frost','ghost',
        'glass','green','grove','haven','horse','ivory','jade','lunar','maple',
        'mist','noble','ocean','onyx','orbit','pearl','pilot','plum','prime',
        'quill','raven','ridge','river','robin','royal','ruby','sage','scout',
        'shore','silk','slate','smoke','solar','spark','steel','stone','swift',
        'thorn','tide','tiger','torch','ultra','unity','vault','viola','vista',
        'vivid','wave','wheat','white','wilde','willow','wind','wolf','zenith'
    ]
    w1 = secrets.choice(words).capitalize()
    w2 = secrets.choice(words).capitalize()
    n  = secrets.randbelow(9000) + 1000
    return f'{w1}-{w2}-{n}'



def _load_recent(userdata_dir):
    rp = _recent_path(userdata_dir)
    if not rp.exists(): return []
    try:
        items = json.loads(rp.read_text('utf-8'))
        # Filter to only files that still exist
        return [i for i in items if pathlib.Path(i['path']).exists()][:20]
    except Exception:
        return []

def _update_recent(fpath, title, userdata_dir):
    items = _load_recent(userdata_dir)
    fpath = str(fpath)
    # Remove existing entry for same path
    items = [i for i in items if i['path'] != fpath]
    # Prepend
    items.insert(0, {
        'path': fpath,
        'title': title,
        'savedAt': __import__('datetime').datetime.now().isoformat()
    })
    _recent_path(userdata_dir).write_text(json.dumps(items[:20], indent=2), encoding='utf-8')


def _detect_low_spec() -> bool:
    """Return True if this device has limited CPU or RAM.
    Triggers on Surface Go, Atom, Celeron, Pentium, and budget AMD APUs.
    Uses only ctypes (stdlib) — no psutil required."""
    try:
        cpu_logical = os.cpu_count() or 4
        ram_gb = 8.0  # assume sufficient unless we detect otherwise

        if sys.platform == 'win32':
            # --- RAM via GlobalMemoryStatusEx (ctypes, no extra deps) ---
            import ctypes
            class _MEMSTATEX(ctypes.Structure):
                _fields_ = [
                    ('dwLength',                ctypes.c_ulong),
                    ('dwMemoryLoad',            ctypes.c_ulong),
                    ('ullTotalPhys',            ctypes.c_ulonglong),
                    ('ullAvailPhys',            ctypes.c_ulonglong),
                    ('ullTotalPageFile',        ctypes.c_ulonglong),
                    ('ullAvailPageFile',        ctypes.c_ulonglong),
                    ('ullTotalVirtual',         ctypes.c_ulonglong),
                    ('ullAvailVirtual',         ctypes.c_ulonglong),
                    ('ullAvailExtendedVirtual', ctypes.c_ulonglong),
                ]
            stat = _MEMSTATEX()
            stat.dwLength = ctypes.sizeof(stat)
            ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(stat))
            ram_gb = stat.ullTotalPhys / (1024 ** 3)

        # Low-spec: ≤4 logical CPUs AND ≤10.5 GB RAM
        # Surface Go (4 GB or 8 GB), Intel Atom / Celeron N-series (4 GB),
        # budget AMD APUs (4–8 GB).  Threshold raised to 10.5 GB so that
        # 8 GB Surface Go models are caught (8 < 10.5 ✓) while skipping
        # mainstream 16 GB laptops (16 > 10.5 ✗).
        return cpu_logical <= 4 and ram_gb <= 10.5
    except Exception:
        return False


def _create_splash():
    """Create a professional Adobe-style frameless splash screen.

    Layout (560 × 340):
      ┌─────────────────────────────────────────────────────┐
      │  [icon]  Skript                   (dark main area)  │
      │          Professional Screenwriting                  │
      │          Version 1.0                                 │
      │                                                      │
      │  [credit line]   [copyright]                         │
      ├─────────────────────────────────────────────────────┤  ← thin divider
      │  [status text]              [██████░░░░]  progress  │
      └─────────────────────────────────────────────────────┘
    """
    try:
        import tkinter as tk
        from tkinter import font as tkfont

        # ── Window setup ──────────────────────────────────────────────────
        root = tk.Tk()
        root.overrideredirect(True)
        root.attributes('-topmost', True)

        W, H = 560, 320
        sw = root.winfo_screenwidth()
        sh = root.winfo_screenheight()
        splash_x = max(0, (sw - W) // 2)
        splash_y = max(0, (sh - H) // 2)
        root.geometry(f'{W}x{H}+{splash_x}+{splash_y}')

        # ── Colour palette (matches app) ──────────────────────────────────
        C_BACKDROP   = '#08080f'
        C_BG         = '#0d0d18'   # centred card background
        C_FOOTER     = '#121220'   # footer strip
        C_DIVIDER    = '#1e1e30'
        C_PURPLE     = '#7b5ef8'   # brand accent
        C_PURPLE_LO  = '#4a3b96'   # darker purple for bar track
        C_TEXT       = '#e8e8f0'
        C_DIM        = '#8888aa'
        C_DIMMER     = '#444466'

        # Keep the native splash fully opaque. A partially transparent
        # top-level window is composed against the desktop on every update and
        # can leave visible bands on some integrated Windows graphics drivers.
        root.configure(bg=C_BACKDROP)
        try:
            root.attributes('-alpha', 1.0)
        except Exception:
            pass

        # ── Fonts ─────────────────────────────────────────────────────────
        try:
            f_title   = tkfont.Font(family='Segoe UI',       size=26, weight='bold')
            f_sub     = tkfont.Font(family='Segoe UI',       size=11)
            f_ver     = tkfont.Font(family='Segoe UI',       size=9)
            f_status  = tkfont.Font(family='Segoe UI',       size=9)
            f_credit  = tkfont.Font(family='Segoe UI',       size=8)
        except Exception:
            f_title  = tkfont.Font(size=22, weight='bold')
            f_sub    = tkfont.Font(size=10)
            f_ver    = tkfont.Font(size=8)
            f_status = tkfont.Font(size=8)
            f_credit = tkfont.Font(size=7)

        # ── Single compact splash (never create a full-screen backing layer) ─
        main = tk.Canvas(root, width=W, height=H, bg=C_BG,
                         highlightthickness=1,
                         highlightbackground='#24243a', bd=0)
        main.pack(fill='both', expand=True)

        # ── Drawn icon: diamond with camera-shutter aperture ─────────────
        # Positioned top-left of the content area
        IX, IY, IS = 56, 56, 44   # centre x, centre y, half-size of diamond
        def diamond(x, y, s, fill, outline=''):
            pts = [x, y - s, x + s, y, x, y + s, x - s, y]
            main.create_polygon(pts, fill=fill, outline=outline, width=0)

        # Outer diamond — purple
        diamond(IX, IY, IS, C_PURPLE)
        # Inner diamond — slightly darker
        diamond(IX, IY, int(IS * 0.72), '#5a42d6')
        # Aperture blades (6 rounded segments suggesting a lens)
        import math
        for angle_deg in range(0, 360, 60):
            a  = math.radians(angle_deg)
            a2 = math.radians(angle_deg + 30)
            r1 = int(IS * 0.30)
            r2 = int(IS * 0.54)
            r3 = int(IS * 0.20)
            # Each blade: two points on outer arc + one on inner
            p = [
                IX + int(r2 * math.cos(a - 0.22)),
                IY + int(r2 * math.sin(a - 0.22)),
                IX + int(r2 * math.cos(a + 0.22)),
                IY + int(r2 * math.sin(a + 0.22)),
                IX + int(r3 * math.cos(a2)),
                IY + int(r3 * math.sin(a2)),
            ]
            main.create_polygon(p, fill='#c0b0ff', outline='')
        # Centre circle
        main.create_oval(IX - 9, IY - 9, IX + 9, IY + 9,
                         fill='#0d0d18', outline='')
        main.create_oval(IX - 5, IY - 5, IX + 5, IY + 5,
                         fill='#9b7fff', outline='')

        # ── Title / subtitle / version ────────────────────────────────────
        TX = IX + IS + 18   # text x start
        main.create_text(TX, IY - 14, text='Skript',
                         font=f_title, fill=C_TEXT, anchor='w')
        main.create_text(TX + 2, IY + 18, text='Professional Screenwriting',
                         font=f_sub,  fill=C_DIM,  anchor='w')

        # Version (read from VERSION.txt if present)
        try:
            import pathlib as _pl
            vf = _resource_path('VERSION.txt')
            _ver = vf.read_text('utf-8').strip() if vf.exists() else '1.0'
        except Exception:
            _ver = '1.0'
        main.create_text(TX + 2, IY + 38, text=f'Version {_ver}',
                         font=f_ver, fill=C_DIMMER, anchor='w')

        # ── Horizontal rule separating body from footer ───────────────────
        FOOTER_Y = H - 52
        main.create_rectangle(0, FOOTER_Y, W, FOOTER_Y + 1,
                              fill=C_DIVIDER, outline='')
        main.create_rectangle(0, FOOTER_Y + 1, W, H,
                              fill=C_FOOTER, outline='')

        # ── Credits & copyright ───────────────────────────────────────────
        CREDIT_Y = FOOTER_Y + 11
        main.create_text(16, CREDIT_Y,
                         text="Jake McNeil - 2026",
                         font=f_credit, fill=C_DIMMER, anchor='w')
        main.create_text(W - 16, CREDIT_Y,
                         text='All rights reserved.',
                         font=f_credit, fill=C_DIMMER, anchor='e')

        # ── Status text (bottom-left of footer) ──────────────────────────
        STATUS_Y = FOOTER_Y + 30
        status_id = main.create_text(16, STATUS_Y, text='Initializing…',
                                     font=f_status, fill=C_DIM, anchor='w')

        # ── Progress bar ─────────────────────────────────────────────────
        BAR_X1  = 16
        BAR_X2  = W - 16
        BAR_Y1  = FOOTER_Y + 42
        BAR_Y2  = BAR_Y1 + 4
        BAR_R   = 2   # corner radius

        # Track (background of bar)
        def _rounded_rect(c, x1, y1, x2, y2, r, fill, outline=''):
            c.create_arc(x1,     y1,     x1+2*r, y1+2*r, start=90,  extent=90,  fill=fill, outline=outline, style='pieslice')
            c.create_arc(x2-2*r, y1,     x2,     y1+2*r, start=0,   extent=90,  fill=fill, outline=outline, style='pieslice')
            c.create_arc(x1,     y2-2*r, x1+2*r, y2,     start=180, extent=90,  fill=fill, outline=outline, style='pieslice')
            c.create_arc(x2-2*r, y2-2*r, x2,     y2,     start=270, extent=90,  fill=fill, outline=outline, style='pieslice')
            c.create_rectangle(x1+r, y1, x2-r, y2, fill=fill, outline=outline)
            c.create_rectangle(x1, y1+r, x2, y2-r, fill=fill, outline=outline)

        _rounded_rect(main, BAR_X1, BAR_Y1, BAR_X2, BAR_Y2, BAR_R,
                      fill=C_PURPLE_LO)

        # Fill (grows as progress advances) — draw as overlapping rectangles
        # We'll redraw by deleting and recreating tagged items each frame
        BAR_W   = BAR_X2 - BAR_X1
        bar_fill_id = main.create_rectangle(BAR_X1, BAR_Y1,
                                            BAR_X1, BAR_Y2,
                                            fill=C_PURPLE, outline='', tags='bar_fill')
        # Shimmer highlight on top of fill
        shimmer_id = main.create_rectangle(BAR_X1, BAR_Y1,
                                           BAR_X1, BAR_Y1 + 1,
                                           fill='#a888ff', outline='', tags='bar_fill')

        # ── Attach state to root ──────────────────────────────────────────
        root._sf_canvas     = main
        root._sf_status_id  = status_id
        root._sf_bar_fill   = bar_fill_id
        root._sf_shimmer    = shimmer_id
        root._sf_bar_x1     = BAR_X1
        root._sf_bar_y1     = BAR_Y1
        root._sf_bar_y2     = BAR_Y2
        root._sf_bar_x2     = BAR_X2
        root._sf_bar_w      = BAR_W
        root._sf_progress   = 0.0
        root._sf_start      = time.time()

        root.update()
        return root

    except Exception:
        return None


def _destroy_splash(splash):
    """Withdraw and flush the splash so no stale compositor surface remains."""
    if splash is None:
        return
    try:
        splash.attributes('-topmost', False)
        splash.withdraw()
        splash.update_idletasks()
        if sys.platform == 'win32':
            try:
                import ctypes
                ctypes.windll.dwmapi.DwmFlush()
            except Exception:
                pass
    finally:
        try:
            splash.destroy()
        except Exception:
            pass


# Phase status messages tied to progress milestones (0–100%)
_SPLASH_PHASES = [
    (0,   'Initializing…'),
    (10,  'Loading application modules…'),
    (22,  'Preparing workspace…'),
    (38,  'Starting local server…'),
    (55,  'Loading script engine…'),
    (70,  'Configuring formatting rules…'),
    (82,  'Almost ready…'),
    (92,  'Launching editor…'),
    (100, 'Ready'),
]


def _pump_splash(splash, elapsed: float, server_ready: bool = False):
    """Advance the splash one animation frame.

    Progress curve:
      - Advances quickly to 85% over ~20 s using an ease-out curve.
      - Holds at 85–90% (pulsing) until server_ready=True.
      - Once ready, jumps smoothly to 100%.
    Call every ~0.12 s from the wait loop.
    """
    if splash is None:
        return
    try:
        import math

        c      = splash._sf_canvas
        bx1    = splash._sf_bar_x1
        by1    = splash._sf_bar_y1
        by2    = splash._sf_bar_y2
        bw     = splash._sf_bar_w
        C_PURPLE = '#7b5ef8'
        C_SHIMMER= '#a888ff'

        if server_ready:
            # Sweep to 100 %
            target = 1.0
        else:
            # Ease-out: approaches 0.88 asymptotically over ~25 s
            # f(t) = 0.88 * (1 - e^(-t/12))
            target = 0.88 * (1.0 - math.exp(-elapsed / 12.0))
            # Add tiny sine pulse so bar appears alive while stalled
            pulse  = 0.015 * math.sin(elapsed * 3.0)
            target = max(0.0, min(0.88, target + pulse))

        # Smooth toward target (lerp for fluid motion)
        prev = splash._sf_progress
        speed = 0.18 if server_ready else 0.08
        new_p = prev + (target - prev) * speed
        new_p = max(0.0, min(1.0, new_p))
        splash._sf_progress = new_p

        fill_w = max(0, int(bw * new_p))
        fill_x2 = bx1 + fill_w

        # Update bar fill
        c.coords(splash._sf_bar_fill,   bx1, by1, fill_x2, by2)
        c.coords(splash._sf_shimmer,    bx1, by1, fill_x2, by1 + 1)

        # Update status text based on progress percentage
        pct = int(new_p * 100)
        msg = _SPLASH_PHASES[0][1]
        for threshold, label in _SPLASH_PHASES:
            if pct >= threshold:
                msg = label
        if server_ready:
            msg = 'Ready'
        c.itemconfig(splash._sf_status_id, text=msg)

        c.update()
    except Exception:
        pass



def _launch_edge(url: str, low_perf: bool = False):
    """Launch Microsoft Edge in --app mode (no chrome/address bar)."""
    edge_paths = [
        r'C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe',
        r'C:\Program Files\Microsoft\Edge\Application\msedge.exe',
        'msedge',
        'microsoft-edge',
    ]

    # Base flags — safe on all hardware
    base_flags = [
        '--disable-extensions',
        '--no-first-run',
        '--disable-default-apps',
        '--disable-infobars',
        '--allow-insecure-localhost',
        '--window-name=Skript',
    ]

    window_flags = _browser_window_flags()
    if low_perf:
        # Surface Go / Atom / Celeron: limit renderer memory and reduce GPU
        # compositor pressure while preserving the centred window geometry.
        # Do NOT use --disable-gpu — that forces software rasteriser which is
        # slower; instead cap compositing layers and renderer RAM.
        perf_flags = [
            '--renderer-process-limit=2',
            '--js-flags=--max-old-space-size=256',
            '--disk-cache-size=52428800',     # 50 MB disk cache cap
            '--media-cache-size=1',
            '--disable-features=msEdgeOptimisticCacheEarlyHints',
            '--enable-low-end-device-mode',   # Blink low-end mode (reduces memory)
            '--disable-smooth-scrolling',
        ]
    else:
        perf_flags = []

    for ep in edge_paths:
        try:
            si = None
            cf = 0
            if sys.platform == 'win32':
                si = subprocess.STARTUPINFO()
                si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                si.wShowWindow = 1
                cf = subprocess.CREATE_NO_WINDOW
            proc = subprocess.Popen(
                [ep, f'--app={url}'] + base_flags + window_flags + perf_flags,
                startupinfo=si, creationflags=cf, cwd=tempfile.gettempdir())
            return proc
        except (FileNotFoundError, OSError):
            continue
    return None


def _launch_chrome(url: str, low_perf: bool = False):
    """Try Chrome as a fallback."""
    chrome_paths = [
        r'C:\Program Files\Google\Chrome\Application\chrome.exe',
        r'C:\Program Files (x86)\Google\Chrome\Application\chrome.exe',
        'google-chrome', 'google-chrome-stable', 'chromium-browser', 'chromium',
    ]
    window_flags = _browser_window_flags()
    extra = ['--enable-low-end-device-mode', '--renderer-process-limit=2',
             '--js-flags=--max-old-space-size=256'] if low_perf else []
    for cp in chrome_paths:
        try:
            si2 = None; cf2 = 0
            if sys.platform == 'win32':
                si2 = subprocess.STARTUPINFO()
                si2.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                cf2 = subprocess.CREATE_NO_WINDOW
            return subprocess.Popen(
                [cp, f'--app={url}'] + window_flags + [
                 '--no-first-run', '--window-name=Skript'] + extra,
                startupinfo=si2, creationflags=cf2, cwd=tempfile.gettempdir())
        except (FileNotFoundError, OSError):
            continue
    return None


def _browser_window_flags():
    """Return a centred rectangular app-window size that fits the work area."""
    screen_width, screen_height = 1366, 768
    try:
        if sys.platform == 'win32':
            import ctypes
            screen_width = ctypes.windll.user32.GetSystemMetrics(0)
            screen_height = ctypes.windll.user32.GetSystemMetrics(1)
    except Exception:
        pass
    width = max(900, min(1280, screen_width - 80))
    height = max(620, min(800, screen_height - 100))
    width = min(width, screen_width)
    height = min(height, screen_height)
    x = max(0, (screen_width - width) // 2)
    y = max(0, (screen_height - height) // 2)
    return [f'--window-size={width},{height}', f'--window-position={x},{y}']


def _centred_window_geometry(left, top, right, bottom):
    """Return the existing touch-friendly rectangle inside a work area."""
    work_width = max(1, int(right) - int(left))
    work_height = max(1, int(bottom) - int(top))
    width = min(work_width, max(640, min(1280, work_width - 80)))
    height = min(work_height, max(480, min(800, work_height - 100)))

    # Keep the desktop window visibly landscape even on unusual displays.
    if width < int(height * 1.25):
        height = max(1, min(height, int(width / 1.25)))
    x = int(left) + (work_width - width) // 2
    y = int(top) + (work_height - height) // 2
    return x, y, width, height


def _adaptive_desktop_geometry(left, top, right, bottom, touch_mode=False):
    """Choose the best centred window for desktop or preserve touch sizing."""
    if touch_mode:
        return _centred_window_geometry(left, top, right, bottom)

    work_width = max(1, int(right) - int(left))
    work_height = max(1, int(bottom) - int(top))
    # Desktop target is Full HD. Fit its 16:9 aspect ratio into the usable
    # Windows work area so taskbars and smaller displays are never covered.
    margin_x = 80 if work_width >= 900 else 20
    margin_y = 80 if work_height >= 650 else 20
    available_width = max(1, work_width - margin_x)
    available_height = max(1, work_height - margin_y)
    scale = min(1.0, available_width / 1920.0, available_height / 1080.0)
    width = max(1, min(work_width, int(round(1920 * scale))))
    height = max(1, min(work_height, int(round(1080 * scale))))
    x = int(left) + (work_width - width) // 2
    y = int(top) + (work_height - height) // 2
    return x, y, width, height


def _windows_touch_capable(user32=None):
    """Detect an active Windows touch digitizer without changing web touch UI."""
    if sys.platform != 'win32' and user32 is None:
        return False
    try:
        user32 = user32 or __import__('ctypes').windll.user32
        digitizer = int(user32.GetSystemMetrics(94))  # SM_DIGITIZER
        touches = int(user32.GetSystemMetrics(95))    # SM_MAXIMUMTOUCHES
        return touches > 0 and bool(digitizer & 0x80) and bool(digitizer & 0x03)
    except Exception:
        return False


def _set_windows_window_icon(hwnd, user32=None, icon_path=None):
    """Apply Skript's packaged icon to an Edge/Chrome app-mode window."""
    if user32 is None and sys.platform != 'win32':
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt

        real_user32 = user32 is None
        user32 = user32 or ctypes.windll.user32
        icon_path = pathlib.Path(icon_path) if icon_path else _resource_path('assets', 'skript.ico')
        if not icon_path.is_file():
            return False

        load_image = user32.LoadImageW
        try:
            load_image.argtypes = [wt.HINSTANCE, wt.LPCWSTR, ctypes.c_uint,
                                   ctypes.c_int, ctypes.c_int, ctypes.c_uint]
            load_image.restype = wt.HANDLE
        except Exception:
            pass

        IMAGE_ICON = 1
        LR_LOADFROMFILE = 0x0010
        SM_CXICON, SM_CYICON = 11, 12
        SM_CXSMICON, SM_CYSMICON = 49, 50
        big = load_image(None, str(icon_path), IMAGE_ICON,
                         max(16, user32.GetSystemMetrics(SM_CXICON)),
                         max(16, user32.GetSystemMetrics(SM_CYICON)), LR_LOADFROMFILE)
        small = load_image(None, str(icon_path), IMAGE_ICON,
                           max(16, user32.GetSystemMetrics(SM_CXSMICON)),
                           max(16, user32.GetSystemMetrics(SM_CYSMICON)), LR_LOADFROMFILE)
        if not big and not small:
            return False
        big = big or small
        small = small or big
        WM_SETICON = 0x0080
        user32.SendMessageW(hwnd, WM_SETICON, 1, big)    # title/taskbar icon
        user32.SendMessageW(hwnd, WM_SETICON, 0, small)  # small/title icon
        if real_user32:
            _WINDOW_ICON_HANDLES.extend(handle for handle in (big, small)
                                        if handle and handle not in _WINDOW_ICON_HANDLES)
        return True
    except Exception:
        return False


def _set_windows_app_identity(hwnd, executable_path=None):
    """Give the hosted Edge window Skript's own Windows taskbar identity."""
    if sys.platform != 'win32':
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt

        class GUID(ctypes.Structure):
            _fields_ = [('Data1', ctypes.c_uint32), ('Data2', ctypes.c_uint16),
                        ('Data3', ctypes.c_uint16), ('Data4', ctypes.c_ubyte * 8)]

        class PROPERTYKEY(ctypes.Structure):
            _fields_ = [('fmtid', GUID), ('pid', wt.DWORD)]

        class PROPVARIANT(ctypes.Structure):
            _fields_ = [('vt', ctypes.c_ushort), ('wReserved1', ctypes.c_ushort),
                        ('wReserved2', ctypes.c_ushort), ('wReserved3', ctypes.c_ushort),
                        ('pwszVal', ctypes.c_wchar_p)]

        def guid(value):
            parsed = uuid.UUID(value)
            return GUID(parsed.time_low, parsed.time_mid, parsed.time_hi_version,
                        (ctypes.c_ubyte * 8)(parsed.clock_seq_hi_variant,
                                             parsed.clock_seq_low, *parsed.node.to_bytes(6, 'big')))

        iid_store = guid('886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99')
        app_fmtid = guid('9F4C2855-9F79-4B39-A8D0-E1D42DE1D5F3')
        shell32 = ctypes.windll.shell32
        shell32.SHGetPropertyStoreForWindow.argtypes = [wt.HWND, ctypes.POINTER(GUID),
                                                         ctypes.POINTER(ctypes.c_void_p)]
        shell32.SHGetPropertyStoreForWindow.restype = ctypes.c_long
        ctypes.windll.ole32.CoInitialize(None)
        store = ctypes.c_void_p()
        if shell32.SHGetPropertyStoreForWindow(hwnd, ctypes.byref(iid_store), ctypes.byref(store)) < 0:
            return False
        vtable = ctypes.cast(store, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
        SetValue = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p,
                                      ctypes.POINTER(PROPERTYKEY), ctypes.POINTER(PROPVARIANT))(vtable[6])
        Commit = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p)(vtable[7])
        Release = ctypes.WINFUNCTYPE(ctypes.c_ulong, ctypes.c_void_p)(vtable[2])
        exe = pathlib.Path(executable_path or sys.executable).resolve()
        values = (
            (2, f'"{exe}"'),       # System.AppUserModel.RelaunchCommand
            (3, f'{exe},0'),         # System.AppUserModel.RelaunchIconResource
            (5, 'JakeMcNeil.Skript') # System.AppUserModel.ID — set last
        )
        ok = True
        try:
            for property_id, value in values:
                key = PROPERTYKEY(app_fmtid, property_id)
                variant = PROPVARIANT(31, 0, 0, 0, value)  # VT_LPWSTR
                if SetValue(store, ctypes.byref(key), ctypes.byref(variant)) < 0:
                    ok = False
                    break
            if ok and Commit(store) < 0:
                ok = False
        finally:
            Release(store)
        return ok
    except Exception:
        return False


def _enable_native_app_shell(hwnd, user32=None):
    """Remove Edge's caption so Skript's own title bar owns close behaviour."""
    if user32 is None and sys.platform != 'win32':
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt
        real_user32 = user32 is None
        user32 = user32 or ctypes.windll.user32
        get_style = getattr(user32, 'GetWindowLongPtrW', None) or user32.GetWindowLongW
        set_style = getattr(user32, 'SetWindowLongPtrW', None) or user32.SetWindowLongW
        if real_user32:
            get_style.argtypes = [wt.HWND, ctypes.c_int]
            get_style.restype = ctypes.c_ssize_t
            set_style.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_ssize_t]
            set_style.restype = ctypes.c_ssize_t
            user32.SetWindowPos.argtypes = [wt.HWND, wt.HWND, ctypes.c_int, ctypes.c_int,
                                            ctypes.c_int, ctypes.c_int, ctypes.c_uint]
            user32.SetWindowPos.restype = wt.BOOL
        GWL_STYLE = -16
        WS_CAPTION = 0x00C00000
        WS_SYSMENU = 0x00080000
        WS_MINIMIZEBOX = 0x00020000
        WS_MAXIMIZEBOX = 0x00010000
        WS_THICKFRAME = 0x00040000
        style = int(get_style(hwnd, GWL_STYLE))
        native_chrome = WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX
        set_style(hwnd, GWL_STYLE, (style & ~native_chrome) | WS_THICKFRAME)
        SWP_NOSIZE, SWP_NOMOVE, SWP_NOZORDER = 0x0001, 0x0002, 0x0004
        SWP_NOACTIVATE, SWP_FRAMECHANGED = 0x0010, 0x0020
        user32.SetWindowPos(hwnd, 0, 0, 0, 0, 0,
                            SWP_NOSIZE | SWP_NOMOVE | SWP_NOZORDER |
                            SWP_NOACTIVATE | SWP_FRAMECHANGED)
        return True
    except Exception:
        return False


def _window_has_native_browser_chrome(hwnd, user32=None):
    """Return whether Edge/Chrome has restored its own caption controls."""
    if user32 is None and sys.platform != 'win32':
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt
        real_user32 = user32 is None
        user32 = user32 or ctypes.windll.user32
        get_style = getattr(user32, 'GetWindowLongPtrW', None) or user32.GetWindowLongW
        if real_user32:
            get_style.argtypes = [wt.HWND, ctypes.c_int]
            get_style.restype = ctypes.c_ssize_t
        style = int(get_style(hwnd, -16))
        native_chrome = 0x00C00000 | 0x00080000 | 0x00020000 | 0x00010000
        return bool(style & native_chrome)
    except Exception:
        return False


def _maintain_native_app_shell(hwnd):
    """Keep Chromium from restoring a second titlebar after startup/state changes."""
    if sys.platform != 'win32':
        return
    try:
        import ctypes
        import ctypes.wintypes as wt
        user32 = ctypes.windll.user32
        user32.IsWindow.argtypes = [wt.HWND]
        user32.IsWindow.restype = wt.BOOL
        while user32.IsWindow(hwnd) and not _APP_SHUTDOWN_EVENT.wait(0.25):
            # The embedded child has a different style contract. Its host pump
            # owns frame removal and positioning from this point onward.
            if _HOSTED_BROWSER_HWND == hwnd:
                return
            if _window_has_native_browser_chrome(hwnd):
                _enable_native_app_shell(hwnd)
                _set_windows_window_icon(hwnd)
    except Exception:
        pass


def _native_host_is_active(user32=None):
    """Return True while Skript's native outer window is alive."""
    if sys.platform != 'win32' or not _NATIVE_HOST_HWND:
        return False
    try:
        import ctypes
        return bool((user32 or ctypes.windll.user32).IsWindow(_NATIVE_HOST_HWND))
    except Exception:
        return False


def _suppress_native_host_border(hwnd):
    """Hide DWM's one-pixel frame while retaining native resize behaviour."""
    if sys.platform != 'win32' or not hwnd:
        return False
    try:
        import ctypes

        # Windows 11: DWMWA_BORDER_COLOR with DWMWA_COLOR_NONE keeps the
        # WS_THICKFRAME resize affordance but removes its visible white line.
        color_none = ctypes.c_uint(0xFFFFFFFE)
        result = ctypes.windll.dwmapi.DwmSetWindowAttribute(
            hwnd, 34, ctypes.byref(color_none), ctypes.sizeof(color_none)
        )
        return result == 0
    except Exception:
        return False


def _measure_browser_content_insets(hwnd, user32):
    """Measure Edge's client-drawn title strip and border in physical pixels."""
    import ctypes
    import ctypes.wintypes as wt

    class RECT(ctypes.Structure):
        _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long),
                    ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

    dpi = 96
    try:
        get_dpi = getattr(user32, 'GetDpiForWindow', None)
        if get_dpi:
            dpi = max(96, int(get_dpi(hwnd) or 96))
    except Exception:
        pass

    # Edge's app-mode strip is 19 logical px high with a roughly 5 px
    # resizable frame. These DPI-scaled values are the safe fallback.
    fallback = (
        max(0, round(4.5 * dpi / 96)),
        max(1, round(19 * dpi / 96)),
        max(0, round(4 * dpi / 96)),
        max(0, round(4 * dpi / 96)),
    )

    outer = RECT()
    if not user32.GetWindowRect(hwnd, ctypes.byref(outer)):
        return fallback

    renderers = []
    EnumChildProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wt.HWND, wt.LPARAM)

    def enum_child(child, _lparam):
        class_name = ctypes.create_unicode_buffer(128)
        user32.GetClassNameW(child, class_name, len(class_name))
        if class_name.value == 'Chrome_RenderWidgetHostHWND':
            child_rect = RECT()
            if user32.GetWindowRect(child, ctypes.byref(child_rect)):
                area = max(0, child_rect.right - child_rect.left) * max(
                    0, child_rect.bottom - child_rect.top
                )
                renderers.append((area, child_rect))
        return True

    try:
        user32.EnumChildWindows(hwnd, EnumChildProc(enum_child), 0)
    except Exception:
        return fallback
    if not renderers:
        return fallback

    renderer = max(renderers, key=lambda item: item[0])[1]
    measured = (
        max(0, renderer.left - outer.left),
        max(0, renderer.top - outer.top),
        max(0, outer.right - renderer.right),
        max(0, outer.bottom - renderer.bottom),
    )
    left, top, right, bottom = measured
    # Ignore transient DevTools/dialog renderer surfaces and retain the
    # predictable DPI-scaled values until the main page renderer is ready.
    if left > 48 or not (8 <= top <= 96) or right > 48 or bottom > 48:
        return fallback
    return measured


def _position_hosted_browser(force=False):
    """Fill the native host while clipping Edge's own app-mode strip."""
    global _HOSTED_BROWSER_SIZE
    if sys.platform != 'win32' or not _NATIVE_HOST_HWND or not _HOSTED_BROWSER_HWND:
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt

        user32 = ctypes.windll.user32
        if not user32.IsWindow(_NATIVE_HOST_HWND) or not user32.IsWindow(_HOSTED_BROWSER_HWND):
            return False

        class RECT(ctypes.Structure):
            _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long),
                        ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

        client = RECT()
        if not user32.GetClientRect(_NATIVE_HOST_HWND, ctypes.byref(client)):
            return False
        width = max(1, client.right - client.left)
        height = max(1, client.bottom - client.top)
        state = (width, height, tuple(_HOSTED_BROWSER_INSETS))

        left, top, right, bottom = _HOSTED_BROWSER_INSETS
        target_width = width + left + right
        target_height = height + top + bottom

        class POINT(ctypes.Structure):
            _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

        origin = POINT(0, 0)
        browser_rect = RECT()
        user32.ClientToScreen(_NATIVE_HOST_HWND, ctypes.byref(origin))
        user32.GetWindowRect(_HOSTED_BROWSER_HWND, ctypes.byref(browser_rect))
        geometry_changed = (
            abs(browser_rect.left - (origin.x - left)) > 1 or
            abs(browser_rect.top - (origin.y - top)) > 1 or
            abs((browser_rect.right - browser_rect.left) - target_width) > 1 or
            abs((browser_rect.bottom - browser_rect.top) - target_height) > 1
        )

        get_style = getattr(user32, 'GetWindowLongPtrW', None) or user32.GetWindowLongW
        set_style = getattr(user32, 'SetWindowLongPtrW', None) or user32.SetWindowLongW
        get_style.argtypes = [wt.HWND, ctypes.c_int]
        get_style.restype = ctypes.c_ssize_t
        set_style.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_ssize_t]
        set_style.restype = ctypes.c_ssize_t
        style = int(get_style(_HOSTED_BROWSER_HWND, -16))
        forbidden = 0x80000000 | 0x00C00000 | 0x00040000 | 0x00080000 | 0x00020000 | 0x00010000
        required = 0x40000000 | 0x10000000 | 0x04000000 | 0x02000000
        style_changed = bool(style & forbidden) or (style & required) != required
        if style_changed:
            set_style(_HOSTED_BROWSER_HWND, -16, (style & ~forbidden) | required)

        if not force and not style_changed and not geometry_changed and state == _HOSTED_BROWSER_SIZE:
            return True

        SWP_NOZORDER = 0x0004
        SWP_NOACTIVATE = 0x0010
        SWP_FRAMECHANGED = 0x0020
        SWP_SHOWWINDOW = 0x0040
        flags = SWP_NOZORDER | SWP_NOACTIVATE | SWP_SHOWWINDOW
        if style_changed:
            flags |= SWP_FRAMECHANGED
        user32.SetWindowPos(
            _HOSTED_BROWSER_HWND, 0, -left, -top,
            target_width, target_height, flags,
        )
        _HOSTED_BROWSER_SIZE = state
        return True
    except Exception:
        return False


def _resize_native_host(x, y, width, height):
    """Move/resize the existing Skript host from any request-handler thread."""
    if not _native_host_is_active():
        return False
    try:
        import ctypes
        user32 = ctypes.windll.user32
        user32.ShowWindow(_NATIVE_HOST_HWND, 9)  # SW_RESTORE
        user32.SetWindowPos(
            _NATIVE_HOST_HWND, 0, int(x), int(y), int(width), int(height),
            0x0004 | 0x0040,  # SWP_NOZORDER | SWP_SHOWWINDOW
        )
        _suppress_native_host_border(_NATIVE_HOST_HWND)
        _position_hosted_browser(force=True)
        user32.SetForegroundWindow(_NATIVE_HOST_HWND)
        return True
    except Exception:
        return False


def _create_native_browser_host(browser_hwnd, x, y, width, height):
    """Embed Edge in a Skript-owned window so only Skript's titlebar is visible."""
    global _NATIVE_HOST_ROOT, _NATIVE_HOST_HWND, _HOSTED_BROWSER_HWND
    global _HOSTED_BROWSER_INSETS, _HOSTED_BROWSER_SIZE, _HOSTED_INSET_CHECK_AT
    global _HOSTED_INSET_CANDIDATE, _HOSTED_INSET_CANDIDATE_COUNT
    if sys.platform != 'win32' or threading.current_thread() is not threading.main_thread():
        return False
    if _native_host_is_active():
        return _resize_native_host(x, y, width, height)

    root = None
    try:
        import ctypes
        import ctypes.wintypes as wt
        import tkinter as tk

        user32 = ctypes.windll.user32
        get_style = getattr(user32, 'GetWindowLongPtrW', None) or user32.GetWindowLongW
        set_style = getattr(user32, 'SetWindowLongPtrW', None) or user32.SetWindowLongW
        get_style.argtypes = [wt.HWND, ctypes.c_int]
        get_style.restype = ctypes.c_ssize_t
        set_style.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_ssize_t]
        set_style.restype = ctypes.c_ssize_t

        insets = _measure_browser_content_insets(browser_hwnd, user32)

        root = tk.Tk()
        # Assemble and stabilise the embedded renderer while hidden. This
        # prevents the user seeing Edge's delayed DPI adjustment as a sideways
        # nudge immediately after the splash closes.
        root.withdraw()
        root.title('Skript — Professional Screenwriting')
        root.configure(bg='#101116')
        root.overrideredirect(True)
        root.geometry(f'{int(width)}x{int(height)}+{int(x)}+{int(y)}')
        root.update_idletasks()
        root.update()

        widget_hwnd = int(root.winfo_id())
        host_hwnd = int(user32.GetParent(widget_hwnd) or widget_hwnd)

        GWL_STYLE, GWL_EXSTYLE = -16, -20
        WS_CHILD, WS_VISIBLE = 0x40000000, 0x10000000
        WS_CLIPSIBLINGS, WS_CLIPCHILDREN = 0x04000000, 0x02000000
        WS_POPUP, WS_CAPTION, WS_THICKFRAME = 0x80000000, 0x00C00000, 0x00040000
        WS_SYSMENU, WS_MINIMIZEBOX, WS_MAXIMIZEBOX = 0x00080000, 0x00020000, 0x00010000
        WS_EX_APPWINDOW, WS_EX_TOOLWINDOW = 0x00040000, 0x00000080
        WS_EX_WINDOWEDGE, WS_EX_CLIENTEDGE, WS_EX_STATICEDGE = 0x00000100, 0x00000200, 0x00020000

        host_style = int(get_style(host_hwnd, GWL_STYLE))
        host_style &= ~(WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX)
        host_style |= WS_POPUP | WS_THICKFRAME | WS_CLIPCHILDREN
        set_style(host_hwnd, GWL_STYLE, host_style)
        host_exstyle = int(get_style(host_hwnd, GWL_EXSTYLE))
        set_style(host_hwnd, GWL_EXSTYLE,
                  (host_exstyle & ~(
                      WS_EX_TOOLWINDOW | WS_EX_WINDOWEDGE |
                      WS_EX_CLIENTEDGE | WS_EX_STATICEDGE
                  )) | WS_EX_APPWINDOW)

        SWP_NOZORDER, SWP_FRAMECHANGED, SWP_SHOWWINDOW = 0x0004, 0x0020, 0x0040
        user32.SetWindowPos(
            host_hwnd, 0, int(x), int(y), int(width), int(height),
            SWP_NOZORDER | SWP_FRAMECHANGED,
        )

        ctypes.set_last_error(0)
        old_parent = user32.SetParent(browser_hwnd, host_hwnd)
        if not old_parent and ctypes.get_last_error():
            raise ctypes.WinError(ctypes.get_last_error())

        browser_style = int(get_style(browser_hwnd, GWL_STYLE))
        browser_style &= ~(
            WS_POPUP | WS_CAPTION | WS_THICKFRAME | WS_SYSMENU |
            WS_MINIMIZEBOX | WS_MAXIMIZEBOX
        )
        browser_style |= WS_CHILD | WS_VISIBLE | WS_CLIPSIBLINGS | WS_CLIPCHILDREN
        set_style(browser_hwnd, GWL_STYLE, browser_style)

        _NATIVE_HOST_ROOT = root
        _NATIVE_HOST_HWND = host_hwnd
        _HOSTED_BROWSER_HWND = int(browser_hwnd)
        _HOSTED_BROWSER_INSETS = tuple(int(value) for value in insets)
        _HOSTED_BROWSER_SIZE = None
        _HOSTED_INSET_CHECK_AT = 0.0
        _HOSTED_INSET_CANDIDATE = None
        _HOSTED_INSET_CANDIDATE_COUNT = 0

        def request_close():
            if _HOSTED_BROWSER_HWND and user32.IsWindow(_HOSTED_BROWSER_HWND):
                user32.PostMessageW(_HOSTED_BROWSER_HWND, 0x0010, 0, 0)

        root.protocol('WM_DELETE_WINDOW', request_close)
        _set_windows_app_identity(host_hwnd)
        _set_windows_window_icon(host_hwnd)
        _position_hosted_browser(force=True)

        # Cross-process parenting can change Edge's DPI context. Wait for two
        # matching renderer measurements before revealing the host so the
        # content starts in its final position and stays there.
        prior_measurement = None
        for _ in range(6):
            root.update_idletasks()
            root.update()
            time.sleep(0.04)
            measured = _measure_browser_content_insets(browser_hwnd, user32)
            if measured == prior_measurement:
                _HOSTED_BROWSER_INSETS = measured
                _HOSTED_BROWSER_SIZE = None
                break
            prior_measurement = measured
            _position_hosted_browser(force=True)

        root.deiconify()
        root.update_idletasks()
        root.update()
        user32.SetWindowPos(
            host_hwnd, 0, int(x), int(y), int(width), int(height),
            SWP_NOZORDER | SWP_FRAMECHANGED | SWP_SHOWWINDOW,
        )
        _suppress_native_host_border(host_hwnd)
        _position_hosted_browser(force=True)
        user32.SetForegroundWindow(host_hwnd)
        return True
    except Exception:
        if root is not None:
            try:
                root.destroy()
            except Exception:
                pass
        _NATIVE_HOST_ROOT = None
        _NATIVE_HOST_HWND = None
        _HOSTED_BROWSER_HWND = None
        _HOSTED_BROWSER_INSETS = (0, 0, 0, 0)
        _HOSTED_BROWSER_SIZE = None
        _HOSTED_INSET_CHECK_AT = 0.0
        _HOSTED_INSET_CANDIDATE = None
        _HOSTED_INSET_CANDIDATE_COUNT = 0
        return False


def _pump_native_browser_host():
    """Process host messages and keep Edge clipped during resize/maximise."""
    global _HOSTED_BROWSER_INSETS, _HOSTED_BROWSER_SIZE, _HOSTED_INSET_CHECK_AT
    global _HOSTED_INSET_CANDIDATE, _HOSTED_INSET_CANDIDATE_COUNT
    if not _NATIVE_HOST_ROOT or not _native_host_is_active():
        return False
    try:
        import ctypes
        user32 = ctypes.windll.user32
        if not _HOSTED_BROWSER_HWND or not user32.IsWindow(_HOSTED_BROWSER_HWND):
            return False
        _NATIVE_HOST_ROOT.update_idletasks()
        _NATIVE_HOST_ROOT.update()
        now = time.monotonic()
        force = False
        if now >= _HOSTED_INSET_CHECK_AT:
            measured = list(_measure_browser_content_insets(_HOSTED_BROWSER_HWND, user32))
            current = _HOSTED_BROWSER_INSETS
            # Ignore harmless one-pixel DWM rounding at the side/bottom edges.
            # React only to a new, stable renderer layout (for example after a
            # real monitor-DPI change), never to alternating transient values.
            for index in (0, 2, 3):
                if abs(measured[index] - current[index]) <= 1:
                    measured[index] = current[index]
            measured = tuple(measured)
            if measured == current:
                _HOSTED_INSET_CANDIDATE = None
                _HOSTED_INSET_CANDIDATE_COUNT = 0
            elif measured == _HOSTED_INSET_CANDIDATE:
                _HOSTED_INSET_CANDIDATE_COUNT += 1
                if _HOSTED_INSET_CANDIDATE_COUNT >= 3:
                    _HOSTED_BROWSER_INSETS = measured
                    _HOSTED_BROWSER_SIZE = None
                    _HOSTED_INSET_CANDIDATE = None
                    _HOSTED_INSET_CANDIDATE_COUNT = 0
                    force = True
            else:
                _HOSTED_INSET_CANDIDATE = measured
                _HOSTED_INSET_CANDIDATE_COUNT = 1
            _HOSTED_INSET_CHECK_AT = now + 0.4
        _position_hosted_browser(force=force)
        return True
    except Exception:
        return False


def _destroy_native_browser_host():
    """Close the embedded browser and release Skript's native outer window."""
    global _NATIVE_HOST_ROOT, _NATIVE_HOST_HWND, _HOSTED_BROWSER_HWND
    global _HOSTED_BROWSER_INSETS, _HOSTED_BROWSER_SIZE, _HOSTED_INSET_CHECK_AT
    global _HOSTED_INSET_CANDIDATE, _HOSTED_INSET_CANDIDATE_COUNT
    if sys.platform == 'win32':
        try:
            import ctypes
            user32 = ctypes.windll.user32
            if _HOSTED_BROWSER_HWND and user32.IsWindow(_HOSTED_BROWSER_HWND):
                user32.PostMessageW(_HOSTED_BROWSER_HWND, 0x0010, 0, 0)
                deadline = time.time() + 0.75
                while time.time() < deadline and user32.IsWindow(_HOSTED_BROWSER_HWND):
                    if _NATIVE_HOST_ROOT:
                        try:
                            _NATIVE_HOST_ROOT.update()
                        except Exception:
                            break
                    time.sleep(0.03)
        except Exception:
            pass
    if _NATIVE_HOST_ROOT is not None:
        try:
            _NATIVE_HOST_ROOT.destroy()
        except Exception:
            pass
    _NATIVE_HOST_ROOT = None
    _NATIVE_HOST_HWND = None
    _HOSTED_BROWSER_HWND = None
    _HOSTED_BROWSER_INSETS = (0, 0, 0, 0)
    _HOSTED_BROWSER_SIZE = None
    _HOSTED_INSET_CHECK_AT = 0.0
    _HOSTED_INSET_CANDIDATE = None
    _HOSTED_INSET_CANDIDATE_COUNT = 0


def _titlebar_overlay_is_active(user32=None):
    if sys.platform != 'win32' or not _TITLEBAR_OVERLAY_HWND or not _TITLEBAR_OVERLAY_TARGET:
        return False
    try:
        import ctypes
        u32 = user32 or ctypes.windll.user32
        return bool(u32.IsWindow(_TITLEBAR_OVERLAY_HWND) and u32.IsWindow(_TITLEBAR_OVERLAY_TARGET))
    except Exception:
        return False


def _sync_native_titlebar_overlay(force=False):
    """Keep the small native Skript bar over Edge's client-drawn strip."""
    global _TITLEBAR_OVERLAY_GEOMETRY
    if not _titlebar_overlay_is_active():
        return False
    try:
        import ctypes

        user32 = ctypes.windll.user32

        class RECT(ctypes.Structure):
            _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long),
                        ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

        if user32.IsIconic(_TITLEBAR_OVERLAY_TARGET) or not user32.IsWindowVisible(_TITLEBAR_OVERLAY_TARGET):
            _TITLEBAR_OVERLAY_ROOT.withdraw()
            _TITLEBAR_OVERLAY_GEOMETRY = None
            return True

        outer = RECT()
        if not user32.GetWindowRect(_TITLEBAR_OVERLAY_TARGET, ctypes.byref(outer)):
            return False
        left, top, right, _bottom = _measure_browser_content_insets(
            _TITLEBAR_OVERLAY_TARGET, user32
        )
        strip_height = max(28, min(64, int(top)))
        width = max(320, int(outer.right - outer.left))
        geometry = (int(outer.left), int(outer.top), width, strip_height)
        if force or geometry != _TITLEBAR_OVERLAY_GEOMETRY:
            _TITLEBAR_OVERLAY_ROOT.geometry(
                f'{geometry[2]}x{geometry[3]}+{geometry[0]}+{geometry[1]}'
            )
            _TITLEBAR_OVERLAY_ROOT.deiconify()
            _TITLEBAR_OVERLAY_ROOT.update_idletasks()
            _TITLEBAR_OVERLAY_GEOMETRY = geometry
        user32.SetWindowPos(
            _TITLEBAR_OVERLAY_HWND, 0, geometry[0], geometry[1],
            geometry[2], geometry[3], 0x0004 | 0x0010 | 0x0040,
        )
        return True
    except Exception:
        return False


def _create_native_titlebar_overlay(browser_hwnd):
    """Cover Edge's internal title strip without reparenting its window."""
    global _TITLEBAR_OVERLAY_ROOT, _TITLEBAR_OVERLAY_HWND
    global _TITLEBAR_OVERLAY_TARGET, _TITLEBAR_OVERLAY_GEOMETRY
    if sys.platform != 'win32' or threading.current_thread() is not threading.main_thread():
        return False
    if _titlebar_overlay_is_active():
        return _sync_native_titlebar_overlay(force=True)

    root = None
    try:
        import ctypes
        import ctypes.wintypes as wt
        import tkinter as tk

        user32 = ctypes.windll.user32
        root = tk.Tk()
        root.withdraw()
        root.title('Skript titlebar')
        root.overrideredirect(True)
        root.configure(bg='#17171c')

        bar = tk.Frame(root, bg='#17171c', bd=0, highlightthickness=0)
        bar.pack(fill='both', expand=True)
        left = tk.Frame(bar, bg='#17171c', bd=0, highlightthickness=0)
        left.pack(side='left', fill='both', expand=True)

        try:
            icon = tk.PhotoImage(file=str(_resource_path('assets', 'skript-icon.png')))
            if max(icon.width(), icon.height()) > 20:
                factor = max(1, max(icon.width(), icon.height()) // 18)
                icon = icon.subsample(factor, factor)
            root._skript_titlebar_icon = icon
            icon_label = tk.Label(left, image=icon, bg='#17171c', bd=0)
            icon_label.pack(side='left', padx=(9, 7))
        except Exception:
            icon_label = tk.Label(left, text='▣', bg='#17171c', fg='#a991ff', bd=0)
            icon_label.pack(side='left', padx=(10, 7))

        title_label = tk.Label(
            left, text='Skript — Professional Screenwriting',
            bg='#17171c', fg='#d3d3dc', bd=0,
            font=('Segoe UI', 9), anchor='w',
        )
        title_label.pack(side='left', fill='both', expand=True)

        button_options = {
            'bg': '#17171c', 'fg': '#d3d3dc', 'activebackground': '#2b2b33',
            'activeforeground': '#ffffff', 'bd': 0, 'relief': 'flat',
            'highlightthickness': 0, 'font': ('Segoe UI Symbol', 11),
            'width': 5, 'takefocus': False,
        }
        minimise = tk.Button(bar, text='—', command=lambda: _window_control('minimize'), **button_options)
        maximise = tk.Button(bar, text='□', command=lambda: _window_control('maximize'), **button_options)
        close_options = dict(button_options)
        close_options.update({'activebackground': '#c42b1c'})
        close = tk.Button(
            bar, text='×', command=lambda: _publish_window_event('request-close'),
            **close_options,
        )
        close.pack(side='right', fill='y')
        maximise.pack(side='right', fill='y')
        minimise.pack(side='right', fill='y')

        def start_drag(event):
            if getattr(event, 'num', 1) == 1:
                _window_control('drag')

        def toggle_maximise(_event):
            _window_control('maximize')

        for widget in (bar, left, icon_label, title_label):
            widget.bind('<ButtonPress-1>', start_drag)
            widget.bind('<Double-Button-1>', toggle_maximise)

        root.update_idletasks()
        root.update()
        widget_hwnd = int(root.winfo_id())
        overlay_hwnd = int(user32.GetParent(widget_hwnd) or widget_hwnd)

        get_style = getattr(user32, 'GetWindowLongPtrW', None) or user32.GetWindowLongW
        set_style = getattr(user32, 'SetWindowLongPtrW', None) or user32.SetWindowLongW
        get_style.argtypes = [wt.HWND, ctypes.c_int]
        get_style.restype = ctypes.c_ssize_t
        set_style.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_ssize_t]
        set_style.restype = ctypes.c_ssize_t
        exstyle = int(get_style(overlay_hwnd, -20))
        set_style(overlay_hwnd, -20, (exstyle | 0x00000080 | 0x08000000) & ~0x00040000)
        # Make the bar an owned (not child) window. Edge remains a normal,
        # independently rendered top-level window, so it cannot collapse into
        # or expose a coloured Tk parent surface.
        set_style(overlay_hwnd, -8, int(browser_hwnd))

        _TITLEBAR_OVERLAY_ROOT = root
        _TITLEBAR_OVERLAY_HWND = overlay_hwnd
        _TITLEBAR_OVERLAY_TARGET = int(browser_hwnd)
        _TITLEBAR_OVERLAY_GEOMETRY = None
        root.protocol('WM_DELETE_WINDOW', lambda: _publish_window_event('request-close'))
        _sync_native_titlebar_overlay(force=True)
        return True
    except Exception:
        if root is not None:
            try:
                root.destroy()
            except Exception:
                pass
        _TITLEBAR_OVERLAY_ROOT = None
        _TITLEBAR_OVERLAY_HWND = None
        _TITLEBAR_OVERLAY_TARGET = None
        _TITLEBAR_OVERLAY_GEOMETRY = None
        return False


def _pump_native_titlebar_overlay():
    if not _TITLEBAR_OVERLAY_ROOT or not _titlebar_overlay_is_active():
        return False
    try:
        _TITLEBAR_OVERLAY_ROOT.update_idletasks()
        _TITLEBAR_OVERLAY_ROOT.update()
        return _sync_native_titlebar_overlay()
    except Exception:
        return False


def _destroy_native_titlebar_overlay():
    global _TITLEBAR_OVERLAY_ROOT, _TITLEBAR_OVERLAY_HWND
    global _TITLEBAR_OVERLAY_TARGET, _TITLEBAR_OVERLAY_GEOMETRY
    if _TITLEBAR_OVERLAY_ROOT is not None:
        try:
            _TITLEBAR_OVERLAY_ROOT.destroy()
        except Exception:
            pass
    _TITLEBAR_OVERLAY_ROOT = None
    _TITLEBAR_OVERLAY_HWND = None
    _TITLEBAR_OVERLAY_TARGET = None
    _TITLEBAR_OVERLAY_GEOMETRY = None


def _force_centred_browser_window(browser_process=None, timeout=12.0, touch_mode=None):
    """Override Edge/Chrome's restored geometry once the app window exists."""
    if sys.platform != 'win32':
        return False
    try:
        import ctypes
        import ctypes.wintypes as wt

        user32 = ctypes.windll.user32
        EnumWindowsProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wt.HWND, wt.LPARAM)

        class RECT(ctypes.Structure):
            _fields_ = [('left', ctypes.c_long), ('top', ctypes.c_long),
                        ('right', ctypes.c_long), ('bottom', ctypes.c_long)]

        work = RECT()
        SPI_GETWORKAREA = 0x0030
        if not user32.SystemParametersInfoW(SPI_GETWORKAREA, 0, ctypes.byref(work), 0):
            work.left = work.top = 0
            work.right = user32.GetSystemMetrics(0)
            work.bottom = user32.GetSystemMetrics(1)
        x, y, width, height = _adaptive_desktop_geometry(
            work.left, work.top, work.right, work.bottom,
            touch_mode=(_windows_touch_capable(user32) if touch_mode is None else bool(touch_mode)),
        )

        deadline = time.time() + timeout
        while time.time() < deadline:
            title_matches = []

            def enum_window(hwnd, _lparam):
                if not user32.IsWindowVisible(hwnd):
                    return True
                class_name = ctypes.create_unicode_buffer(128)
                user32.GetClassNameW(hwnd, class_name, len(class_name))
                if not class_name.value.startswith('Chrome_WidgetWin'):
                    return True
                title = ctypes.create_unicode_buffer(512)
                user32.GetWindowTextW(hwnd, title, len(title))
                if title.value.startswith('Skript'):
                    title_matches.append(hwnd)
                return True

            user32.EnumWindows(EnumWindowsProc(enum_window), 0)
            if title_matches:
                hwnd = title_matches[0]
                user32.ShowWindow(hwnd, 9)  # SW_RESTORE
                # Keep Chromium's standard Windows frame. Only centre and size
                # the top-level app window; do not reparent it or alter styles.
                _set_windows_app_identity(hwnd)
                user32.SetWindowPos(hwnd, 0, x, y, width, height, 0x0040)  # SWP_SHOWWINDOW
                _set_windows_window_icon(hwnd)
                user32.SetForegroundWindow(hwnd)
                return True
            time.sleep(0.1)
    except Exception:
        pass
    return False


def _find_free_port():
    with socket.socket() as s:
        s.bind(('127.0.0.1', 0))
        return s.getsockname()[1]


def _wait_for_server(port: int, timeout: float = 60.0) -> bool:
    """Wait until the HTTP server is actually serving responses (not just socket-open).
    Polls /api/version (tiny JSON) so we don't pull the full 1 MB HTML just to check.
    Timeout raised to 60 s for slow devices (Surface Go / Atom / Celeron cold start)."""
    import http.client as _hc
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            conn = _hc.HTTPConnection('127.0.0.1', port, timeout=2)
            conn.request('GET', '/api/version')
            r = conn.getresponse()
            r.read()
            conn.close()
            if r.status == 200:
                return True
        except Exception:
            time.sleep(0.15)
    return False


def _show_startup_error(message: str):
    """Report startup failures even though the packaged app has no console."""
    try:
        import tkinter as tk
        from tkinter import messagebox
        root = tk.Tk()
        root.withdraw()
        root.attributes('-topmost', True)
        messagebox.showerror('Skript could not start', message, parent=root)
        root.destroy()
    except Exception:
        try:
            userdata_dir, _ = _get_dirs()
            (userdata_dir / 'startup-error.log').write_text(message, encoding='utf-8')
        except Exception:
            pass


def _hide_console():
    """Hide the Python console window on Windows (SW_HIDE only)."""
    if sys.platform != 'win32':
        return
    try:
        import ctypes
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 0)  # SW_HIDE
    except Exception:
        pass

def _detach_console():
    """Fully detach from console — call ONLY after server is running in launch mode."""
    if sys.platform != 'win32':
        return
    try:
        import ctypes
        ctypes.windll.kernel32.FreeConsole()
    except Exception:
        pass


def _window_control(action: str):
    """Send minimize / maximize / close to the Edge app window via Win32 API."""
    if sys.platform != 'win32':
        return
    import ctypes, ctypes.wintypes

    SW_MINIMIZE  = 6
    SW_MAXIMIZE  = 3
    SW_RESTORE   = 9
    WM_CLOSE     = 0x0010
    SC_MAXIMIZE  = 0xF030
    WM_SYSCOMMAND = 0x0112

    u32 = ctypes.windll.user32
    pid = _EDGE_PROC.pid if _EDGE_PROC else None

    # Enumerate top-level windows to find our app window by PID
    found_hwnd = []
    EnumWindowsProc = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.wintypes.HWND, ctypes.wintypes.LPARAM)

    def _enum_cb(hwnd, lParam):
        if not ctypes.windll.user32.IsWindowVisible(hwnd):
            return True
        # Get PID for this window
        w_pid = ctypes.wintypes.DWORD(0)
        ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(w_pid))
        # Match by PID (direct process) or by window title as fallback
        if pid and w_pid.value == pid:
            found_hwnd.append(hwnd)
            return False  # stop enumeration
        # Fallback: match by title
        buf = ctypes.create_unicode_buffer(256)
        ctypes.windll.user32.GetWindowTextW(hwnd, buf, 256)
        if ('Skript' in buf.value or ('Script' + 'Forge') in buf.value) and buf.value != '':
            found_hwnd.append(hwnd)
            return False
        return True

    ctypes.windll.user32.EnumWindows(EnumWindowsProc(_enum_cb), 0)

    if not found_hwnd:
        # Last resort: enumerate all child/related windows by process
        all_hwnds = []
        def _enum_all(hwnd, lParam):
            w_pid = ctypes.wintypes.DWORD(0)
            ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(w_pid))
            if pid and w_pid.value == pid:
                all_hwnds.append(hwnd)
            return True
        ctypes.windll.user32.EnumWindows(EnumWindowsProc(_enum_all), 0)
        if all_hwnds:
            found_hwnd = [all_hwnds[0]]

    if not found_hwnd:
        return

    hwnd = found_hwnd[0]
    if action == 'minimize':
        u32.ShowWindow(hwnd, SW_MINIMIZE)
    elif action == 'maximize':
        # Toggle: if maximized, restore; else maximize
        import ctypes.wintypes as wt
        wp = (ctypes.c_int * 10)()  # WINDOWPLACEMENT is ~44 bytes / 10 ints
        # Simple check via GetWindowPlacement
        placement = ctypes.create_string_buffer(44)
        ctypes.c_uint.from_buffer_copy(ctypes.c_uint(44)).value  # cbSize
        u32.ShowWindow(hwnd, SW_RESTORE if u32.IsZoomed(hwnd) else SW_MAXIMIZE)
    elif action == 'close':
        u32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
    elif action == 'drag':
        u32.ReleaseCapture()
        u32.SendMessageW(hwnd, 0x00A1, 2, 0)  # WM_NCLBUTTONDOWN, HTCAPTION


def launch():
    # Hide console window immediately so no terminal flashes on startup
    diagnostic_mode = os.environ.get('SKRIPT_DIAGNOSTIC') == '1'
    if not diagnostic_mode:
        _hide_console()

    # Acquire the process-wide guard before creating the full-screen splash.
    if not _acquire_single_instance():
        return
    # A locked runtime from the previous release must never block Repair.
    # Cleanup runs after launch, when Windows/antivirus will usually have
    # released it, and is restricted to program folders beside this EXE.
    threading.Thread(target=_cleanup_obsolete_install_runtime, daemon=True).start()
    global _PRESERVE_RECOVERY_ON_EXIT
    _APP_SHUTDOWN_EVENT.clear()
    _PRESERVE_RECOVERY_ON_EXIT = False

    # ── 0. Detect hardware capability ────────────────────────────────────
    low_perf = _detect_low_spec()

    # ── 1. Pick a free port and bake it into the HTML ───────────────────
    global _MAIN_PORT_VAL, _API_TOKEN
    try:
        # Port 0 lets Windows select and reserve a free port atomically.
        server = ThreadingHTTPServer(('127.0.0.1', 0), SFHandler)
    except OSError as exc:
        _show_startup_error(
            'The local Skript service could not open a loopback port.\n\n'
            f'{exc}\n\nCheck that firewall or security software allows Skript to use 127.0.0.1.'
        )
        return

    port = int(server.server_address[1])
    _MAIN_PORT_VAL = port
    _API_TOKEN = secrets.token_urlsafe(32)
    SFHandler.html_bytes = _get_html(port, low_perf, _API_TOKEN)

    # ── 2. Start the HTTP server ─────────────────────────────────────────
    #    HTTPServer binds the socket in __init__, so the port is open
    #    BEFORE serve_forever starts — no race condition possible.
    t = threading.Thread(target=server.serve_forever, daemon=True)
    t.start()

    # Load any persisted collaboration sessions from previous runs
    _load_collab_sessions()

    # ── 3. Show loading splash and wait until server is fully ready ──────
    #    On Surface Go / Atom the PyInstaller bundle takes 30-50 s to
    #    decompress and start serving.  We show a splash so the user
    #    knows something is happening, poll the HTTP endpoint (not just
    #    the socket) with a 60 s timeout, then close the splash before
    #    handing off to Edge.
    splash = _create_splash()

    start = time.time()
    ready = False
    while not ready and (time.time() - start) < 60.0:
        _pump_splash(splash, time.time() - start, server_ready=False)
        # Poll the actual HTTP endpoint in 0.12 s increments inside the
        # splash pump loop — _wait_for_server has its own internal loop,
        # but we call it in single-attempt mode here so we can update UI.
        try:
            import http.client as _hc
            conn = _hc.HTTPConnection('127.0.0.1', port, timeout=1)
            conn.request('GET', '/api/version')
            r = conn.getresponse(); r.read(); conn.close()
            if r.status == 200:
                ready = True
        except Exception:
            pass
        if not ready:
            time.sleep(0.12)

    # Sweep bar to 100% and hold "Ready" for a beat before closing
    if splash and ready:
        for _ in range(14):
            _pump_splash(splash, 60.0, server_ready=True)
            time.sleep(0.05)

    if splash:
        _destroy_splash(splash)
        splash = None

    if not ready:
        server.shutdown()
        server.server_close()
        _show_startup_error(
            'The local Skript service did not respond within 60 seconds.\n\n'
            'Restart Skript. If this continues, allow Skript and Microsoft Edge '
            'through your firewall or security software.'
        )
        return

    url = f'http://127.0.0.1:{port}/'

    # ── 4. Launch Edge / Chrome in --app mode ────────────────────────────
    global _EDGE_PROC
    _EDGE_PROC = _launch_edge(url, low_perf)
    launched   = _EDGE_PROC
    if not launched:
        _EDGE_PROC = _launch_chrome(url, low_perf)
        launched   = _EDGE_PROC
    if not launched:
        webbrowser.open(url)

    # Chromium may ignore --window-position/--window-size when it restores a
    # prior app-window placement. Enforce the requested landscape rectangle
    # through Win32 after the real window has been created.
    if launched:
        _force_centred_browser_window(launched)

    # On slow devices keep the splash visible for a further ~2 s so there
    # is no naked gap between the Python splash closing and Edge's window
    # appearing with the in-browser boot screen.
    if low_perf and launched:
        try:
            import tkinter as _tk2
            _gap = _tk2.Tk()
            _gap.overrideredirect(True)
            _gap.attributes('-topmost', True)
            _gap.configure(bg='#0d0d18')
            _sw = _gap.winfo_screenwidth()
            _sh = _gap.winfo_screenheight()
            _gap.geometry(f'1x1+{_sw//2}+{_sh//2}')  # 1×1 invisible keeper
            for _ in range(18):   # ~2.2 s
                _gap.update()
                time.sleep(0.12)
            _gap.destroy()
        except Exception:
            time.sleep(2.0)   # plain sleep fallback

    # ── 5. Silence stdout/stderr then detach console ─────────────────────
    if not diagnostic_mode:
        try:
            import os as _os
            _nul = open(_os.devnull, 'w')
            sys.stdout = _nul
            sys.stderr = _nul
        except Exception:
            pass
        _detach_console()

    # ── 6. Write session.lock — absence at next launch = clean exit ────────
    userdata_dir, _ = _get_dirs()
    lock_path = userdata_dir / 'session.lock'

    # ── 7. Keep Python alive so the server stays up ──────────────────────
    clean_exit = False
    try:
        while not _APP_SHUTDOWN_EVENT.wait(0.10):
            pass
        clean_exit = _APP_SHUTDOWN_EVENT.is_set()
    except (KeyboardInterrupt, Exception):
        pass

    # ── Clean exit: remove lock file and recovery snapshot ───────────────
    if clean_exit and not _PRESERVE_RECOVERY_ON_EXIT:
        try:
            if lock_path.exists(): lock_path.unlink()
            rp = userdata_dir / 'recovery.recover'
            _remove_file_family(rp, backup_count=10)
        except Exception:
            pass

    server.shutdown()
    server.server_close()
    print('Skript stopped.')


def release_self_test():
    """Exercise packaged runtime resources without opening the application UI."""
    report_path = os.environ.get('SKRIPT_SELF_TEST_REPORT', '').strip()
    report = {'ok': False, 'checks': []}
    server = None
    try:
        version_file = _resource_path('VERSION.txt')
        version = version_file.read_text(encoding='utf-8').strip()
        if not re.fullmatch(r'\d+\.\d+\.\d+\.\d+', version):
            raise RuntimeError('Packaged VERSION.txt is missing or invalid.')
        report['version'] = version
        report['checks'].append('version')

        for relative in (
            ('vendor', 'pdfjs', 'pdf.min.mjs'),
            ('vendor', 'pdfjs', 'pdf.worker.min.mjs'),
            ('vendor', 'ocr', 'tesseract.min.js'),
            ('vendor', 'ocr', 'worker.min.js'),
            ('vendor', 'ocr', 'lang', 'eng.traineddata.gz'),
            ('vendor', 'ocr', 'core', 'tesseract-core.wasm.js'),
            ('vendor', 'ocr', 'core', 'tesseract-core-lstm.wasm.js'),
            ('vendor', 'ocr', 'core', 'tesseract-core-simd.wasm.js'),
            ('vendor', 'ocr', 'core', 'tesseract-core-simd-lstm.wasm.js'),
            ('vendor', 'ocr', 'core', 'tesseract-core-relaxedsimd.wasm.js'),
            ('vendor', 'ocr', 'core', 'tesseract-core-relaxedsimd-lstm.wasm.js'),
            ('assets', 'skript-icon.png'),
            ('assets', 'skript.ico'),
        ):
            resource = _resource_path(*relative)
            if not resource.is_file() or resource.stat().st_size < 100:
                raise RuntimeError(f'Missing packaged resource: {"/".join(relative)}')
        report['checks'].append('resources')

        import tkinter as _self_test_tk
        tcl = _self_test_tk.Tcl()
        report['tcl'] = str(tcl.eval('info patchlevel'))
        report['checks'].append('tkinter')

        global _MAIN_PORT_VAL, _API_TOKEN
        server = ThreadingHTTPServer(('127.0.0.1', 0), SFHandler)
        _MAIN_PORT_VAL = int(server.server_address[1])
        _API_TOKEN = secrets.token_urlsafe(16)
        SFHandler.html_bytes = _get_html(_MAIN_PORT_VAL, False, _API_TOKEN)
        if len(SFHandler.html_bytes) < 100_000 or version.encode('utf-8') not in SFHandler.html_bytes:
            raise RuntimeError('Packaged application HTML failed its integrity check.')
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        import http.client as _self_test_http
        connection = _self_test_http.HTTPConnection('127.0.0.1', _MAIN_PORT_VAL, timeout=10)
        connection.request('GET', '/api/version')
        response = connection.getresponse()
        payload = response.read()
        connection.close()
        if response.status != 200 or version.encode('utf-8') not in payload:
            raise RuntimeError('Packaged local service did not return the expected version.')
        report['checks'].extend(['embedded-html', 'loopback-service'])
        report['ok'] = True
        return 0
    except Exception as error:
        report['error'] = f'{type(error).__name__}: {error}'
        return 1
    finally:
        if server is not None:
            try:
                server.shutdown()
                server.server_close()
            except Exception:
                pass
        if report_path:
            try:
                pathlib.Path(report_path).parent.mkdir(parents=True, exist_ok=True)
                pathlib.Path(report_path).write_text(json.dumps(report, indent=2), encoding='utf-8')
            except Exception:
                pass


def build_exe():
    print('=' * 60)
    print('  Skript — Building standalone EXE')
    print('=' * 60)
    print()
    print('This script is self-contained — no HTML files, no assets.')
    print('The EXE will be a single file that runs on any Windows PC.')
    print()

    this_file = os.path.abspath(__file__)
    out_dir = os.path.join(os.path.dirname(this_file), 'dist')

    print('[1/3] Installing PyInstaller...')
    subprocess.check_call([sys.executable, '-m', 'pip', 'install',
                           'pyinstaller', '--upgrade', '-q'])
    print('      Done.')
    print()

    print('[2/3] Compiling EXE (1-3 minutes)...')
    print()
    result = subprocess.run([
        sys.executable, '-m', 'PyInstaller',
        '--onefile',
        '--windowed',            # no console window
        '--name', 'Skript',
        '--distpath', out_dir,
        '--workpath', os.path.join(os.path.dirname(this_file), '_build'),
        '--specpath', os.path.join(os.path.dirname(this_file), '_build'),
        '--hidden-import', 'tkinter',
        '--hidden-import', 'tkinter.filedialog',
        this_file,
    ])

    print()
    if result.returncode == 0:
        exe = os.path.join(out_dir, 'Skript.exe')
        if os.path.exists(exe):
            size_mb = os.path.getsize(exe) / 1024 / 1024
            print('[3/3] SUCCESS!')
            print()
            print(f'  EXE: {exe}')
            print(f'  Size: {size_mb:.1f} MB')
            print()
            print('  Double-click Skript.exe to run.')
            print('  Copy it to any Windows 10/11 PC — no Python needed.')
            print()
            # Note: "Launch now?" prompt is handled by BUILD_EXE.bat (CHOICE command).
            # Running build_exe() directly? Manually open dist/Skript.exe.
        else:
            print('[3/3] Build succeeded but EXE not found in dist/.')
            print(f'      Check {out_dir}')
    else:
        print('[3/3] Build FAILED — see errors above.')
        print()
        print('  Common fixes:')
        print('  - Run BUILD_EXE.bat from a normal Command Prompt (not PowerShell)')
        print('  - Run as Administrator if permission errors appear')
    print()


# ═══════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════
if __name__ == '__main__':
    if '--release-self-test' in sys.argv:
        raise SystemExit(release_self_test())
    elif '--build' in sys.argv:
        build_exe()
    else:
        launch()
