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
    'o6wu8ll0bS3aRreK8h84/Bk54fEJc+mMxHALmUFJDWOYTJTH+zxE++L8y2KESCw129s9JxOYxbC1nNDVFtkKUEiuNYew41KgnRul'
    'QVgY3//pX4E9bDSbzUwAxSRMx/CAclNwGWBg8dPtcfQ8nIDgUVkLxtGaSMuwDgGC2dWHIUi4fWA/Lw8Oj6ztXCi7DRJ9RQS3+hGM'
    'XQWKogoHPcLxW/s2hUH0ZqYiqllt7zeHBy8wCRvgHZ1eW1KExwuzzfQlaeEx63vQ3TK/Kq9H9Ny3MJITQ/sFkY7zgoY3/+ZrnFeM'
    '7tCyv4FkNgyQ0WLb/AMbZ0J9rn9jqM+hgwj5DB3BLBfDZVPyyyTGkHlt5GqjEH7hAc/X6A1UpQadUjU2GjhQRr3BtB/S4mtrpl1Q'
    'gumtbUjPlJlZECfsHPYVzOl9pKCs7GKR0nQw0YSkKKuBM111rlJxya1GfOFbFGWRLuqmTHeSyAPXiGKiincCUz6N4wn6S1ecAI3m'
    'ypBxX5yco3cvBgrdTZI40SiE+IsmC9s0WlcQDcK+NpZ4PczwAcoKlvYLFts7p/Z0pG8pt71PbqhWYwi7A2wqs4Z3MA5HuC6VcRu3'
    '78a7mvfALM+Zyvqj2Po3xM7ZkqCn1Mxcxp6ydDWtui3i7nhUNyRFRJvUOqaq3mQtMG7pOs4i+3BQRS0TlW3Rqrqp4nqOeG4ws4/j'
    'PfKTW3lpUX4dpcY3ZUtsDcZVuqDGwdjL1xBvwoLiz9JxvnjfmA2ts3TqCZe3Ol9Q589sY7bJIuNGsrTDTHZgsYwc9edKmavGlZbO'
    'TLGE3w3nf4ahRK8xGnxabMSuU+0AY18YMhs9dK3ANPxxzenZ08elDKT4z5/FLWiu248mZbL7zJ1WZ2kVFrfiHFmLSorOJIs393Pu'
    'LBZY9BfZ680a4+bc0fvpl9Of1+ac8yZ3jdA1b502OWe3WrR8LB2UDvks3uay5orw/bEOFU5qIP60XUqXmmmsVDA7Etddz4fEgXdD'
    'r6sMopIwkmMe80sUNRwjpuBIX4suPMNIzo80b12U4rLuVSkZEaILaqRi63S6eM4IgrVIllbZUn0HvEnkZjcgWn8mI+KiZthafpt2'
    'uMatG+oCo8QD5+UaodK3bqOfwNq4TV+ogtPM4jrUaG+SmfdcNjG2jqig2xzsY7v/bdCDEpp+aCmD6AoLmeH4JnYuLYIMHhYppXU6'
    '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'
    'mRV4jvXkVu6cts/5sFFDiOXPbi7CunKnaxTcD95GZxJp+i/ZJmiNnzNEVkWo+XEfFhr3CgaesOq+dbbf9h3v7eWKKHpssFbjOE1W'
    '3y39mXtvo7rGbO7cM4WTzN1Ve7vTcOzkPpil9Nq60STW1bXE7Qa5nDlWIVH31GxVS+ugk/A1vrS9uu6SrGIhuFy50WKkKHqqb900'
    'LEpWCLleuw7DXx2Lwk3JD3//d7gLScycvT1hmf5WsjzJXHpmp7G+ybY3Ly9nnY1Xjv8nPupfeyuZ3Yq4fmQ0Vn9yvdumuRXJLtj0'
    'qC0zfG69mLfYGcwHPFJLIlByzZX5gF4ZiPQEybU9n54hOKZJp15F9ze2VXTvPnA7jdNgQr8++6zlbxrfy1Qv6nV29/Cr99HVaye0'
    '4lN+3GKlM5otnaiESKObDS/nliUXrIjn7sA/3YRs8Iqot0tJmKOSWNk2ThJM3GCj1LS+x8Z/OP1wkgo0qMnjBcn8+lp71bv81Pg2'
    'Vx+cVktP60qczq9bjvnMrAWw0DRI/frXKuLzWj5iCSR4yNqQu2JHU+Pn2lmIrzvTrk31a3UHIRSL8BTnHMkKOamQmMQRumYcg3nj'
    'Nmnjat/h67sxmoaCyWvCl+PuHZ1r793maWYj3bn5SHdqjHRHRrJOvynitVAgSYwGwof9NW8YZK0IT8hoSD3ywczax4Q0arGnk3Br'
    'zX8yM+M2XplAB3XljXpy7aienc0f94TGPSkZVRvBNPpo9w6V26HbNeGirTH37WOlGnmjQWOrEIDV9ls7YhYaK1/WyTdGivqsrR/f'
    'lmurdVLbPK+s5po7upU/D36Ra+wI+n5jfpFrLIFYJfCQF6b1ldlAJuYC4pfwQKRdfIWsIAcnfOOHzBhRmDQF/K2WA/4ax0o73WSo'
    'og+VQRX6t3l/VcCSCiFpSxmhE2F8xMTbltzc1/VHlY7XaaHqGsdOmzc1vHd+tEwlrWiq4ktU5j+fiTsOt6Pfrp8MZprWkV0qZDML'
    'JRbPPkSQy7XVnKHb7fYWi+CyiyvbptsC7qjIZ98cAWQj9Sk8Oy1IwaD0s2xqzkPLEjMZ0rkMCd42Z1ZGg6OZBH1JkjlRrnQi0lmI'
    'MtjSm5Y+moGU/bHsvVUdJia7J58P87JL6V4yA/U5M/PlrItWgZbRrAc86fvuUPn+eV1dqy36VDfrpOV06EeyXUmo2u319RLPMRey'
    'ju4yI4x7lM6uj396l3ZO0pkXChGM3tT4FM2yTxn39aCe95nPxXk9ulnuVMDr/B/VDrsIm7zo2177nCw0X5DItNA+P57oVTHAjpZA'
    '4eN9k65NyIfApWUAVIhbmql7JCHgYHM0EXto5Q4A3+lVbiK//bGbWL4T7v25uXplb2iRKSRhGmcqkLsSqWMP0s6eLwZOtFjkDxo7'
    'arHIgiABn/qSSpd4zrRstUb48m+u7mwpCcCXEnjLKXbARNGz57iEHbtu6q5DCDvRs0fIqXGiz7licOC388nL9bzWx5pTLmBesQP8'
    'vXC64rJp7cHzGbce37sVTh80sm6zAPJCTHmdblF/kUhcvleWc/zJmkfo1bUQuefaBPoXYv/xkY5qrrgP1Fi+hYC5bfwjS8+zRTNf'
    'TmfbZ8F8a2N9/m57TmeI9goOF2q97N7QXAmqdQXHqJwXVNktYtHBaoUvFKfkl5Q9ktwUedkeqqdRqu4lKZfbLoF5AMkC14YeCbp3'
    'S754IDk1adrd/FVgye0B4zF7Gq3wXdWtFvHF2kpfU91OWzfFLyhvd67+jE4we+pMU/EKUvK3dvYp9FKMj9H94J7Uccj3HQgJU/v0'
    '3g+cqeHh/mEgYD+Tm0HAu7GWMmtbX6wDOX/13vjzfxxYbNaFxa/em9P3UL3+OIAxfhE3xg49k58NCK8d7+WPhxfmpv2Gixd6/NHW'
    'fvvnPQxM5W+8ZuYWP/eSV97Z6WGQFd9ZPmlI6pucIx0nRD0JYZ7vkKoCacTk1sxcSDJHkW9cR48wYw3WV7XC8aPqLut1IbjFkdtW'
    'eRe7IhUE/8kUvj86LU0r5+HINI4/M35yWrTzxS4jUhdklvuqWd/89FCr8iwGtKzc5nWcSQ83MTB5PTtacs7FTr1XN5mtNX9p6VZb'
    'NX03qF3H/4nLKI9SnW6fy8SOQjF1AuvKQHu7ANpMlFs5V8+UZQHgQqAkS9DKHj33jVKYlqQPWtmja7jKpljaY5ZZaGWPrnXrmh4z'
    '4XVlj66RL9djXr7VBlxOyKO3VNsMmDBwoHjKUUI+BrjmoDv17cpZWiVSaZM71cZlbuhRyjv6YaaWXVXrQJOAiMx5GXKyQRyRx9wi'
    'fxK8Ee13n6mN8lwJmnR5gzyApbu8nw73o+8diukWCkN47uwkeg509F8xZxm/rBOaZ/34HQvfqGDg04781PHIKIQN472PWEI7HH1R'
    'YkyzgQBt25UxDXZJJeulRCaJ3cHs5kQAUGudGc1+ZE1hpYCxgePpfFIAjYlVpjXw6+2a2RlKYFNnnT6c0BHgJBMrxEkz6v0L8wFY'
    'lQXDnCXH/jJ2dGVjtRzCg9cQbpNTju3vsJGw6ODlq/PS0iUr0tK1JZldwtgTnV42jbVRGMqWMtnnrP8uHuUuJpiw47ncQEjxF/yW'
    'SwaptZPggXuRcKVxNJ/zLZdpQACg1WNOyxycaNFLe/67phQip8YOFD+fz8PFDokGTT8PQFOH/JvwMw1izh1gYoiEPHxo6oGxsf2Y'
    'zg/j+ZKPFCcVELFPrkXs/OWNuaPSOQfMXwIxLQ3R47GRjOSF2SyVbZfcAoBZcS9j95YKZr8tpR/b+yiwMPhCQUlqG5KGbd4obLn+'
    'sVloejvDAvfxnQwZZChGgw1eiIsS8jd1q/u90iZEwuAdgAfZG9RiOUuUWOXtlqJFopZc2QDZ3qpt9G5Xbmo2ne+hZTl7bz5HtbBz'
    'QsaZTd9gmfA4o5K//rVyfsnFxVnQyAz333HPx/PJS2e8V4Kq+rNtz8bP7VFVsfr+4HWXG3XAtl9yJLL8jjgazBnnau2V0m2Bda+9'
    'ewA7UCsb095JSQKR/BxFffYyX/zNP3LmC531QrLvsSQRpo2E88SGnyLvxV1cJZTsi80gMcOCSQpC2rxkR6Lnw4WXQO9h4R5FDqzx'
    'a5HkXJyj7z336Nxa4zpjc33dJOEzmaaEv/zP/+Mv439YzON+7/j5UZ+0kaPek87xQeeof3C02z9SXBNgqAb7ar/39eBJ7/jg6Je1'
    '+E/gWvRdgrItZ8PFaDB+x9e3k4mb9/Y7QjFOl/wIBeKS5shgmsuFg8mE0ZC+d64sbdMyOcjDRPdqi4dBjmXJ3RSyk4udmHePzocA'
    '1Wj18C0nAyWjsz2dUPCZCUnlh4zc8MFe0mJk3O58mZzzA0tkePD3Ur23T4wbHbeleX+COhR48Mrc8+tLLtvt+6ybrvlGBuFz53r8'
    'XDMZbfeXV7kbm0XImf95n5ImgE+bSYpUTP/KVAf9nAHBr6CpuQ8B4mLCDruN19Ibe7flIEm+N7u/1Yi1nZvvPbXuzvTBfQMfScfg'
    'jsECCC/NfKV/rfrIZPNAKXdl2r3Uw72S7LZc5t1uoO+zEE7MlX0RkTevXak+QWNkWA3Hx3B9lDk/sCt+qJ+QXqe25G/nVixYoCaG'
    'mffmy6yrV1l+Km5k0HH1crJjixiv2XgHpWjgUFK8xa3bUTRLwkX6iC8K6WVbT7qrD1XLXuJOg8Wb5zPOdNzUWF/t8CdzWPLFLMMX'
    'V+yO7q8lUbcB+6YkBXm02KSA13axes4gYPFkMpil8dckVjTfoz5T8DaCZNlIpnGcnjc0maAHciNmMmznNc3vgvHYLADE+Ea5ong+'
    'nVnw9mYJ8zhzVBldnnHWO90PJ8ozu9rEz7aKQFOybL/0LKdsk/B8doY7aAKAxNS73jf8QUEumcGYdMZlWSdgCDlHDnnugkGkWQ0J'
    'gsI8mGVuG9JcNGlOhw/K7w+Ra5rzQ/h2ufnl7dNCI5OeHZsktkmmu7Ydr81DdvmyLW/Ye4SPU8uVD/kdoUAfUcZQ/EMQVgZjQgcF'
    'CfxD108vz7IjIQe2q5ynhF74mU2nyVoo88ZjOOqc0gENT09pKwgD4gs2xzRAzvSyrszuVU+TqARN0vcmzE3FuLuWzuZaZLQ4GGGI'
    'qLrfDiTzhvX2vX7q3D4H4LCLuAJquiuaf7MKbONFPO8z6HIw++mWtHKPddOai4/n9Re+eje9ceWc+0j6qZYuoP8V30Tjd66/Y06c'
    '8doL+fF9GVWFEJsB4cqaxl4sgnmOZXDZnfEY+v+ZVpVD2hcljte6Ash3iP5+7n93P9fR9ifLfAND4k2O22Ivq9hcni9gFdu/YA1s'
    'eLg3OO4Md476qCG9CLli7ijkVI+tX6TuNZ9EaU88KHHbwka2becdyx+SH1twOnvFKbBFYi18NgTb+C1/tl54/qL4XF/MHJfof2KD'
    'HvLXxHNDi8ru3B+KHdJvtcU5Pb1nvthTeF3smGThhcSjVMs/aM7p2YmmVkR/1OhgHL2NOJ1esSgDC3GNlX2cpLOO9JPwWlZPRZZo'
    'zJxWDHLUAXH2uw/zbZLPPQuK6UqnrOVQO+0rB+LLn7eU3lvOxhycyNMuu4pf5StgXLsPGseUj5gZqb3p/pRF2nz4Ftnc8B+2Q2WT'
    'sVV9MPVcrRJ+dL/ems2eMBFT7/lbvQA46emqH85Tm6i8sZ1LOF+FN462kKyOvpGJEbZ0ktBNSZn4mTqTXDwOo6HJl818tXFP4nFN'
    'JCzfQgE7P1MN/tG0eZJdhHmoGvaqTrxvW/jiAX3B3TZ1Emq+QzYOm7RVNn3VPWSv+vUk3ZYP792SaTxAUYqq/M+5Y5DKqXmfw+X7'
    '6jN+4+jkpGJcD0xtyEJjB6D4WVS+cBtTfqhzgHIySwcnwBr0522J5J+EBVumwfVD4Y2aJXYTMOtklP79c9GyU+l6zwmeO7ap2M9p'
    'VrLnLgSx9a+8EhvaJpiN8/AD7YOEKi9fOZot9WsNOfWBw8m/NHjoL366Ajzz3KVCTuWk72SxnPXG1zVdzOCiZpKsGdM2Yn+yKNyH'
    'j+uMhmugksEYUOa9b/dUNJT/CKdLV5E0n+TiX+gL54k04nW6NqGxE0JS3IOGfex+g07cYNwPoldMrhInvslBw+0SkvksuDwJtZDj'
    '+FJ86vE4Asqn7hH08rmHwcJcxPgik8PQHSmqcG+To0HuOG214SY5Z7mOawtrfvdJM6dFWGgVlbp87aZGO6+CWFyTzq8HvuW6btAV'
    'M8DVDkJ5HmjzPy+ADisHnhJV6Oh2fuSWnjS2iqeAP3TDXEiXtCwB0TRGMar4YubCxokcqtaBC3K3kU2zl47gDZIQUTe/LWkhIjjz'
    'fFr7o3jJnjk73P6IiGCzJVKA+dSsJidT5g0pRuNfgSC8ejZUlK/eORZmoT5gLf68U/bc6VV3imu2tZ5eUONnQXpOUsS75uaX6239'
    'i/i1B5fPFHR8vaXd+PSUTtILFog6HF1lNyMvRnlSYK6Bkah4HsSldDWf+gBbzssOkjF0+MBy7BgVepp5X9xVI4cWLWRXeWtGi909'
    'fnnGgGcHe3vfOCYBLsw+fP7sWe9oMOz/0m5gg+RyNlKZpMohVVES7kigLRt/Mr/lxyQzstOGDfvnOrZwH7gIJm846u2C8yKz57RT'
    'd+8jXea9d3wZGpmoySnzTa0OR5DS97f6xsRRFgslAt8bR5IX/jrSGLlTZdHhDJoqTlLilu8VF65QB0g7vWqfVi4Pz/HQ7qnNwolh'
    'knSCi0uuip0FhJNtqaGcxfWH8rxrijJqTjaMTkgkO/MveLGHwWSC9W3pkFpZSzTTsLQKmb4Zc8auEJd9WVmL55ykij81Ernfa3Ej'
    'MYtTMCLxxkYIAc0qgYduYF5jwhX7TCt7ErDRgtanBX+OE2aJG1+zFSWT+/DM+Ay81POyN/7sp3ffrL2Ln0Ww6p3ltrSH+Le/i58W'
    'L/yzYeVyHR+1sjhT5hHUTfmA4nCXTf/YmaX0aSuuuJIW2njJXzzvfd1GBHUfDf2bTB8ptTdA49sZa95lTbOy7bWa20LsWWtS86ta'
    '+5Xes0+a/AWYbKvh+lFLL1dGRf925gQxZEUvdP7lbOfLoebg7lBTTEsWfvjDPxCK3hGJuqQsMQCMYPCLIEIS+cnkWTyZZJ6cqASI'
    'QtPEk5fjsJPEpNGknTudzfXNu+t3N+40jBsnyTHfpfGbcJZsYTTzOLkkwWFKHSCmBVG63D0SWKnwHYk0QB2Yn9hwFcyCCbXvqhfw'
    'eD8j0jvLDhsoeKCpQlscwzgY+Ow8VZs//OHvbpOSAcCMQhuJy25pCOuksxHg0hR6V4KLDdwqYLE0E34lCeAxDqmiEYm74h9rUUbR'
    'j/kkTtucC5vLPszDUXQajXT0jsld/wbnPOWUuKpJHwXEVWYw4JxOgjPgTBJPQ4nmIUpAfA6aVKurHnFw0IhYHY9ge5dwGmP4p7ks'
    'A0NOqPdpjCOZdBWRrBPiJbDOET7pJ9RhMCXFqZttUpgkiJfeUi/fq0XMxcKJPeDCbyRYhTLyhuk61Grr25kcleygX73yREaTS0og'
    'f1/ZaBHq9GH35fqrh4y8rGrvxMvJWM3iFMAJF5xlQz7sNhhJxYdyPAa/Q3hVQtLr2BkGzzS1abzEtMxJoXP2Sk9UOpTJ0cYPUYe8'
    'y511l7PkPDpNLZJH4y2u5E2vL5otAyxMd8sOZZ+SGrtVVmEc+m2xwvh5vIQDxCapjWcRmAVJ+Es40NpHBEHTt7jW1q5ePg4unWrl'
    'bVvNnMjBwun3qugCIld5+wDGHrtT5Pw/cu+rnUiIHZ4E0vBQR7FU+JIUW5peCz4uHkH74e//QbHYZ3GLdJKQMYM7s/zX9QZfWE8z'
    'p6cM6xZ8n0l4T+Shm1FHXc8UqDdJ5A4Uo5sSDbFcgwqZmAVv+Q64+jr0cbzITlKNq9HMqsGdyQI0syioWtykmfkbD2acnN/Ky2bS'
    'RAv0tO2Es1P0IZ40Fb40HyZOr/KO8ySL/uQDXSlLxT89dn2PhFJHH50QrsJ7x+6EZLkotxmc+IkychZO2cJM5T0xST8cDx5/GLel'
    '9c3JkJDjHpj/+i19Vx9Cee+1jp+FjMDKGawjDhBgIErSeH64iOeBZNlsOrmXnE3MxJjkZaQdCR0jC7/Lw8lZdWbmOVkml42W3yS/'
    'iD9kixA1g7P2ZGyeznepcqnmEdwxiYUv5/Z7/sRPcMNchWWmCh21agXGpFFnEc5OXHmOJ64BmT70zF1XbAzxyQubRn7hlpG9gyd7'
    'g/2+etLf7x/9Ap3Tc6aRTFSfB5eTOPAKFC7CZG6F+tMQPLFxK5hHt6Z8+tvGXZUk0Zhkn8bhwfBYC4lSRS9B6dKGxsUO4sEb1IzQ'
    'jkgBn/Fbv0OlQXWlY4u4GlouGMzMy16JuPbusZ0e5tpFb81ML+dn8RvHnD2mn4b5peeL+ILFpP5iQQTXtNDSLb4yj0I0YJmTYWX8'
    'itQpiez0OsuWpBmt+U7C5660WwrpgSxyP9HS6jizXfreG3vS8Bnyy2peLaFdx/HwchbPkygpaGzPdQ0s/a1O5BjNlPlC/Vodoo9u'
    'o8xRoWTISoau12EKMD6sLAzJ4+QQzojqekBbTH0FcKxUwLar+9dPjBs69hn+7V084UHJ1WZlUbOyMhu5GiA29886J/+Rt+hvK0qp'
    'r9H22gOIgYJAtB0LrWtwnQ+RNYjdmHvTOvBfhARMEQzc9FRyfeLYVNC1VnPYZd78Js0goYmFzXW5K1t3LVqmkbYP2Fuu1ZC7AZw2'
    '17m0ygvWwKHOGrOn1vbELqbD1lFYiu2XXQdAHw4i58bAjUe3MBt+MzzuP0P9xFX2BkzW2hoM3tJ7kk9pi28rGjCNCO2VwW02Bugi'
    'cdpY0VWf6GBOxgNQLJpBiILNoIMqnk0kkG0GRZwOaht/QdfBXRsRZdLnJdPDJHojqvbWJ+/XzIhrWy/pB+dL2VrbC2n6RAUQ7Xu5'
    '1mY0p8fdbnftqp012zHWig4Bq7rZE5Qo79CKYFLONXt19QkkXrNwNV1CTA3F4qHNK221efeHP/zdnXVYOQinSLaCn7Qt5LecBFuq'
    'p17SqtPgLJ5By0DNNYCdCMkr6fTlWRxMbtGunRImp6901rRbBOeXSQozyquu+hrqHpu6p/PzIOFKZelFGEq+RWIDYSg1OOeLiBSi'
    'lISwhM002jCyJKEdryd0YhMRfzOLTgT6wJ9dSiuMf7aAyTdRXMYdFhZa4mTcRaYGbYLJ2X2SfAHB7uufzcz2edHMJvh/M3MPT9sx'
    '8FiqU2rhWQQX11h39BFnYxSyleqEBRlELFuYAK/vo8vMoen169cQBr6nf8O1KZfbReku6SuWNvhXkzuyCa3FBvBddr+RlxccSwB/'
    'b7HdHOJulnq6inbqRTZlOl1LKAgAL185BZgnxYTCXM2xlmOLjOwrfS6rbHjNnPllmXndnEXmU52GCbtNx/JpOp3QPKUesHYik3K9'
    'n63uhukGOxVNJOuC6cQprpjIHrIrVH5AfF85np/UyS46nl+CKThZnSaTHXrYBP1sEaP+T/9e4bdN6/TBvfbG4+OYLUy671yZMWQo'
    '1zVSPzOmSm6eDe3uTuLpbHiS81EolaOMQ0WJYeuj8/O8eYwJVFftnIek/DOPG4EqiTAIGzUONGn80cxl7Vef/Gjm7oq4eneh4zrq'
    'TSoyEVRmuXfRoxR99RxUhbzrKtiWVM2kPEgMx4NofhLjLPH1AotajKVdyDIl2XphhdMTKXiHlSr0fwfsjEJzcgtuUcWPMARJeXeN'
    'hbKVB5CDqDkwSbWZm8CJvygDlBb6ndScvAcfbxNWWujL7PNinW+8NGoTSSR8OyeLzu4BUmu7/+ks9z+F3f4qK7PxI2z2P4XFvmCv'
    'v+4sVJyEHuz4je1Pbn4Mrn751qzdQW/v4Mnzvjo82BsMn/4Sg33m8SRKzvMBFflIm119DX/IrR1nVe97yxVxnZr/pBCmvVjOStuU'
    'WD1KmjoU9uf2HjKuqjKhH5Fiwr0XMd3ZqxFOUeOOoV3LmVCsF+dt2mp/Geu7U7EI5+MeK+Ewppg+xF3hrrFprAxfMd90BBN8g1Yu'
    'yEhcch4tI8g4HNJOIgdfgBFptAvwlf3eIEtrbj6570OfPVw4gj9iwtWMOGkd+E+X2VFY5rPhen1s38h4YWdqzRdoyulFF+EoxEkK'
    'rl+fdaUwtoxPBmOaXXR6qVuwMwPXn511CBKdWUxnp2l150QlwSV2zZhMjA/FpToNw8mtKfQ6VrdnuGY5EUmfoAp/DGpOi4mTiPDy'
    '0uuUHk8IeblWODwkEunyggXTYCK5gd6QDNBGX05rVvlJ/samkf4cQVFvdT85EptuHXMM3hj3LMm+BWMMfDa0JYbAsra10V5LkI41'
    'Si/XttaS+DSF+SSa04+DDFBbSEoPn4VwGjMNkbTjk0uxwnBPd7yezrUhhnvqW+BsOdYKvdqEbWkJg46BcxITlAETtt2YPpVMDrng'
    'SKTANiATfVvJSLiI4wzhBBJ3gwWoevDuJwcAGbutOEhBgvuSftGbc2SVA8QJnCTAT2EkYXgDWxFJwt8iNT9RJykdHWaYSHBmrb2r'
    'ngXvoulySrxdPvgZDShffhQDyq53uqwhxZzCzFT7JajaT2hVKTON1LKt/AjTiZDeSssJku+BJXOO4vAd21XPZJ+zFG9V/Go8OdOk'
    'vYMv2vkHnXM/Z2ToGVvKSsg0cj002o3yPrNKZQV1xvmADiyYjkl2kyn0zs7KIdCFe8Zd+clWomxDR8Q3U4lB5spIfAzMqvgEFoxI'
    'Ecf180uOSEOXxHc6asN3MZBwIpdleXfvLJL4sY4F2IGT8jiWurDCwIBCAGMpBBHLmAe2Wwmvx9YQ0snmivQ1bT2eRLaerUnLOK+d'
    '44Ta+pay3EYhBnPVMpTfPluGP4SvlnCHmKVzRBl8rrWH3mcGPWz1Z5/lUCUvC2eBNKYOxsr4ID1rauU66dDP7CDTj1UR2CvvZLLu'
    'Ozx90A0PCvzUO/eSH5CxWsuMhs5mwl9GN7nihViDNYueBr8jbsQHwfXPWiniF4sZ+l5kwACZ02fYbZdqM3LwO5ruxsNGY6uRiNXS'
    '5VjJEsITzemMA8mcWV1d63ymJd3E3Dxru1pmUuv6PX644FsWu32VuzcugaBc5pbrZB+u7uSy4/3LI/iFiTHNtzPQActeujPriPOJ'
    'qndkH35oGoAPwIWrXGVkovrBBJda4eicyxOQNDciqYdO359EumNYRtipmgWhhBXMkzDlqmokmyzPuIiCehGeqKEsonc4UCesY0h+'
    'b3QRnJzAgsWeK4k4WJ8Hc1YdcCiWUhyanSVnGiTzgAS9pOtEzqYLDa6I5Co2K3KYgmA22DhIIZ4bbbPPU8AV+DSeeX7u7nQg6+JD'
    '59bkZLB//G332+TPb51FbdUY6JtK+rNlLjPc1v3fuq3771a3lr5v+R+ZIdR1Xx982x1+25WP4tNTZZJHlLX9+tvugWn7NiYhWEla'
    'pLK2Owf7x41daWvK7o4rmj4/VscHW9J2ZwnNr1ve8nFvt6+ag/3vD54ff3980NLfPA7GofrVRsVHw2e94VNFg+jWw2lAAu5omXar'
    'Zz7Yf37wfOjNPl4mmd2hP+2MqRdc+P+7v/VRDDRyOg3kR6sEGZI/f9n54Q9/R4zx1We8XzQGdsf2PZlE7CaErknXQDwEd1bSV/f9'
    '7avvf/jDP3An3W7X6aa3t6d2eodDudRXTeJdy5QDOLkQyHicXcIT5tJA8QWdQXacIF09xZEjeWwkAWjUX/P4eKjC2RmrjlDd+TWM'
    'Enx6EQ3F8Z5LicJIYnVB6mE8a6CCJeuaur7IgDgPPkcSR9zki9Y55WlB6yONcxYyPBnHEpMbbxTME3hjmGnborkgiaTr0tMZTeeE'
    'FOw3YVpyDF82W68YUBmQdkjnpG7hK5IuAkRckZ6PZZXt2/vN9hV/r/zYHuzZLEFxUBuwEs6Mf4JLjwgmACLBHmXvDNYQT54Yyz6X'
    'sLv1svvpw/arX93qomZEM221EHBEoq0OpsgCjq5+uQGyXx8Mdvr0927/F2Yqd7j1s2i0iKW4yS3N7Y7CUXw2k8rhPy0j/qUiDsjI'
    '4+dE/HqHhwq0nBgjCf76Ikb1XvSOkPZ6SM8Gz3pPrH/x4GD/F4ZpGaLthimiSWxkHExebLETD/fJJZFojmATRyzSdVVdYU6PIIZ4'
    '9hhDFkS2ecF18wJGZ7HFwa44nafqx4qPesQdGULNYSuXG84/tohbnF2HOAIKBROD+uslgi7ElST5CSeqPZxJSbWOJ4NpcBY+X2QB'
    '6r/goz98Sud7Vz3t7x32j4a/sBPte4qLi3g0Xu0kHo2v8wv3Xd6P4b1zRAKaNiGk5nfXZLvKnpzg1O+J8/i21zZYpnEvSaIzHQVA'
    'ypYkB9oJjCsDPZIAu+eD5mq1OF2UebizzctZhg+c6mUguOmDBiwB3S8JvVadL/Xs+d7xoMPxOMP+Xn/nF8cuqw+dDgidTnQ5HrG9'
    'oGLOy1dtY/62lb7Ydh8KMnGGiN2DZ4qz/eLT2UhX5gEdbsun/MXFeUiMEmlxbklXrC8gZRBXXTT5crbEgtfmDx3ujRTF+jvW1wjb'
    'n4aTMY3ktEdlHHa5Bqs/R1AKaVOE59FpRLO78opiTCdPQqTL9r0japkJtXoyyuXCq50D78qfB183GXPmdNKV4TKHXBjsygyF00nH'
    'KSuGnwJ97RPBXfGDh+Ufm9bb3rjKFu7IOnCzhOKp2Swvqeh0IsTuUTA+CwsVyaeTYZgeBTN6BWihskWu/Agno8p2JbPhnkaca4ua'
    'dEkDD98dnHIXLbeseKEFdW/T1ES2kgT/VUzqOIn5e5vP6jSi+UXOAOeR0yB45zb42DtmDNlYjNzDTuI2JvCZLglYZ0DmHO5omZtM'
    'tqs2Mts+uWbKxu+3rL0Z0UWqqzpo4b11MOIET1ammJvI3U6HWzohWPy7uMkzwS8DO+0g9JkLETrQKM+RBSfNpEbje12OjPrN3SPN'
    '+MZF5AYLp22neQ5CKDmGsgpFD698c7MB/hd56O3SmCaPbDj2AJjG8tIsm1fIQz1UL7MnbdXtdjO4yFU/0Sn/aZbMVPeaK8JifeGy'
    'LFeBmog5WyXzONXRMmqMr4WEZye/4uDD3jYSgcyMatPzuGd90mp1T6MJqUc6Ez9qxay3ukm8SJvNoH3Suv8g6Jy4lV1kMnLMXupx'
    'Xq6/wm30Kyd9LKeSN6SF8702reMUjWJmaHrQQOlsvGIzl511NBtNlmOSIblOCriXeZM7wd6tTMYacka4gK2KcJSayWUgbQISLiYf'
    'eO1lInCn2jnJSVT18FqmZg4Skdd1JxpW9+VnrJTasfdhH8SU/Hp0JjFSdh3MzVtlFdT4TVbqjA2YO6SIp720T5skH26j6tl68aTl'
    'iu7IJtP0BSmcvCGm4o6pdVM5nm6ZlUguOByL+v6CxKQd0Cz34cqaNcYSyrfrebnhcjQJEeicNLNbHXP2d87Baz/a2Tcd+gibCGph'
    'DjgXPIsyh2uvpumTSXwSTJRN4rklUqAr4v1MVo5PrksaqXOMOvkjOPFcVwflfCqOAgVpQgr7EasQtGFtLUkfdgvV+9xsyE4GvR1E'
    '9JCkTRjP2du0l61wGdyZ8HW4smJ0lpekbMw/yzPKlkdZqgol044Eigg3vCxpu7i0Bt+rCKdEmqUwbasFoxm7c8ILkUiSsglKi9Ki'
    '8RJxRUuuZCS5/mjkXb5PkQVa76tMYbikIyvXKHoMGVpOkopS4zSbAh7w+SJuHTIXautOY9IKXMhpuHHwxlfhpScUfRyxLifYiXB9'
    'pbNJrxShrhB7MQrmtDukjgF44oBTfpgwmS294J/7NH1SM2Ft7ih96uEHp2/OMIN+mqOW8FnbcM+aETMuziNE/+LM6byaiaAnbm4/'
    '8Z3KzBy19vqYtIhDJB9r2qy3bZsA9xtX/Edfe/pYTx7WONHZF7QK5/P7LkF2jjzqe3MVG1m6JHD0DrmctB+FmyvQsUxQL1IGV4tz'
    'uYhdoMHZOU2DTQjX4exyvqUMuv4Jlbn+pFY64VXI7KJqlcqMq+JT8fM2kJzFunCIr1IwQvB1ciCJPTU1c3U6T63xfNhuZAnwiLNb'
    'h6kMQUgf8ff2GHfTbIdh8wu7lf+Jli9ftcdvwssq3k+vxA2TFtlwTrAwLmSj1aYpxQYvbJw2S8ktP0ebxDOclq9kFIneQF7OEUl0'
    'Jh9uxsaAD2EDTkDaMucQBXjroPs5SbzwpGbpAHIh61WezS5xU5SZFzdTiW3qfvnY0Y1XJV2HRFOckg5+4HXH4mqvRyz41Fpk9JlD'
    'NnNdN8dPxppAsjj+5rD/3c43O3v97YIzMose3NJqktqs4aZwbeUToSOI1Hz4somOOH7m3+iuBIh2Pr6c7iSrdRIK9xZwWSfESgz3'
    'zjaYAH4RSuQC9t8I8tgHFxm5i12grLBN/8XzOWEqkiQXxJyVAC5kYpa6KJp3uf7XlvxZxuZTEfljW11vNtJJmR2rYNE6YLXc5cK8'
    '9lFYw/6hqgDRQxd3Cl9Dfd/yscu4UW05y8rNRMrWuWaJrAZxDnVgc9BffFY9RRy7zkbrVQZhxh4CbclRq2TNgnFefWJnwH5C0qVk'
    'yHZ0ApD1ayVP9r8bhaSXQHZhl6Jb2uAEw75HedQfk2z/KIrn0bt7ajNfqdiBpQVD/ggKVCyvqCKUlUkJS8x8jqrWm10imcyMr/+c'
    '8CtwgrHsR0ZNOMGRVDfFLiFKRlNbuxhXgthgMxZJxOliQkRD/5qGaeCQkI+1HrnB4Yw8THZEphfrjF4IabaSERG0Ml3Eb0LjYza5'
    'LM9O4Ca+zBCHN18bkx2R6GFX270SZBL1Lm6y3JGZEvEuHO3AEXJGJExgivQLKDMhN1IMznz5B2uRqjxivzjXBXUIJ6SvB/0X7O02'
    'lOvWeIwgNdf3VH2vGpyZn/+C5ePkEv9s/CJDyYOz8GtOZWAWve2/2DknHXPWA/qjEFBZuDlh+6Fu3YRfaRtBbWm8cNQMp1KSfdda'
    'NYi10DgTRN+eNwGSJ1ohqdBQ6JLoCiarr8SX0puX7o639dLb7m6/skrtNJ+8JJd9thCh8BYZWjixz9SNKkKOET+lqQTq2yiDtpoy'
    'vcP8bc4SWcYxlHCW0r14QCy6I+XaASzCZSJHl9gNXSFeOsDw6FRn/s8WaVUzdjDxv1O2HsNhuEhoQN2RSTjSylKPlGxS0fSa2YwL'
    'g1ns8DJu4KZg/AwXJOV5Nux7vcrywnPeXQFK+Riu6wSj8OP8LuuibfJJRaEMrsjmZmTmomQlyZgnI+7qLLyuKp6fLHqU9WVYE9fX'
    'tHUxSH3heSbhmThCBKlkrX4bLZDxviMYAvT29C7d+r4fTamLwWRPHb+Cyag7QlDePihmBroZo5XP4fAsw3IuqeE9cfhbcZo+mzMz'
    'lSIbeoJuluTClO0tS/lMmpVTmRImdYC2DS6EWtkOf411Q2+uei66Hog5w1b5/CoM5yw1PHq0ozT1EXd19AXHfvZjpxaRZEUMRct2'
    '97frL7HO2FeFVPamrZawHsBCUwXnzAZg3E6Tk4QrqjmXezxvUhkSaNCbMuGT+J2n6vMntXK3oWUuXbce0pQ4gKGiCYSNOPRXwZ3C'
    'LkBWhYef3Yeg7Ef/QsOtmUGOmhanQQ/NLIiJmEFfRq/aKvsBTfxVxj9Icj9rq9/lkn/raqlnxcTdmsnE7+rOFGmE3xXnKmcqfpdN'
    '2JK2s/3ltH7v3LyifwnWb+Qb++4Jr0Hs1a/eAzK/A3SuXvtz9+o6ooOWM2cCUiW5cXMixmwY1+eWfoBSNSFIOEthZEZcnLRPqPms'
    'E44jVlucVnxO0MJkFejrNi1V+hgwYUmn4Y4lTfPsCGSo/E2z8VL3a6b0qjJoMwvdrDOTKw8GeZDzbJwWbmscAy9revwuoy3ZNvGp'
    'ddvRd35GA+Z+Rloj/LGxso2NRkVZUHRamrytTNLxnXNXyQBnOosPkFhfLnvCwJmDYkWerTszNCn78AJfXeRDWrXOWL56Z21SsDOF'
    'uMMz4ARj86yCDVLWkWxcqOGpOToELeQ1MDIZkKwgnzFjs3K+SScAuz+rt4HiRGqYcnAJyyhoLNwqac4pH48KxVbsbhXSfMtTEHii'
    'bWWP5RWnOnLqEP5SfV1Z3Xxy1EP9QfX/k/euzW1kWYLY1436FSmWWolsJsGHRJUKFEhTJFXiDiXKBFU13SxOMQkkyVyBAAYJiNKQ'
    'iGh/mQiHn7Ez3rEnZqM/2GGHw/vdjnX4i/ef1B9w/wSf133lCwCl6p3u7YeYyLzPc88995xzz6P17rvv9lpo29si1TzJJSG5vaOR'
    'HcpQbXRz//OFBqPt5TDCHBCw2wdi9Ct2Ztr+FhndhljxDsfdeL8jv3CzJ+l1gvcNR/Ah5TiCrXhUC0LziWyO+NMPgPb8GWUlhDLi'
    '8lC1N9lQFsgyqt34vD/GrQcjc4x2U1ibDnT5nRo9rFTNGE9oWwq93/EH5gEueKnMOYdRrwNcNkZAlLiHj5+qYOVrtjFaRwwVMu3k'
    'kwtnZnGSdE7ZnqvgQ1GiYUJAmSLPLvS+VVEEjQ9ArpQLA7pNp/EmaPrVI01bQT5zDkxKBYtTtbHZnwT1wb+Kf33uPc2qQy20qruY'
    'UL+KUh5mwRg4dV7NgW42yzWHqLwh/woleBI/KvwloAVywbLRfzp6d7DXCmwyiSXq6rpH7PHYYkkJBdYtR+FECNtpItRW0nGqamnu'
    'GoNqmPCwIb9w7lKxC2pjEKFrcc9wy6qs/ZVUjRzWdcMuRn08eEDPTjgR3bykpfeBzbhcUoB0++KovbislOsW3YAXlwMjozxZn6Fp'
    'CqealjetW3u6Ut1a1PkQD8+X0J5gnMZWg+TKjJFQ2NmbbXrwKtXvfvJN9DeMTI/HKjWTureInQ+vaVSpGhUNsrb8L368uX0STrqf'
    '/sXyZRLYkY7seZjqejZN73H1bHAaGJd3FPeKphJ1/hWLmkscUF9ifPEMxUQ1AkZ53PNq0NInj6NHXMXjIaqh2oFp8KXk6qOdDxjq'
    'PVmE3dDwsFqInnl4yg0pvWdIGRDQUzIkp3AQPQBii2Y0um/s2YWh8qVAENYcGNIA76ijO+7nTjd+B/ttCIz1OTyOEaPhL/Ah8G8H'
    'RHP4E52n/e54hEVH/RFq8+/a/esB8m/wOIiHFxSN7g6qDqmV6AadMKE+uunz48UQ4wjEaHQKv+Bcv7ykTIrdT4G1rgqxNzKooaee'
    'ndePN4u1rQZ0cQd7P73rj9M7KHcHJPIugv8n6dVd0r6LuncRTL8/xLl04zs8Sau6NWhVMyC1lyBA7FpHXtIk7JT9m4taJI2pKJff'
    'GdJFFJWPb6FCTmTLrD359NoW44vhbZNe1D0uPkAMdad7MO9MKGrj4W06hqVJsccDOkH5WJjAF9k8LKTaJFiYE9t4xv4sFpfKjND+'
    'xKyLIqgJHddRp9PSY5B4fDBKDqH3PulhfiFpQ4LwUYjmBrfRBo7xEqMZ4uH0nVMsgRlLKXykEj//09+pRhCcX1lB+qQoxo8OVdLH'
    '7qcDq6+L5CP9pJZYYmj3h0O+zVOdpt9HXYw3zdxDdiEId+zFsrpqeCpSs3SWUfjiDbqjPck3rqvWst9M/oOMtXQ3sWTeglSKE89w'
    'mh6IX7t8/qoJVvAYaE3ADFOB6Ip8p43djt/XlRu2LXuzIH0uYTlj5Ye/AqorWephOBQtx05kPwWNHdbRLmv45D/D8NE5+ax1/JuD'
    'Pe+Rt3O0/fLYI+aN3u84bvbE80pYz14M9DMdDyn9CfICHMuSanlL3jZxAJ4wEl5tgDlmiJ7pZJwOq8gx/QJVHU2wr/7D/44pU0j3'
    'MHcDh+bo95hwz93EUTyIKauCyRIMp2Yb74uB6I+7o0RaS9tRDwPDoJ2Yrn0cdd+zGyRmkqku/2fq12oFKxhGF5j3UBF9AEiE6lPS'
    'AejcSRRlWPYg/MWsPcsYaKzb9c67YxCwJAKCC1o0wRvqpdIrxNxoOmKDP4ok2yerfkzzNYzryu22jUPDkPUih/80ysjG7vlMM7FO'
    'L15RdSaFdATBaZ2K503JUdfwzqjfytNYNTo5c05Gquieiz5m1kKI2N9oJGUHHwyw/PSyBNYiQk4kk+BwlJyfAxAVKcf3ZrZ/ge5a'
    'MtqsD4oKrcE7AXZ3R2TyjrdaX09FLYchJoypSeDdI0oFdd+CXoiSaxkwp9HYUeXsuWiNgtuKpZRghWHTa7386e3e0cvDo9fbb3b2'
    '6l10AuEsSXCEY0RzOFJr6cXexQXzlyBIv0VZGnrb8tbW6LtO2JEfdE5FkV5gvvP9TjcGgaenBx96q0+hkZDHlVk2u+AXDElf5H1z'
    'zxDzlpcsaU7SjJPjhhuQC2QMOMuHjINKZhrGS4RU4uKYR1XViGDiaj1DTv6ZGksbKfMGbcieLhK44/aY7hJUSMdlY3/GxhFsudrr'
    'qzNQrM1wb6g6R+OeCiSMrwFN2PvI6EuKrh3t9YE3i4uuRasSSfCG0FEpWe59zOyqYRQK6Jy8nmNNxmlIHkU6Zx0cDm8pjcxVDMI4'
    'lFNBEereNkw/6r037WHQOB340hvFINziXQGZdhPeIM5gSHhg1C/pRoA4RA/YHkSluh38WM+rIEx/RpXlZkYgSIvPmoGyak4H1TWl'
    'ddRfo98QqOl1JmNHeTmwoeE7N8DWmPKN5RRT2UGDLPzUMU4oOAjVjELPH/GGWqINhR5Zf/j9P/zP/9//9d/piOr4n7PMtgNG4OGt'
    '1SkM82ObfB5TnRiAB1rH4wOteJBJUNynztNcP8tYAHg5TC/C8ZxpAYbcoPTOV5K8cxinaP6IoaA/UbKB/6SBZQxgOSwxmt8AI4ap'
    'I0SI+6oYNKhTUU3aUY8/B0S/MHgm7pGxVq8UDf5jHguP3WPBIvqpePkqUxsvRYMGVHUquh8P0D1aVhlNGQc7Ksg8/fqsUwExofA8'
    'IMfCYgqkR4CK3qk7SgYI2KGEgSW9Jowzf/9fuHvqKC80MOaojicOMHNQXKCSCLTJgmQepaR3GL0Jc5EUbC4XyBsOkDeKgFxAvu1T'
    '1uj+Sg4ky6aOU6q4jakAL8N0JOPK3UScrJxaAU7/Klr6m+2l36oop9k7Id2ZaRL9WNQPc3O1lru54UgxeiCAFQIss/IKWupYzKAJ'
    '1vkj4gnstc9HicyhY/BDg8JBklUHSVzOQeuTHUFLM0sYphkoHcne39cP66F3WG/RvzvwLwdTrhSxRF7e+8vjn95uHx/vHb2BIWCw'
    '4R9rJ38VnC7+GMDzw2VbYGarfN1zjf1nFItvuTdlvJ0KKIRheDJOyCIMONbBseqRwWjFtElJ+Wf1ZG8ZhebWFAXLYS+h5jRguldY'
    'GxPZYfMYj4bSOH0kHXwuNIapXZwaj018AWYvOD5ATvI24PyysCyf1+fB64tCwP3mhCuqzHeBOkyd7EKiFBUIr0mKG8adMjIspfDM'
    'MOOUu9DJm5GzdH/wgDvRI5GfrvjEhL0E8Dbthrev5craujezViTrsSdWw7reln5ESs+nhlwAqDhKhXI7QZTysSozMPIOyGadMXlX'
    'LxEBoP3z8QhDHHLeXIx/KFd9PpAR/3Qx8Jfh3cmqloeqPAeW2OHnwQPsBq0L1fyaNMNMcoU/Zy1+XqP/6vDYO9hvHXterXXg9YDd'
    'I++44D+poIotTHOsTfYcNn4X04P989T2zM798yx3Dg8Oj1roC+AjC/N1/M2T9uO2H8LT02/itTV8ulhtP1m5wKe1uN3+ZhWfVqPz'
    '9rdU7vGTb591zvHp2/P1b8+fUt1vV+Nn9PWC/uNbkbmox5/ebL/e427f4HVb6B9hBBb/kEJlwMNv4m63fwMP31HKh9A/jqMu/HnR'
    'HePnt+PhoEsPSQ+dkH7A4PjYi+5m++DgJ+iK+qCtfIuZfTERrh8Ke8YqcP9r/YJuV7s30adUvPq8SWjVpTTXUljq7livTF1WADl1'
    'OUKWU7dlvaquiynyKFW0H6q61qvqusnf6D5UXetVZV3kjvAcxMJS97X1qrIuLGM3M99t61Vl3S4aJLljPrBeVda9GKTZ9X35tmWt'
    'cBWsUIrPrJH1qnrM/XbEN/tmzNaryrqdOG1n5rsbs3Kbq1fgZGc8zPb7OunNNl/Kfu3O9431qhrOki3Lqnts3kzBDWLIuKzUdbZg'
    '0XztrY3n00+t/d8CAeFIEEi7/L2dd0gf6F/65zX/28J/DvBf+ucH/GeP/j08xn/fHn4P/+6TvAEP2/EwAUpjESzq7vXh93uv994c'
    'G3pC9BJtxSmttv826skf7yDGmzR+PkLTJvXj3UA97bKvOz3v66fDsbqB84+T7kjK06OqsIuJKPWD1OVnqg0NjdMr1SaGu0fndt0q'
    'SKHv9fj4lxlhjB4CUVcNU/1UXYM8DCwtf+Rn/sJNv4p6HQwcw1BBxWc7QlLr/7bfv5bx0KMMc3vY1gPBZz2Ml32m/GrEMHwQzPDL'
    'EQaoeYmMLf76AQ0/BOqPn674jCTOom2/+e6AkUThyKcYOv0Q40ly0L/xhCT5r6Bz/eNFMuz86KceFIZfu2NgMZd3oh6FCPNBrr42'
    'H9FUABWHOXQ52HvTcnpefXYN0PDXntCfx+v0Z32F/jzjX6sr/HNVvq7J721gwDCDDOKZ/zJJr2Lq+3XUHvZzHQOxk00kHa89wX/W'
    'sdMV+OfJM/jnKT6trq2omWN6D5xcC3MjvqY8srmGW4fv3uzaDbc+9XBArw9xE23vHsG/3x8ihNDrjZZNzmPDN7X+GccUmpFroqth'
    'SQ+rNdCjtOHpkNswXSRzHFMRDhX47N/553Rb7VPYRlHgXMedJCqqiAx36KWwKSYqNALqJqATJSCxBxnG3PY7yWUywg2Bfi/JRzhm'
    'tQpKbJaAR8Gcssz6KCZGMSQOcyHcgnXwq3NczijruFEngKbmpzq77XggMY22x6P+X8RIyU9OjaJJXRf+NE46GldX9Vt049rv8FtW'
    'dfKNyhVFoiUdDZRg2wwKhK8qchxZrsjpMek1TfRl/jUqKl+Ta5wx6aIv5EUkw/LRDsRU6oLgiHjvmgQ4OP4q7g7QJPRPFL+NuiTB'
    'mMR0ZkskUz/tUupKXLfFRYlMY8whInTgovKuWobvQHQ5kOWJ8VWmH/czJSgzJtD232LpOh5l/LU5le3qxvT8kG6o3GKHQgq90i3Q'
    '60hAXBwAuwfjzv7YwH8WF9lDB71yYooKzOYeYsMTd4OQ9DGN4nTuIQZEnDjqCR1rFnrTl06WJvUCteyAsNHOOK59iMgeqkBlJD40'
    'VIBTzAbOVQAXhs1Na0Qqo1H/Hf5kHb6l65cUcqTqX/IDO1HZospSZi0jtamXUG8q55JBqarEsSLFZVDPEt/5RH6fBtZHzlPGPbB2'
    'yE6fK56AQPaU4pz6qZ0od+XlH89rW429vzw+AvbP2zk4bO2dLHmnW+/e3gHDGfx4voxZEIHT1ORPqrzY/84t/kIXf1FQ/PXe7v67'
    '126N17rG64IaTlH64R2+udNVyvs4OHzzHZ3pd8AWqw6ANy4pziX3d+VB18hXUFD6YX93j0urN6ZL4LwV0H7It2BqWjVax9svDvZb'
    'r/bVmx9ad3rgBY1Qgi0q+FKVKpgd8PNHCL3jVwREKP/uYHfv6A7fe/DSM2+OVTMoMGTbeXu4/+bYO3xJUXLuQJiQsihWOGX3gSM8'
    'OoYaNLZgi4uJ3OGU3N472t8+yJZUggmXPHU2pTqwy5H4h1f7b723228Eaop3dvqFz9Bp6+4NQDrY8g72Xh7LXJRQU1X8aP+7V1Z5'
    '5uerKrx7a0qDVFFVdPfwhzemMIkdVcX3rcL71UUP31ljRtGkqjA8b+8cHbZad8eHdz/sH78KdF233vH+wTFVdGeqhLqqsmaqRu7L'
    '4dy71ivcby2a6x3KptgC/VJDEikwX/XgQMq+2N75izvrN4BCV1Zyo1N9FxNZ6Y64qBZDS0tqCBsp1Z3/0budv5CyBuUsSbW0tIVx'
    'tijrruDeLhIQNUeNc5asW1XeQjxHHHbq7Bxtv9nLdKCF5dKSpmlLmHZK//bw8HUG3EqYLiunga1FbZeyHO3kIK0F8ZKSFpSNnJ5F'
    'q+MjQCZNoOmXhdO4Ve5eAk4c/mC9JeKmlk+kfKfdbA0uK/oBp+Sr7Te7r/YOdrmEVkU4ZVrHe9u7+zvbr7mQ0VE4pXDk3svDnXct'
    'LmbpHJxyj5+uIIHe3fvuaG8v2MoSa1RIFFJqkqfKyTTM1yOthZxbWkfhTheWxC5mqS+yC7P77njn1d3O9pvjvd3AruPoNfLMy9Gu'
    'v9Xy9n6zd4fPLXjgpVpA7QjrPxZyp/fh0WtVC5+tWqg2KaqFp+0rWJcs/IxixS4N7QHifr93IByE1uYUgrqTiLcVGRsQy7T9eu9o'
    '+46gwMzS8fYP27+5ewlr+Ns97+URfL9r4Rq8PsRAA3fH+6+ZxTrYftuiudjspMXBEgeJMRb1SYw/eLHxSY8lw+XaPOglBUSkwN7Y'
    'XKhP9ZCxJrRmtMV8uLoA/cyJ0bXpCoZO9f1TgbdKy/Ki3+/GUS+o/6t+0qv5d74rctx6JWM185nkZRJlO38g8rSRBR3jeUfcViEo'
    'szJ43sIdPmLDGCOeRSuUmh6vrQQFA8mX7Q/YzQQjGPwiIuot+xA10DiOjRL4mYOg4DODTMUIQemyrnRAgef+lkALFh5p7QvqJyS6'
    'g1unntfQiK+rax4wUGFXsZnX0UAJgihHk4DLgXNXMm8PVJAGV5CbV9Jmz9CsUYCOAFEgOjveiU58gsrwBJkaU6MqaCv0nLRv2Y8p'
    '8CxqZYN+reFjolBYjWpDJzdUk7jiUgONh7dc1Q4JpRMeROnrqDeOuqRlaaHWrKlwBjWVdXQhr5E2rbnpxEXCd7YKAxWXRLzoAybN'
    'hIajS8AI5yWgj9MMBoyjj85koUX7N4C/9iBXCqqad4Rcqhr8CAKrGyc0E6dtyM+bhqlRnaI/YFjXIBsPShAd9wcWCDPfPU+m2SBX'
    'Y/7FDlXqVpeXI7SnGOqBh5nWUJXaEGtJilUCe391DX1vkJQ2SKY1BLVhXTIRaUUi7bToxqmafJV/cqOlTWyPhBO1CzCL0wijk+lD'
    'hl6Nz8WIHX/xheFpJggHhSthvHU7UoZDuAMzWignIgbTyXFcXF8wH74bvEcXt3Fc12eM2Qh8GlcvevWCly52m0a/1B5PXfGG2f8Y'
    'FVE7RFes/1Oz/jwz+1Dld5kjll/SY0EQMhPCUBNn9lxtWseOId4aJIr6YijFIpMsMZN0SQqp34SkeDZh4A0MTakXiCx6tNObsAiO'
    'aRZTx7jt4htVpGsRHCwgcYRs/FCzCLKhBdUHu++yWIMXCUgYFA3Ul7nhDuHefJUS7cD9CQiBz3Lfr2wzbDsLuW85dQ8F7ospNz0j'
    'kNRgT+jNKdln4ozld4bMSRNqeXUrt7l2nFY2MtRFIY57rE2jNPZCszbcTA92Fl01yH2ZnDu88WQJ2BDAbKF6vY5DhE1IQVfwIv5i'
    'IA9kw8GPyiSDfxHt4ke6AqNHExpc7rW4AN3M7Xfo3gqLX5NvGP8CHuK9udCytxzvLwMZvfkcA0q+/GAOUl2ECGfrbAdivp0NMcvR'
    'bNgnVdXdwOyX1PSyR68GxJY7Tt6XySimgM7419lgmVbMCd2Y2kyijnf7wHe2KY+1kJ14oPgCNRogsy7nYEokyDq4pv0Z3sRpaqOg'
    'IPO5ujlTpGg7TIoWnxxOkSnZJ5phLXVG3JqNBKqA/opq4ylnf9W8EmXddNpMOg6XL76vLj23I95Y73NU3x6xdJhnFpE7cEaOKRZK'
    'B/6Vxd3ZQNN4nXSyF3AqAHYPFvC9MYxj1jcbBbugUE2DZOKARuQxtEFmIC2VAolifNP2h8kppIBH1QQ8ilhZH1KmeTxV8G8tK01T'
    'K/qA1kJhoRANw6AQMwRB210qQy7E9kALoPSZXx5LcDj/59/9vXslZhZbpEbnazk6fMTl+Wi5DKje7fqJkCCTvoensKi2Ec2irs0c'
    'JF5ZjDd6qZkI31iSpzgawu9g8NqnT6CVJKhoRklrGupnD2/dvQ4AWZ3UH94miq8sbKc9Tkf9a2zIaqfOZhiTh7dynZoE9UHUIb+b'
    '2uPQX/ED1agziVpSoJ1gkCKOZm/L/xqBz5+LHKmk6cLdmt0+6VUFqqicAjn5+ASqIR+DATiFW4UHw6LCD6UIusKtkvKDHMn0g07k'
    'U9ErecUeYc65dfgeg+Ypgw5YJAEdjkAdIJynj4voqNSC9tIGnigP/lqHRNTCzF8HGaN/x67jiPar96druWSiOQjlcRDqQ5Lf8XXL'
    'gMhxBYHfGKZBLKwVapG8ABw5GW8ieKG6gW6bgi6a6OiSZIIPeTHd6Qz7A0zYYFOaiyrfnLS7RA0scQO2UUF6ERTxPoWcFxw1FzBS'
    'wPxXx6/R7N9/zuTaI2OI5sLCJsag5krPl/nbJhrDcJt8ytr6lLNMA0gZgHOYLGyqp7qHT44U+GQlmOjWz5TG1XeYIkHtAEfMlhoZ'
    'dJ98VUCnHUJiLyXF7Hud9EqOduIaCmg5nGKdMYy5FoUp6VwjNAwaRMM0ftntRyMgloqjDu7uULRdCbLnh3JMLOq3ucm9QqemT/vA'
    'rcIIypiL5MSNp85EXrxzqbszZ0jnakDlbZ8vYT00CVOdWPjG9QPV0NTurRcwzdUtP/Ubvq8Oh6oJ0qItYbCholmqJQVy+jL5GHdq'
    'q8HEu8ZARvjhzPKZZUs3PlrRzC0QaonkAT2marjRQ4aVNVOrGtsNBqbaC3xRq6ihNP++4oBa8qLmMszx9WD0aX7s4CAZG9mG9rpT'
    'qAiVspdTqgWqfi5MHA9wC2CA0VJ8vDvRgePcU7wEoK4JFmrZpoyRyrh81AjT+UyrhmUccyvujLR2+M3VcNBHhxiePR8NgWzh2InQ'
    'EZ2Hl1f4sk4G/EC24KdFsvDFcFMhG3XjElhhNmVhK2XW0bAi7cJo6NLHMtbXyH+joZOW4QxAxKU8/rMk3KAwyNCUrWaH2hnYdOg8'
    'HEQ9pPIEJEbFyYJHONNcOO8POxg/Lr5AuoG6h4e33Dq5D9Uy3QVwSlgqF1V2H6CRL+q5owViMLHqPpccTjTh5gIieich50s9uAuk'
    '1w2KwLrgiWtlc6F1UOcg/C+o3Zov3SSdiR8sbP78T/+DeE8/X+YuzIhh5TubZxtlWVcy4EcM5QQhJRDOoV0H0S7udl+NrlnyCT3i'
    'LSbccf7YpCb7vc55lyaHXn10ZqFn/Ws0IK65grHRWzHe2tkVRsM8j2h8rDOj6nd1lJKbBO9prTeA3OjyTUbZDYdNPXuOyGQtGbaG'
    'OUOId3BlPpgzFjbg5kbZxrtR1SgVWUpv8P7YIGrUfs+xTBqy3lTs7g62WdRLOUiQP3HxhHLWMiJnsKR4cCx+2YNzha8tNVgZFO+Y'
    'D9GwtrR0jiHflwbk/BdsXMCxt0Q689XVwccNBR/dlIYOXWxnRmHM3ht2TiCR/C9SyRPbvyB2UZd+OURv2Jf9YYF6AYZeXlYjmdew'
    'glRrGGCX6gzb4l+I9PDgXtOd5be0mQpeob63VodyOxbkckTMzwyzhuEnLur0Yr8zCfnnBX7aRxF9Eix4o2SEC3IItYHsgPBHyK6r'
    '0Y5GXYLlnIi0jNr3sg1SShtNPc70FAMjEOKylaICxRZ97CDBCiHBmz7dEr+PO7L8fnZbCwag9r3h5fAQLTnwP5aVsKqiFfUNp4q2'
    '+Siowvr8HLazZUhxL+T+mB8Yvi4bGHo9ulSEqsBrr6wKOzvmtyG+LhuYcmh0p69eF1Whq45GAXkTXDJoRE1hcaA2hDbmU+ablpee'
    'rgRlFFD7qbhDVa+LhsqXmzmA0Gvk8/7w+7/7t34BJWE/mDwRGUWXqZNjTVI/C13lO4W7OxNhPKAqfEFSQK+pArAqnct4YfMPv//X'
    '/87TNPraTuOlIRIUdUzXF26veNCVd4wVVK8//9PfqU6pHcWRj5qbAFvMh6TGsOwUKx+YRopO8sHutCMpD1LEAxqdxVlCWYvBcLeb'
    'OCM1rKYreCD7HDPsQOYYwyxR3s+/+/eGWOl4e5w2V+OY79vxdPIygC0dOez/5TCZxv0zgceCDi+PL1wGHt/cg9eejXlWlnUfZs+E'
    'Bj9zHB9PRtp3i7KcxSwzmqUSZ0ERcsoZZrcFhz+fm3u2eH2CpM39Qes53M3hISu4ry/VLZu6TNQ3OOoFWtxtiYBL7/iW7Lq5ibdj'
    'sALZ0m5wFa24GMTtlDWycnyF7rEUWkfOadasL2OrEQ07s64sli1ZWPzk56QyOr0Drmev8nF/oBbZlHN6cVbUCBouzTBdLwH0MyIU'
    'rgcylvg3Hbbx4IHHOjwCNxt1R6jiIzbxD7//b/+dXy1CATmak3oUCUlIxGaYCkogzlzKi5aKCE5XVS3gEWsfvPa5+6ZPhisqKEFB'
    'u9A1oqLhYs/Ke6KSNFqqQvrT5mZe9IGvCG8qac6P3GFAx/IkA90zB4fmEgBzOx+bqJD8sqqseYm70orNQt+Xl73vQEYbiHL3/JMx'
    'NgLxlMPNRam3kEKdwULgDASq2RajjnLtPueCNHni/3T+k78oUEQTkluh1w2PZWFxkj459SZuGpOsnVfuIm7FseyS/qAsUEPrB3Wp'
    'O7EtsbDZiVlXXcM2R6GN4l4Bl56ih+eY6IV172mNGzRWF5fDQRZ48ErOl1/gIKVF5mzW9zhHzdBmPE0zG5p7R4VhPCzSdjWeDD56'
    'ab8L+O9qvIo7nmy4lC5LDKg3dI5HcmAd6yWtQZ/5L3jECx0pIxdlB3/lgU8IJwl1rPslsWtDjXXS+Qi7B0ekLyu36io52xlVkBFr'
    '/cVZ5urVXNZQMULge9/EaAsQRJ5ZsZAKz4SF5qLnCLMc20O2bVJKj3Nuk3Rfw/7NDIgxg5os14bWgcYfG6uziJzrlshZ2pqrlmKl'
    'xfDyPKqtra+H6v8r9cfrgVFZQXHsSXOkinmjlwUdJr3BeJSDgVrqBdJdNRfYYmEBr3+aCyu4ReMBPNTXF6yLSVswpu4WMgbLKhHQ'
    'Vb8LO7u5AK0R80NhkYn7gd53pQWH/wlHV0nKtNLoj1RJCuCQ9MYgXy/kNmNejcuoNxMr6NClWUlK4Q5sWIouvcVnw4ZsL3hfR9Js'
    '2f3c//t/qt4t+yK5qiwmWdP3TqowDDdhVnTOkTkCcZURBN8GeFd/MjEubCbNPoDYcF2HtqDd0myKibe/5X+9fv7teWfdb6gvuB/x'
    'fefJs8dPIr+BJaIn6+d+JgyGdSxxHxWdkKyR7eEPv//Hf4Tm//D7/+b/8Tey8N85erf7Jx94UMMKM9yQZlw5SnhsUaRSv95mLAZ0'
    'yJ0Ks+G8Cf7dHUclVzE3+K+8/co2yVfkXgzxfdsLw9fuF2RajIbHyu7YmB0bi2Jte2xMj43lMT5pg2PH3tgxN85bGxew7Vn+lcOw'
    'bBSbF2K5vPACyyC3fAhKDj7iAp/ueElw8Bh5Ad7scui19o7fvRVA4dvD12+33/zGQ5d0mliEOYZe720feC+O9rb/wvccZzW5eG1y'
    'YLjMiuqQSYap46x3+g1FSVEsFA/yBAuclkJKGPFyWLmgce5AE42S021i2XAmYUtlLVjO2uGO2E7j5nAS4UpwJFcgdKxVCxy+mAXV'
    'IyIDOWnHSmlrqm8ZZw1bjpndEfELuiLa0aQoR6A1Tj3MDdfNoKLppneCzgP6w6kdGD8DBpXB87NMi+3hajSYE33cxWp3+2nMWgvA'
    'pOkYlVwP+sOR7Qvr0tVSozj2pGL7NnVVwGlKj/tRCoLBm76qfUGXRgmaWGIXdT/ICvnzIdBMC3nqYn867iLiFzj03gp0JJ6kkvDN'
    'TM5oPdEEiqoDunIyB2fyE55s5u2mttsK6YYTR1EnG+4JYTwbetnvm2TrBVVSf2InCTFWBOY+PSk+BKds7sTxP2bD6jy94EBYHP7X'
    'scLWd/6+AZS81BVOalh90VsNvF+pNhggp7NSOltkwKB3ICR89mTFDj5z19fEtgu2irmmMQwWbSzvz4O9MurNL4VH2s2m1GBc9q/E'
    '8MM2ppszUhC/JRIO8/aMtDXzAv2Z61qFyNm60SnCBSNRz1Brh0lgTChK7GAwEaxt8QJTa2/5gKNdclOhDV5sJdPOGsdsPLx9AHVZ'
    'C9ZYHXz0OlGKCaO/Xl9f3+CWXPnavkb4aQBP2pimjTcI5qrcipx9kpxOjIHNV7bhhO8aUhIHiSrv7PUvQWfE0NGidFaQHJ9jDVs8'
    'Z8UDqxcoqet5/+MCrDOWP4ay6DWxACvGF8JbPpURELpKg584ID9WqmEtVhZI+cDuk2ZpBHG2rc1L3uqqxgEoc1S6k6BoGdFwc0NW'
    'jJ6ZT//66dOnG+3xMIXnAcAWjuaN62h4mfRYu4n8xwYZw2UveEqUGApbmcHXi+IaA9hYW7YuyhqAPOrQChNOmH4XGI0t3/qqXjLS'
    'ZeBZ0BrM56o/tNVg5F97RafBb/pjX4PcLsFr8ZW5BXpgDeescE3k8w73O/+6sHCeXZqMJZC9Uk/JMuiIuzX3+A1zaVSwYracwma2'
    'JavBBIwcZmFPkhyyaQXw9pY9omL7RNSeL3MBsxoIQCAekWyia76G84b9G2h+rew+jm1speqmow+aYXg0IAwEnx8OEz09GAQojsEE'
    '3SYM/YC3deyqYKkwgW5+yNJNqPuh0K0BkYkKzj16jiPgqWD0U+egpHg9Dx3Nu2QuqsIfdz4UwWnqZEgLoWfCIa5LpkFF/0hzwAj9'
    'U8eOehM9dI6RXTJ0LPlHGjnbJx5Fo+mwvxiY4b98WzZ2KPVHGjqlJ5i+hbGU2cMYyLtsD2PJPxbCiIosP3xmMTTOSDnrysKhh+q7'
    'shucdxz6OqJ2nfSCaaP5Qjcs85MIPPnyg8uyBcjMIguJQ1JDdt6yI4fhluVOYMbheObnuNvVg6OsETMcbKQILT/Z6PN9j7aSoSHj'
    'lxbDTY2KeGK2M4SHSdHVirAm4v3TwPvCjctoQHyF8Bmj/kDYjPw1nZ5/fEO9Lbj3adudDrHpP//uf11wryQ3LGao4AZx5ZtgwxI0'
    '+Ka9oNzqmiq3NIw6yTjFi3nFTLXb7Y1B1MEYP3Rf/ww+WazUGs4pfyHY772PP6GvZnMhuaixoTm8wYuMvR65Yt4ipwftEusdbHCR'
    'wZD+7rLhJLx2fV0KuUXdRhGLmPcLAHJ3MSqAS0HJy27/JtgodzDIw8wGFHGZ5TwouyTA2k6x/vo8/BYeegqKKwmDtz8//9KILv0U'
    '4Lp8+fNEdyXUfCbG62aKkJ7m/O1quIpTXn2MUy6DjFNqTSH718+i8yedJ18Cwd/209FMGK5UNtNVQeyw6Fz146vpmiQyAaE20GQj'
    '47DpI44VuGdaKpf2fdRk+bsUVkM6atN2ZvD5KIhfZ49qr+6op6zIiLW4K+qBuFuQ31AzbqHS1ianqNAKRAtrz13TVmfisJmrDRbN'
    'UZbxR2UDKKjPRh9lqYTz6ugvAGv2NZBsC9hP6KEKSqegUrXU4CyjPqMqtXtwQWVpqxJu+cthi7YNpznAegXuT9Kl0ZL04vzILBVX'
    '8iUx+NaGK+ZLaccwdSA1RfDSed0d5NJk7D74JefEPyMU0642DpaxjqxBKjKM2MO6r8aXQbuMriz5BZBOzYrw7jb3Tmvz0CUS48FU'
    'LH82I4xcVH6RMRdcZWmFmKTrqUQp8kULtupWghOrFe33N6UVchssbcVKxFDZivYkLG1JewhOaYkdDEub0V6DU5ohp8PSVrQj4ZRW'
    '0A+xHMLKtXAahMkzsXxGyt1w2oyUt2JpS9YNYTXiKGfC0pbYSXD61NjHsKiZ5WXvsNeOvci7jIHt4aTxuFGSFI1CknN61/0kya8o'
    '3VcaDz/EGLDBG8Ojn6qG2ld9INUp5lDHIPde/8IDdBveDBOK3QkVrtH+SJ69HlJUjKrtpe2oV3ejiDmRMHOx3azUWfNbJtjlhUDc'
    'n7nTsTfs20flLJW1out3x9e9P/0UXUiGZS5FdHaekE54kVQa0+mBCuoUWIEYFG9PYmeh3Bh1k8seXVGljXZM0gOKks9cWcwSKB7n'
    'xY3pN49ay4ZBIOjmMR92yr2F3LTuqlT8Ei2psBSdu7mrjjfUXeL4OY7IQhOfrfYsIkt248AKFi26TFQsnarlDT1yj0DbUEAKTmmd'
    'k+ZmIrbbhWY5FipRGFzOLyiJAk2OVxiGNHz6mdCw9ngpdTG7/I2O1venvcP1PGYnlbASSwQ9gKIOEuYuno5luDFTaxzVsLw5/k4H'
    '2rY/W5PTkb66De6SgsfkGymbrRO5Eb36qTMneNPsoFXWDHgMyorVjM3kvcdufCZmGu2kmD4A2miEuf9acD/5TI8aKWsZm9gCiM+H'
    'qoWkRtBrGoNVhKo2SmYAszELGfkeQ5f92ZjcA0RxQrUPetk4NJv3gSF0wpHgQl9nhFXx2k61+qlneziWrQaG1Xp425ssYftneczq'
    '4S0joHQNH7jTLQml1pC/QQbRqzvDfqjHM2Cv80oxzs6CxvjYcS59ZunytzBNrHccXXqUK/ZPaKl55jR+GL7Zp3bi2wfml6MpIdOV'
    'VtKJp/otU+aWFEq6WprzUW9aVewY/ei1manuNE/NzZiLA+552KFyedV68lzNIo24HdKFA2yqGiZCIQ7s7TBGFKtVeH87xX6BzEE2'
    'gAfcz2zrI4UVpOVnoXvzZ6fEdfLuZHLjFkYSLsxy6zh9l+cWmcN/Ous9fcbHMJENnNDDW+WIxQHK0ALClJCgZSY+J9EIjhhKgX4A'
    'GHRwk3tRScYiAwwTtR5eJp0MXKLLqtiorCWzovCLu5QTHzXvu62NJwmYi15Nd7PlFQT9ueQIpwubixR/h+OWOvHU3FxIUiQwcCby'
    'iy4bPny8jDvuUsh9l47F4GbiyKZWomDN+p1krHFfdpKo278cu2mYHC8HCgKKUtGsOH6C0F9igZNaWDhF2cheCDdTEHfWY7wGHgge'
    'BBlbIClpZlv9B5OygLyLZd0PN1dJN/Zq+O3RIyqCfiBxN5Di8O/UxsXliypQZSdJULBRDKP0i4DIbjyTLGzV/oabpkZZuSkTDfx5'
    '7jnuFfBqcTGbr0nnhiDldLt/jabXu0ID3vbThBhxhNYj7w3Q8fru4c47tPb76e1hax/T3/3EmSUxqaQ9tmRxtTiTUkZznfdbdMI4'
    'P0Mv+0zamSKHk7xVu8c7pX7m1Cs9hdxhaucrRd6LIxcV+vW+5Pjbfw4+pYNB9xNPp8YuJSpOvvIDcf0/3IrkAZWpLeHmC2q7niPo'
    'w+kdJOfDaPjJ+xP0FMHxy/A198KzpU/fDdE5cwZvDix8L41WdgSf002R3DoedPtRh3qpBbJ5ZukE0AfZHTqvcmhzFfU6XR76O2q/'
    'Rro0l/3DFvjOcjzC4yPGaF4Wp4evin06MYKBOE8CWsZH9MJ49eIvOEqxXzzi7RPJjismt5WWiy2GPGjQuOr4GGJQrIYX10fREOBQ'
    'F3c6c0y4gnIOISbOgPDPdroL/b87OqjR5PQd6HiUuQWd5Dlpq/l5Aynxit0nSp4NLx3Byn6JKtHrCp8M7hoDRS2UGmhymdHV+Pp8'
    'YdMORnZthyIzZpHXtDo5q9aSdimORT6ypmkk/67CBkxZAq143ww+4v83clZhT3JmYAXWTGydwNvOx5lyYLQys6a1FQzsif+rsGqy'
    'CxmjpouVZ/DfjFHTY8uoaQ1aeeraexWYON0kndEVfFn5FfmMlEW5zhs4mUsDilxrwRKxDXXb4+teY3V5aXWDotfSBYm6GikNE7O2'
    'HhirLBXi1kuuo0vg1j7BZvWY8IDAj7IlZk0aYmolHlR+j9nrkXVpJzzKbAZhdwn1r3Mu7YUhxDixHCfNUbENgNMyoRCb1g+dOKi5'
    '+RGaTsiYoNBhPkN2Mgfw3kd0dP5z4GFimslO6/sCw4l0zkwd9nFypY6TE/9rP/RbnLzUt1yV8C0lJfRf65yEPicWD3308IA/L9+2'
    'sBhd0sNLdcsO7TiG9PDiDacLdU40jgVlxYHCgasM6BY/jNkw6yaEB8XYqFsBOnTEJHy2gyXhb7KJoB+qYbKDUJ8vBvqRbA3UD9uT'
    'gLqzTPbxt7ZP52Tj7ENBJ8KCTvf0AXOjkMVrbXlh+TL0FxbQK+EscF0AU9RbnPCC0BUZAoZbHDY3h0JIQj9QNOXHXkbB1u2fC2Pw'
    'Ah5rJ9DkaQi7ToJnIIFZhnd+JqnZeNhFJToczKIt4Xh2eFBjk26u+grdSqSGE9WvKEg5trwBv9BIVvgRislCF4x1HAl+VUwUVcVB'
    'gKzSf28NAlrJ+ef7sBVkUwBd8ws0cPzx7e7L6TvG9cT8QPvBBHrfwTfIuRSGdtdfHZUdEHs3BTedwKjZoPbr/JMCo786PPYO9lvH'
    'lOzqHWZwt5NdVW0RJxxjRcIuTNZRcLR+fbGO/+WT7ybGbA+N8363A4eJk8Hi2UL2+H86GHnPBqMNO6zfY3hXFNYvdaP5OcfsaCMT'
    'tS/NBuvTviBWrD7J6qCyiRTHveWgt4YMhEIBQt72pyWp7DHgllFKWfCzXVg6TlQ3G3LMJjyGmWUdWRQJk8EXtcaV16SyS+nytez2'
    'Xf/P8nIInSlFDPWbVtD1sZoyq8d6Vo7PU3UPru9Px3BWZuEnxe7UV9AAxaZ8sHu4c/ybt3v0ZvO5/AskdvM5jU+1+Z8NgHVCO0fK'
    'trz9xOuCDJe2o0G84bGPQ8NbTXreSv2b9cQKU0pOwLceIcJFdJ10P0HtYRJ14WyIeulSGg+Tiw3PYL1HaK/rX62q2vL1CX7Nc4Iy'
    'iKXzPrCc140nThtrmTZWStqwPNgz7a2u2Q2OovMuAsNiej3Z6tBENxqkcUM9WLWuKMKrIS9ra2uqz5urZARFFf1YF/phjfrbzJiR'
    'plhtd6Bt44YgtWVMMoeV+romQV93Op0NDwjtKGlHXWly1B9YLQ4bvdEVWtF3O+S7EXAnDn38Fv+r6jxfZox5vsz4g0uvUfJq1Y5F'
    'gMQdcRbe6gJrEnRvppRVE/IOTzn83wy17ICfzc1osSrY50pQnAUMhrumh0soYO9MnjNsPMzx9DWldsKnVruuny2e0XxHkmN+sWuq'
    '/DLOnvLidWKexX0Qf+F2xyccgTUigv/D2yEHMRw5y7FsjR/kNPwE08PN7+R3u6G4qfAvMCgUrbuGTJ3/0znsfu3FAJ+NzRTaS8Y1'
    'bKnoK6ms1MmdxqPj5Druj0c1uc6gwgNgCUekMgq9JysrecYGOBaPCnl8fUGaOJfHsa6iYyQ2SRp7y2hkPsKUtP+cxRhgmIhXsmMg'
    '/svW4Zs6IWyNHlPimpOLTxwXLMiq1zAqFUavjC9SSylZnty0PF124ISdrdmBBCVcqRM80A5DLR8OJIBgLoE0sHZuiEErEb2WQIhc'
    'WyH6dWTBbLB+jjJoGYGHEp5QG7vLaZh3FkgF4h07aBylju7UnawTIrcjf7+R1xe6CgCOx1YcYy1naYWFTRi4SoPBio/Yo5gTciqr'
    'UO4BQztvU8gpfEKTlieUdDvaClFbboeSpsUYJp5ulMe2swdjTEntvoN8LG8aIdSonJqOtKWyEJt7nIpK4nuje9hseisgkejfi94q'
    'CCGrobcSOpmtcgnNZgmsNmOAPpcZv44+0h23vSnVQQXfOAB8YKeyeh2NrmBLfuTPRBL2gViqUPwkL6XdFd/I0/ATKbYfhMD2BBQb'
    '3gln/dOY1MO6YfwdysgwVJnh9O3QmGh4wiZOGDau9anX1krtPAl+G/XirkfCHyav/VO6F5MxZwTkAU2oWqdOZRx1Or3JhPxSHaiL'
    '2B/6w/cgU9K6SdJUl2+/GeIF5bCq8+sI2FYpZw9AXgWqjUpTYRpspZXpMgXoufHQjOk8AvE5Jpg5yWFbcXvW1LBS3U0OC/UDbiY/'
    'FGXTPGPowow2N7eyM6xlJcD+CMvjF7A3b8fnQOW87bf73p+W3lb4EQa+2AaEJqpu6ESRDfMhXsNcjE5mGkwgyNCOlhga97vQ8qEJ'
    'jb9dqJ0Lbe+Q0PUbCAuMy0PXQjZ0TX1DxeqiBWmYsS8M7Zv3MHebboZk3/KG+Yvf0L6mDfPXq6F9f8GtanV5aPSA/EU40NBmI0PF'
    'JYWaJobWLgplx4VyYXmBKjqMzrQzxlvSzFERFmxarmm8ykPtZR3aTsSh7bcb2s6yYdbpE1sEnuqrSUBJkmHLvOr333NQMbSyQiEe'
    'hjrqS57Ro+T8vN87js6/qmXs0nlr/9QfJpSeyi2NezLzyrZsF6JvGEs5OxSHLSmkb4153LY6J9Vnb0gN03gX5eyppWiPdx2jKX2S'
    'XmPqmqjb9fogAw6xYBqo4x1H7Rwm5t4ROoNVTalhVs1ibvYr1KRm+6ZepcnWQd1Qzw034gM2eRMNUnK46w89CmSDIFaxYr8qSG9L'
    '150lTS5rqS31bMrpTI+BnBkKVu31h9dR1wYgL5XhVDYUfhCGKCeY6ENyGeH45VSSONFLUPlqCdDhIhle/zHo7Vdo5vVTer4rOI9m'
    'BtpDjz4Ohn3gF3GMrREiDQd7/xAPUwyT7q3hLmjDviUrP8ry8xXJ0n3YzZ9S9QJtn7CCfoHKPlLIpqimpzpIlpiq6XcREqkesi+J'
    '6oA/gEiPgpyui8w1vtDto9YPf92y2p/Dw/cvqRI+nyMXzzHi4yjt97aHbfoVD5K0D2IFhXkfxm04D1DhhRmSQt6pwH+Pk9En1fVl'
    'P6I5eJ0o6X4C9qqTNtZXVjBGPALzLd4HN75dIWLW0d2nwLoTOCiavKSewJQbjRXuaBRfw6k8MhNCXS8KoLeoF70cQ7MNP+4tffcC'
    'o9YnQ0ajht8dDX1uAc51kOLPxyMb7GyDBgLye/0KsQ1O+JEBHdBO7Eet8aoI2mkDZgy9p6MWhWPe5vD7+OKIYAg/uev+cABkI+5w'
    '5GqGFGwEF52+Zztp48qQLbA7jC4PlJUuYyRZLZJmRiOjhwk8hg2W9GEXwRYm84hQ3bjDMFeITmvmzHTxLunU2DGl6Q+ESqobh4e3'
    '/GWy9PAWDqa43uvf1FBxJ1eKj58G+InkGgxP1L/OfBXLw7XwGwqMO7FGgIhh5snamBmUMZm9yGoZW82QaZR0NzQpkg9ItyDWuf0L'
    'j37SrXSf7vmcaMHF297DO9HMJ7onxbYUI6I2Xr5onT9SjZrIs/iC1RMBI4+1pQpaoG9WA/Q7U99slYIG+KPVAr/INKH2QNEciMEw'
    'M4CfTuVJAfjqmkKiM+9wGH2qJyn9rZWWDLytimZUtupsCdm00M1a0WdNmKeOQ5csGodppmwcmuBP7UiXLOrINFPWEcK/ro2kq76a'
    'xAGVbVgbomjmVlF1wZwt45K/glFlCpQPLNtS9dgypdXwiOk3lOGA8B1ZklKKRA0cxW08zBwWdT6HmWJ3GVlH44VhUOQCuPXa7K4u'
    'gWnHWMlT42LCP+SQHyreAHVmwjXhT1EOo/bP8ndwnGWwgOMuQzowcXYoCIFD5ctcZ4q8KIKMkw6Rfjzz6IHW4hXwDniqkJeIVvHp'
    'CRqdp1J1x710PIxZ8uEzlKaL5jv0jmbccK36URtnwSPUjV5x7w2JqwOn7x5meOFx1vknB80ITYYd9bkn6eeprklhGH16Q3f2qhie'
    '4ocXQFJUQ21gKyRp5Pj6GkRQYjaQbdzDilcp8CVZE3uZDtnVCnSU0pAFAgS/+mCgzi/qVtveoqWwBKDQcztOujVaAgUwGOpq4C17'
    '6+uB63ajVxjEpyGgSgxMGe5yK4WPbVlCZinUsDZS+jH99Y+1k78KTn/9YwDPD5dJxZpxw5LkKFgfWn+gJoKgM/px/BwEnvORIEQf'
    'sqpo3rNSViCPjZ8ojEddPwBqSfOc/qnpi3Nr6Zlm22m6Hhmrayu2TpeeZQm1zSJlf6ObO3qkRUptdTLGFVyXFaJL45opqFZz2Xvm'
    '/dp7hkv1TJsxquRL1CERw4y4A5Qebw+HDvfpfj8a93rsTC0BV4qYTNrBrR4Irdo7xeE0GR/0JRWN3r6lYp/tRrZFFpWkvdDy1bT3'
    'dt16xWX0Zubv8lPpVXhn8yf+ZVgq3tYyPvnNX81u5q/qtyjMeCcjx8Sf8YWkEzqVgcsWV4MWfGFSIOpilKNsJBBeyz7ElCjhssF0'
    'eTAkCYXlDTpCUH/gk9qKdJ9P1lfkoOvG0VDdGhdgQ5A58S0syV03I7NwNez3kr/JDIk0yDSgSSBjyJzHWPVFHJFK7IdkdCVJgBhb'
    'DU8vfMO5lGSiA5sABJce+vYpHNPxgJjk9Ludvd6IWO9mJnWuaso6XM8/GTEMZLbX0aBmGlCXvJTzAOaMf7fqyvmRApbIlxN8UJhN'
    '5U7tI1z885hnyZABnjcePUUHdfwRRF3ehmqoqBSv2VuJLqbU3E6oHcvVQ7UQ0CjkM0mXgLXqY1i4RyXQgzURjj6B0MqIbxq0JHVl'
    'PvbU0U5nFDehzgpZoffxJ2t9NHAoQ/OmKGDNHCkZs5McOUrT5LKnWwi9nmEnlI8r6hZRvcex3+xFVRHgit2ioU6AFes/qeYVxUPH'
    'yG6/hzsAR/E9opk1hltze6J8I3ny+f2wE3W7ras4HqXZHQEoybAixk/D32C9qsmMcqfftjNrx/Eoi1KpGbz4xWxmF+zWZjowSyDH'
    'PVQ/tdLEep0KW8Ov8DE0JtYoUI1iVVz9hhrD+AZnrmrJT8Nqoee0fLRfZZr+5Lb8SdROpKSTiI3qtxOEwfJr74/JAlafZAg4p1Ta'
    'Hw/b8W7EGcPha12/2e/IcCqESca5TsTojCIjY1yuKaV7bmjWXu7zVBHDZEldWRTK7aIKKTGOTyKHVFmUytxHc0tqYXCKuqUOvqAs'
    'TE4Zt6paOacmYqapqYq4Fe1VdSrrmHu6Abto4cBxaURFVb4OOu+Ygad9U88NanSZpUXJVGfn9bNRhpfG1RO4KxdwWEz7lTSq8cr9'
    'qlHEbshZbM1bOudE1ipZGYdl0EiPW5VXnv/SHFCk+lWUymvXzUBFAja7RM0Ih1XQEB5mqqGp46PRSQ/uPDXJcrVaBexpqM2wPs7C'
    'd3qelnPSKZwe2UcVnN07WNLwF7JoVn12wujfECch+AY/6yT9EKOYMd4P0WT/NMgY8Xe1L73KfKlhddGNRq/zeGGNQbnQW4Nrcpuc'
    'Hgof80xKloYe4SScidMCY2V3Bo5MadXWXJ3oJ/WHUMsKNAYW6AlAmRSgwAnQPU+pfrHg+LeEWhgyybP0HgV8d9xUqmA6rhWanoOM'
    'OTNkugfuDxs0VA580NZaBhBBR+O04bd+QJ1A0n4/HnDG3uh9LI9IWBsZwiu1YbbxqPCbgtPE4mz00YdMW+bwCyxmg2LwalbQ4eLG'
    'AzwgNPuib/9qtiBayvaY3KWWEg9vcDTvw3ZceI1uK+vgVE/I6oEplsZ3KeoYXop5F6NcCROVntdpFIZ1op9YnR7qF5ixx3yln2Yb'
    'IETolWOkiXoLh2DmigRByT6qVvee5BrStnH8xdGWEq+v2PtczdBIzarzLSU5E+Lw9WnHk7AoE7cne75Ni2XR32mNMp/yiOVosQoh'
    'WTAxK/AdywcFZSq7zK4djxWXzcYve+nojbVq807yK21F62wiNHoxW+G4j8/RZTzbHpoihQNRu45646jrK0MThfgA8ybd7SiJu1gB'
    'BEjwoFohrom2mn+ZJklBYjT8VJoSuExVv5EtD7vKOlVFqnaYghNH4cS1MqemwvnWLLcsFo13MmAzEbIlWbfZIM9IPZjKSYnlhjSu'
    'rF8L6ZfYqKuxaCplunOpzDmgxnv0msxrSDq7cpEKeCEx0h2WYasgDJSyRnfPYd6GU2+ITriRU+pTTWJ71KCF3SWbFjhq91uHwhcF'
    'hgJxQ3UZYGYpVbsun5EZCVtaqKKBalHeF0r3U9oICRJBVa/GziLXsfk0U9/5lgq614ute7GXv0B9ob5m2ppxGZvSy4ZLmqeAbUrp'
    '/EQrqaxiw0sV7vdCVJuYuKb8XDAbLw4/ZRAKj5YySDjNB95MxTS01eeCvi2cKureAu2UEZSVNIMwJQrGYbAOh8GEJttl0VvTvG5h'
    'Gm7NsG4WdeUbI0dQngm7KnQ9gnCi7skQ3/gC3aiaHn7OiO6ZeHrme2HpjHbaOVFsLY9DDkwz6qYPeX8eVFA94czh8UJNJKsKts8Q'
    'CZWp6iA7YBmbYyeWOJJtukCV7DRePF7SllVeMVTXq1bFFtcV7bgSMctAU24QY+zxDf+zo77WrM8vFIxyX4mjzIygAILlY8hPTbMc'
    'LFhRtBOUJqJOJ+6gHRpLf/QoRzcbpNm3xf0Lr3XAxljm9gaJQOugnrdlDty+CsvUMmlluHSdRqUSxss7GWDmrYy1ai2VKGliNZRO'
    'wjL19rYyL2qBtu4xGDaX1FuyKkV8qmUuoY1YtSWBqOwVw4f2KHLNNQvvXK1TA6ZadePYUJYycXZpMbAUecX9gqvVUBfkacMhXAbl'
    'LNbXfGL63rAJvfpYr9ctJBOzuIkA1hHMrqPh+3c9FM86NtKJHAVIVeqpYgC2dDU+X0Jbbt8JEy22QKkOFB2o6L8GKV6Nz93d7Vz1'
    'cD2WWEvHgXWWSKMz1xg0EbT7L3fz0Qg9VydmH5j4ciRHFgphBiNIFeXBHoRBKkFyivECyt6TchOGFxjgWYlh9zYKE8qBtrnIWqty'
    'W661V+0sH84Un5YwleXD251Wqx5TbAg1nsnC6ZkxOqPmCw3OKEq1YycmUgxVwXcS5ZXMpSzVFRUjFSANHdApbxjmGHXRQS1HO3aq'
    'k5NhJKBKozIOXNooMSTTykkZOBUrDjtrXarSEPJ6kcKD1FrbWZUOolYej/oato6OXYSMcg17EFiR7EVviM05UGPNM4dJVDqigm6K'
    'LnfkXix3fTJTtzpnlds1FVS1FYeZM0xIK/Xsaf86rok6fpP18gaXjN4d0I2/lWjbSzTxtncoDyaoGIuJR+layPvUNTr4Aqyxp9AT'
    'fTzb5F31xasBre+79IRZseiBAsjQE0KrYftLFlm8FDBuxn7d8LUPHIuIDttDyB2jJWEqJ+iBPvTZFknwSNHEAZz4eBYN5FW7n46A'
    'huPbG6C7w/55LF8+xFdJu0tf5FFVIWc0eB3/9TgZsNc7s6MUxyT/vov2UaRRzle5+FjwNsJDPvdWLjxyA4UJ9NCjI1cB6MQwSl0Q'
    '8BrBK15UX1uxF+m9gjJVgRSObX4JkSvVmjJlzHMCb0O2q0hPg9Io9bBuWJK0XtY8lKBW4wa0oCetD6MbNwK4WBfx3bm6OIRC6s6w'
    'wKLyAUXhzKgqvtSmnmk/l27l3Ha2g3B/ztbGYTF5m3t3n6HUYeTXBgbMsY0LGdSTM4F1nhRkIma7IbEzZIL8Z7UEp/oUMgFz0Q7u'
    'mCvCZjHxWFWitNGtEyzz1EThrKIpMwjnVYLnBMXe9pVXi4dDGCnOFOfhMrG+Xi6/YM6HrLzagX3+grlB+5gWL8JqV3g0unLd4EnY'
    '4heBaqTELZxdZFFfoFne7BDd6aCjWdN4dxk6fmJehtacQ39IjCtGA2G3IIozorRlGDbE8mizrY6xJ33fNCsKTJwrGHFGw5Y2vpqi'
    'Y6iKqeBKNAzk+4s/lKZBCQR8zVUi+/zEMvxv+/3rF9HwewxSknQBatllIsfuTH0C3P0HyYKlO052giVH45gSG4nVbRaxC+dj4TV5'
    '9zbnHJyWAvCnTcXdiwZecuLYGduIKNOQX6JX74g1GaMPflDgtSi6ZN+wGWg1iaGsbOTj9i0E/IpNlU400XM2w8//5n+hALAqt1N4'
    '4uyPn//r/xH+1dhI382e+fnf/G8UJxZ2hLfs7R4e7vqnodWPGjGU/C//K/j3UOnbPdzUKRRGux0HAE0BAI74xGzK4++xI/51ekq6'
    'm8Duydm0P//D/4GDNq9w1M5OhjJ/+w8YqNbZ3iF2yMFusMQ//k/w7w+SKvUYmHfoWrrkvw0c4vQ5Tm+VhBdEHScO+dnzXqRDew+u'
    'luAXBlMkU1my/TlJOmECMw8pVSWzNWcq8LbUQ5dSG5GaGFd5S+0cTGOzYGJ0Z4r6D28xQvdG4Zaxwotz4kwcG45mQilkNtVryRSj'
    '42ZbsbEnuSDhRbRCd3TEYiV63tPOXtj8+W//e+6Mj8ZsV8+XAWSbz9E/10MhfkB+7ijXLlhgVa+gOJbkWHHqrhcnHg9TzcyrndPI'
    '0RG1hULbNT1bSG8k1ITRLsqXYV1KGoriRTux58vJp9C4pmfLCDKG2kU2N2r2jtUJn5SjeW7g+lvoeHnnS9pbiiJsEOYX9cxfNOdf'
    '09A+cfGQuPEycAfZ48bUfcUpEgh70KXrXJ4k7lfTz3hf25H0AS84JDOgBQZP50iO1MCEQiY+H2BkR2kTXg0kLn+mEekL94Y8SqB9'
    'CRRfNvbtTmcb2WTS1DdZcrJPKZEtoMI1sIRnb+CE4LRVE07ocBb61qmEr7aEFa7wuL4n895gyUEY7fuK6WL6QoN21bvlu4jXvsjJ'
    'nlgThiCG/rpI4m5H5D/nsL+HUaJYiCfG4ZRaQW96ejihzk6VGf9GdjaT4iGzPZca8pcf5ANuBjUZEuyjdsYpDQBzjGA48fAGgrKB'
    'm/4MSds6mw2Bpgw3576TySYwHwKUM3fFGsbqOGfmSBDGsooxr5LAjGaBsyKz+sNH80/4YxR8ogey9ClG02MrU7SyhNgFTBdnMQs5'
    'suebMXs7Fkd3CLwJW5JT0q1B3B8gUSQf0NSLeh173WMGTFqHXZrlLEb9ASZttNgHFMgs8XhhE5NlqqNZncnTGqkWe0vhXbHyC5vY'
    'lKer6bEwxWRminUlmzPMsoBI+0J7fehrUQjxycqpq01ZxLfiiLqKcYILGKKzwFukszh7GFE0IIzQTkGazXv6je+dSL0YSN3E1MWj'
    'Ypl2mX63w5ikf79FQq1/7SGx1r+O0NFk2evEI/utFamXo/VmQvbqSL3lZADBrjVWdrR1jAj+nG3kPZVZ2Ya7Td19RbyQUw19hLEf'
    'mrzJwUJulZubZ8/7FK9YEz7J94h/tnxlnM8Z4mVlny9zFZd9Xeaym06cchw8J6jXCelViGhDZgNmu+eZGlbLTG2+foV8cGj1ubvX'
    'mtrPGAHxA/fsn+p+Vu/Eg9yzd6r7Wb0j33PPzrHqZ/VthdSfH+0odcuU3l2amXbJ1bmUbtqsjtMbNP0f/sES33S+B2fTjSSyN0f7'
    'nsJIs1kEMKcD5dDLLql4rDXJkNJiDEyCVpWNIGt9ViIroMgzWCAnEjjBaPgLqJ0hB5PmwsqC1xlGl5c4YDhS4CRb8LL3y9zJRD4k'
    'vdFS/NHJAGZ7yMM6EvhFMsawVSgXR+x5iRZqIBRi0LwBi8ssK3Gdfg/HQlfKzqLo0Fco98to/A0Mkj+ia+PjYdRLLzCGp8SW5swy'
    'wDgkwMQUNRSoDiWfFh6+dpdv+bUsEYynZvUcUs/ZJsaDsgb2ehzR31TJ4d1/PoYXSnCkShUdvo8/8XiTC24XdfWYFHgPu/Tv7pyX'
    'nh/c8gs0d4a/u/FFNO6iznrO/ieSRu054FS/d+meoDlnODyDuJzSuhShC2z9n3/3976bW8UJm6DybVAj0j8mAs6lkHNuWdxMcplr'
    'b635kYFZcRR0KoLHVo6klcWHyyi1WgFJ6vxm4g0unaExseNcs+zKtYAZDZoLq5i0JgYcWV8wtNBs+K36NYe8QzHo8cpEq5b20lFy'
    'TQZpUsCiW7ysKTCCwF3C8COOollMSFvxiBZJQuvh+to0ZJIjpJp4ldEuZ7lNxLacKY4VyjBjqIs2dtnAHE4UN4ejbYm5rCMxsaNc'
    '05vmbYu+dJUxwMoVC4CJvkpHeYZOww9vqdfJWYgkMTYedv7KN42VFTvwD/nnsSkaRu9BoZaflI5hNr2C2pqlagU+uDSEXDGdrIqn'
    'eZojF97cFIm3yTnuTKy8T654zt0BINA4mITzLW9/lCoLmZuk21XoAFQeJibjx7TBVVK6HZGtarxaStcjfqBHnAFlRRgUfduwxNvF'
    'p0jt8wOfeRSGe7lGB0DVvMcawAqgCXaAoBYFTpPVN+5E55lnsIGqHjeCj5xYdGArv7SCuWLOPdr9x32csLL27GAkglDRqObjFctS'
    'RRnJzbDsOUP4UpP2u7uMQbvAjTsDbFCskeWCSoN0Y8vfY1G4FWVLRGtjjVLIiMBF4DEpuGS1uBoC9n8EvN2FU4MPe1k+PucJQCUs'
    'QwFDmmfDLgvYMPL5Kpq9iw9V6BVUHUb7qZpux7HKLDuU9BqTeYqgWw6/6GNhaATbna1sYAVclZqQBWkKufOBeACOkrvFeXtSeKj5'
    'xFCEzLiHLNSHCFa+3S2/0C0DSt4ibMrpIFmg1TmAB72d9ZAyLtrsPdC/YTrC7ECqpwzily9xPSld4zxD/gtD8oHWwqoHUcUW2imn'
    'F0uj/rh95Zecbi5xVc7VfLtE5jeyjSRGHIeeRnFGKu5EA2g0FnZfJA6mblljmqngM+KIIdGFI82jit70heVlZ1TNXDl9CuYB/dFR'
    'tjW8RbOLClaqLJMGnhf+/GXo2T9/EzhLXAeBF/BoCcVwP3BQnIZtOtxS9sb48IkHbR0Rn0mQMqy2VLI4gjk9wYTVxYOo4AhULrfN'
    'TZtANc0RqI4qbCDgSw11UFtxHRdpfHd3j1cCE7kh485QxpojlOzj9XMPVxwtUZscBuLNfVMuF/0d+BP1PhFbjYpggBkp6blYA00t'
    'Dl+/3X7zG+/14fd76tqxRl/1rSPxsMSYy9mdlwDwK4gA3Cr9K5UBSC6EKs7gkq3JN10GgCH+/JJwVMwjz7FpZlvCRkv/802s/KLL'
    'FHTuuZoz33LZtvfN2SzvSayOgbESU/gK4IkRPoJ4M7e3VBQsh7cM7Dh9YyPaNJVdv+R54y35QA2GnCwdrV2QvSxr5q/KSD/IkUUe'
    'eSTeoXFOy1hJEWFlDoVUfakk2VDHcVr3jkGu1+wk0MAEFt+jMC/stBhSUiG+YUNLKWUAUheL6JKLJ0wKiIEpyy6gjLiOV0/0y4Of'
    's9+3VYSqGEqIfRWnQjIQof4StqSdvNDcGFKEd91mShkM0VDn//boEu5N/2b2oQ3sANLvLW1IirPFdx5HUpG31pXalGu0q8eblrjM'
    'rUB1eF2k2F0a9PvdBVGcYiJnpRTKMu5cpj9w9aqK/ad8AaJk3Hx4ayG1aE+27Ffao6S5Wa7NDoxivOGzxs6MPQbq/WnBzciLaV0X'
    'NrcBK0XcA75MY21HlGy+Y6PCKjcEi7QkSWRhvTCD7MeFgku+rF5oq7zAtaILrkE+vOJVaVbQCzhF0DWEPjY0YSg9qW3yMjFhzT42'
    'Nz9yB4EbKoPCzTX1SHQau3R8HX4MoPnx9WJt8WPdPuvpZA9X8smklb20WR9oeCGLb8hXoXJ1wcp5WnK1o5RC1Xc6SBp81iCVXSO6'
    'GPLtOi5ptnfWtWKDC8Uj6cx0vZUbTSd/tWW6Jh5gk2ioMwwM3F0yDFQQwjBYQzjnWLBuTj/LY8iCgxTUV/1uB2nBW6bQWh1ZMjQ3'
    'c/ZcIzO2IkXrhvnrGqsb15hIiDf54xV3DTOE4TzqXMa4bQ1qqwTEQhUoAzFxrRfdfn9Yo52w/HQlmFyheQP++tXTlcm1rZWnnuYy'
    'niB2zJooHWGvmcskaw1N0O/TAQvNxmHW7ciczLN3IvDm5NYfomFtCfYrrOAwqLjm1Ae02791z6nTFxfYDyo5S64F8SdfF9qYlXQY'
    'n6YdTxuEPRlbf6y0hLX8QLXRjYEdhXm7pZXRfa4CnnfTy24UHYk2lquTUS+DjZ9I8z+WnIRCvEMmxNaROLGaqmmO3Bwi+BOtQQrv'
    'cmWxJds4JiZfKlj4jfZ4mMLLDsN4YVNd26Eo5N7NqRYvh0kHmxpf9xpry+v2DRoOqE4Ux9yeZU2kC2Uah1o8vKV2ii7U6bapGEBZ'
    'WnB3pyG2pU5x3wcuw4UWMxmbuKSKeFzFw5i78icubi/LIajycU8c9qWw4bzqK0TjxB5dqKseiRlPRnXV6xSbgDw3mXM/niYCFYUw'
    'AhYGBerZb+aC2Ys28zd4RaoDiydnzphvR1M8m94DU+mhobAArQ0oOU5jb3v5hZeOLy6SjzAhv1IGLYFnltL+MVQU80iqyqKripWc'
    'j3ssDImLQ9WRXcWL79ZZEREOo5EHlTDEFcqTtE5anSvznFiwG0UoYmvwcu4uxwmo6YZPt+FYHAvBRKxgMOaD9yJzjfE4iLJiTN7K'
    'kLxWLN5MKF6C86l4r7tB4SmBV4EeqJ36QWiF3m4waQs5qx5MdatOj8BIvevRU8d7azncmcDmijENdUDymeNQI84trgahiVg+a8Dp'
    'UEdPVwxp6IRNt3nBUEdyL1oBR48RygV3ZunsLAAUFrg5PdCwalmCIJDDIOYVw9/NbGxhDi0MtM0yRm/OYIouSCimlWz8/OiRDhoA'
    '7ygZzN3d7USQ/taOyru4GlL3BRF5kYEO7XC8JhqvCcbbdhaAw++qnxOhnTxpWK3mTLbq2RmhHbcrjeKIGzxFsbjbIWNvMmrQU8+M'
    'jZ0k6Ku2j5T9UpRDgLSnlGVvoyTuTJPmlXQ2KmIA5wLoGDp1ZlhjTARAVjHkE2DZIdTP1DlhB6TBNvTvbahafmSwkxOHXjFJaXV8'
    'Zl71KuUla8+WqCA6h4paHS1BOkw0plcmkxOrKud2KdWximPWZ6pYaZPdC98ilTd9mjaT9IyPUA24dDgeLfUvlpA+AWcoMyClzyVQ'
    'gKFZXHT4UNm9UqUBVYohOJiK9WnIyyLPm9NtWIq2bVwijwZFGravbOneqkJWF8DwqaNEWYCL55694MgzU1Ips/mUTbfFTesNF0w1'
    '33ak/LKRtRQHWjwyUudUqcK0pkvbn2s9gTDvtixg1DtemaZlvlnNr17+TlCE1g5VruqFWk0tVyi+XvVViRAZvGS160BrM2DLLKXJ'
    '38SN1dXBxw1b5sJ75KXHRLxQAXneh96vG6uk7GhRpI1oOAq9H+AR/eND7yU8vUx6SXoVeq0f8FcKaN2Nca04Wjw57t0fMqjIdwCD'
    'LwrgYmlSRZfq4k5/PBqMRwulGtYpAk1moSz6dEv7JSSSOGlW0N+NL8Csz8OZC19/d/eARugwyjvQW4oyn2Yr6dZES4CFfPIvyOTb'
    'Rbcyqe549Bb4rmCfFvLTZ6W7Qusaovb7S0oo1/j64uJCcP/r1dXVDMo/I5y4euxqpLAgbISdvTd73hSrYVbwldj00obMNcCh2Ny8'
    'JSp3iFKi2Fv4IrpOup8a/g4w8gms4BtkhK77vT5FKpAJNdj8WZ9xHMhsy199MvjoN/zH8O/EW9nIlDIZDrd86usmplRw5/1uR0EK'
    'FTaNx+u/Ii+eTP2OZPaG6nbptfVfQe2PokRdl7o2Tdbh0YJJXpdiaTfM2+pgHJn9D9xkxbl+9pA388T7+Xd/bzNjZ6HPZyxdMPrh'
    'PC5sbzGxNRMDxThw69qBhPCbNElU1lv23u6+tG7aFmuI8XAgFetv6FrU7GP4AayxuXEiH0TkPXSCGpyW6HGCafSOya8dF/Azmav5'
    'dQvD/k3a1LwIS0ebtj0JBucAqlTNFiDN0pJWjQ2fQwrr0Si2lrsPPcuRLuONlrsOo76duPekoWjybE5WTrdYUg4x+qN6y39EDl5a'
    'VWWcEJJn7KPY2Sz2iiOfn2lMlAOtW4qDS9Jgk7wcNuBokZEQqGg+7IgD8KBacNpwBZ5Us4mz2AJZ8qXfUCXpE7wzb7gQFPF/8Dcm'
    'PJ8zngo3x6M/25i47kpDVndOfhGq4Oe5fMprhBAQsHjnnwxLjzLP/SlEtrNyqvB5Dqw4BfIpnZGfppJ5zpmaOMuuRs5FFfcwEjDB'
    'zDd9oiPG6b1jPNH8Kv+zIpNAC3qkqrKpFa9vcw5MQNx+wD9yGtGbpNeE/3f6N3V0xIb5hv5P592o917qwUeHzdrudvs33gDWfjxI'
    '0YNgQEuJVzlinJJhtKABbadZvxkCbamdPUfqD7wIAxRnaK0EzxhBRh+eE3+wieC7tXmE7SEcyBuDqEP5bvDy0mJ9JnWFPbd8F9MA'
    'scBL+92k4329vr6u6yGnrNgKYJC8FapJi3RrjB825EIHOuhGgzRuqAdT2ht1QuvHVUG/33zzje53HbolySTqJpe9BrIS1JbE+xBb'
    '2FsJbtbo9XsxeW19IuRhwAki8sqa7Y5O4oxrBOWzYMNZArLJRL2LnQS2uYllaClrQbi2sjJFba/CyNSy4UW0/Z8qgcFc2D8HKIh+'
    'md+hOmaNnASLq5MzxkAnDkmR2WvatLKyVwf23Zqaq91w/8yj1m6L4+DC1ldRcE0QXFqDY0wgLimaStObw3TdNuGFrcOzE7Q2JR+8'
    'STvT3KS6UMdOM6CyssPZNoqbJ/7XTy6etS8uYEd/3XkSPXvyGJ+etKOLbyJ6d/G0/c06Pj27+CaOv8Gnx0+i9WidY0WUr1CZLSaU'
    '8IMwF91F9IGN0vjhvG9l4CfTMONXUlB+nhKsU2jkA2w3WP4dfKD7DnvlQ5W6GThigeuE7sGAe1Q9EDbpz3B4r9LlZepPzoruzUpj'
    'K01xBdObJ+kEtypmFL9qlk++1AsJ9ogq9ehR1g1saG/Dn3/3T3BuyRsWA37+3b/F6Czl27FyRKW+XrMDalJieUuB3r88pB6oYnd3'
    'dkQb6q0EPl6UehEFv2dCgXdnW95vQELVus/OMLoYKdc6ihyGhyk61Am94i0AmIim82wnqYL6P5ErqjOra8Jlc2HF9MNXMpw7wrPw'
    'goLgNeyIeLIb3AZ5o5iXvG8MHBuO7MI3hhO0IS46BtC82ywQrKQVemjetanmZT4sRVrhHoTnX7rxc9M4IUgEmHFepFka3fSd7ZQW'
    'apSuo4/Gcj9iGKtcBefOz2ADhRDKc9FcCSXtATwp8rOyYQmLHKocVrqGlRL4mDyHHjaSxUW1M5CHaEqPJ8lpOET1RvNcv9iwZR4S'
    'eB5gleCWhrC4uKG+beNvEFYkhx/sGWwpuJUhWiXZmMQuiy3S+QiEgKrJYcnv4WQ071Ejomit1eYOv4E2oTl+GSAI+NSxJMEEWATm'
    'sXPSlCsqYt9b1J/SgOeK0JDyZTiMBK3uFDQirCiSvSqMiS1hVintf/7bf22pUc61RELKbgwHh0szYaRhdZwsykTlz+C3+oSTB9JY'
    'zyZFfa3j87QIoibATzTsJvFQ/z6IRupXqYCkhSgjKcE+6aKRUnPhCVoAAeFMYdOM2lf1+wtMLSBc0WV8gFcXNbUfMGiAZkdJpALo'
    '4EuVyBUYnlWRcvC1ptUF3iwHZAnDL70aqp/ij9H1AMC5urYdIGsLHC20MdlmpjXjxpIlWQM12PQEH0+btuPKZx+esH93RVn5PR8y'
    'ysPw1jDNhi5+iXwWYlSCwUcUyLaROejh9YbSnOo8Nj6dRFuGXaY9RwuBTWSZ/Zz1RKSaVtNUieS2tprIvZfxp1AP+FNi1/GfWfnT'
    'yVxLUrgig0H3U/GaiErql1qZUGDenB2G9RMa0inhMbx79EjaCG5dIacp74lsbpTalBUgQgTwSMjLw0HhCrjOf3kezsDChmpEX06C'
    '5IURy3dpfeFU5MoZ7uEtrxg9fSBUaATU0Vmd01Bs81jrvExUjWgIfGFmtE0MWoJJY/EaLMotQr1Uo1d5iZmV/9H6Wov1rXj05R11'
    '0vs06Z4IC5tor4gvPHpj6xy/up+Bgj3nVC6/DCdKOeDjD/PbCVMjdXqeGLtgi1GBr4opyMTw0eSLWmCahpQMIAkCsyZmmQA7dsMi'
    'Is9mRuwKaD4PXMyH5Wtu4Urt3UvaqTJDLr080sa/juxLmso4jYcfYsdshXaLZQNsGSVUI4BIQB6zMMyildiAKM4pawECks1CGdpk'
    'jT0EKgsluDCLTUfZ8JiRyw/uPD847DNMgqoBYggetNPLaG2WVvNBEu89kTn8OXJy6oJaOYNag823hoBiVpBMiphy9i2QmOr4RgVU'
    'B+AIMwjcvCWFsIW+nljoEQ6/wQCFEgo6Z/jhGn04QsY0s4+pdgP5emh2pY8JxRYIadOnhtGMCssCwyvVcsKpk87AeSSdUzweN9Tt'
    'WM5tkFXzC5vzeQplGS6JTE9HlrzTOODlSa3L7EgM1pXw2UpgEV8QyWCOjAXwJHtjjmEWcYYy0BD+TGC03ytZtygYPpPFyQx0ESBi'
    'ODAgh22hk3rJhZ1LC6hhqRER+55JxHjF0nKYJdap3NqX3s0pmaOBf7+VMOCUhZDi08MPTAiDf6NhG0nHBjTlxluaw8KfGe6mdQtO'
    'nhHT4zRglAYsudlcefRI0oieS1raB82mlUo04Kt89VH4aZxcXibBQhi/gCHHqkAem1RTJjZhBxCTgIAA6hHZ2CjqRw3ehPygsRO8'
    '0GqBe8xWwtYNMN0aGME1VwFemvKT2eNRtNTCakHduTfSn9Wlkb/t0TsWEJ3LoPw1r6os2iLrFmKaDKdQuEyo/pfj64EdJwgGX5B2'
    'YuOXErBZYIaa/W53vzfqU7Ka2/P4KvqQANvop9f9/ugKdgrKBQ0fBoqWThNV8QLGkpFOSwFwD1HrXu5PElpVm2QUuUEV51OfqRRT'
    'ksp9upXdoXVxFCgmQHO2hTtKNaYI12QWERDWN75kK2uVFwZvaiVhDCWIoXwUGB1CIzxJeZbp47CdqrsI+I6iok6BohZiPpMOd+tS'
    '3Aj1c3YBrThBGDrWDjse/aoyBxkJFBZUYNDUNpW8nX7MuNnjFbsRDUcYN7+AzS9Jy1HiGs3Oc9NDr9qi1QyAN5QnFxcUIHcIEM0I'
    'Sa5uuchOs1jeLREPttujsmgCAOv6TMHBFXHJRzb1i8KDV8srBu+mhnuv6FdvnWzvIoFoUeRh1TGD+Efnlx0fHsGiy8ABSodWqfQz'
    'l+TDC1wCGCQNz1XctPtBhZiDbCh8e7mxgL4ika6mrtiOTZc+c4TQQuUA4Xv5+JZlr8/GMfOGlq2TAuFv969jlTfJawO1Smf1HuaU'
    'SS8RHDWHPc7hFhWsiiZaxljtDZIU8whqtoroTrO4g3rMpY25zca0gmVa9XiARh/UmbrKlqHAVuD3k7MQxA51mPJhGKr8U5Zfniy7'
    'Pz12F42tDBjSPUM7ycgjwtoMpgKmyowgHgS38aBylSoMQNRKoVUDNKbsEOQ6lW3pZBjGzyqluEombd+WH5Rhj57DDHO8pwmHWYAK'
    'llIVug9HSVVLxh8OY1Tfwab8ZX3ijr/3eAqezpxJCQVpIc6T8y5lZJOh6LQ3oVoq4sGQLRNwL3XjD0AdBe/Teyrg7Z2OXJj8qOKb'
    'puqzyw5anjxt6jIWQDBKmaqU8gE2AfSp9Jyn/gETkOrTw+lFSE7paSFDl2JzH2otvcpzjIlRY7viDJNR6YL3GBetGuGnGZnSpyW9'
    'pSt2fFl9hj5w04dMDU0bLhWqOHe1anPKpYraTJpjMHcr8sl2mTiTaE9OoKf2Vdx+f97/iJpoGZ2pnPFjAEK35VMF4csscHB0Gv62'
    'VUJITcN0Orp5SRrTKjWntqqIWAdIGBJmtwOXRi9semXuEQwlzVk+Px9uVl2goB276L7N+aNzY+HtbRwNKWJLgarQikhUHvotew7h'
    'msKRPIO7W5FPW5mYVpXxwRCyQV2YlOK94DATPpWXmGhUqyoq2jpFRSujnNCQmLrP2XEh9awQhUobYrYrt7VPNB9GMSwvRuQE/gHj'
    'MsITm8LAA5/z8HjKUrgjAkEfYtDVbKZ52SedJu9MuzBUR6CZTtF14bSzpHxlnENhzvUpPnc0LZxH9laM9NRDpnQwVeISFIruccCo'
    'QQkjc8+B6RTI5YOTIhXHSiZA1Iy3IEjOyFNLc9mjvnc+Trodi9OeVbIzSW5Z2an1wyXh7U3CXPvWgwx0o8sYE5CMoveciUTtmmN4'
    'gWKSTn7aBro+jEhyIsdfUi1WD441SIG5tJvGhy+xW60JdVGh3SXXPrlvUOE4QO4a0vdGYh+fOXDBEdzAIKclM2C9eX4e5bmGK0Tk'
    'HYGyhoMZpe3nnutNLMexnGsliMY4Vshrbp3U/94ymh2MB6614La3s/3ae73dOt47QrNBMXvDZsytBndUVyhRKnhDAZSUoG4D/1Hm'
    'bJSkC3EjJszQWDNVqLZAiAJgqXEhouMXg6DRUhAMsW1jnylGKwIQ2hdaXxGIdxCVzbSJM840yUAggDvNlQEXvxq9BlfXGfH0zuQE'
    'xHNDthzRCbbqMhCe9y3HBxx1czrhUfOzqUeT23Knri5i8FdzE//Vdag8azxkFLPPUA1jCkHiE6Hoxnj6FOdWjzHTYJrbH8XXqm8M'
    'njAIk3sD+oQaOG06v+6vWZkfkuIp+j7p6TnMcCFnOReU36VkQZE7wpwbFSssl2WnP+U6JGeLn7uwyFvrM6RxwqelJv0O1bDyMVjY'
    'TvhdsFvgzON9n/MFsN2xpx6g83oD4HxYP4Wnu7/l7/BDw2/hKQ/CKa80X+HMZs1PINcm+68YqCX5eFsqmgICZ4phf6mBfoU60MJs'
    'BW3MG+n/MjfOYlLRNF3d3c3N84glhmFv5KwT44qt6USiofKqTNE1ot1UR/Jee4880xycWcfDqP3eU/xASOtDakZrveC32ZakdezE'
    'A2AEcI5W1oCzuWznMhRGYSZd2OKTRsj5DXTzjRMri20TtmebJrVmmcaLkNw1YDTLWabiKuQri6+W89aOzq0UaZqK7Ibygu/nBNiZ'
    '5YLwoXCPW3PrgMuUKGTqKowt2cUz+ZnLcMDw3WQ3gHxxRlJ/mON67ShtRTbUBcbRdMwiK5y1jp4hirITgNGfxQS6kKewU7P6ai4U'
    'Xll4gPvbNWOECVvCKLLTu9/64pl3n2VlQQCX9JhOjOIVZWaTEqnT0Tu/SbzDmm5pH/aGzxHeuErgWwbzxPNbISWwAZEUZkKNJzZq'
    'cG1EjVnQwuLjHWSQaQgG5CbVMoSCH/3J7ObzVUhI4M/1f18MpNa8bv/yMu5UK38zpKfc7LiQqHsGc83kWIqr1jdlBQwHFkVpybNs'
    'pVnpGRVi9lD5VOTj9rNHK6ftlOFyqfuNl0/aLzRcPr+njJYKVSjzzhoVervUtccY9SkUucX2jPr9rkUWLet5iyG/d8DE3QRJFewa'
    '8n9pJwNMc5fWyjV9FXfRaJnXffTohC+jQ44LjCcGBSv2T81Flb66DkoEwbdDZPRie3T2lXuKcXX3q/V9Hai7RAU176tVHLZrXLFJ'
    'K/nAsSUrNTRUsDltqKu1QAIqor4dIIB/lEM/ddssClpcaIAh0zGx0/H33V1lDHUdGtIKUkxOcXZIdT3qQrf+wTDp521pOhbMi4wp'
    '9Kz2naFzk8YzE5o2ZjjGXl6jWHM6Drqda2C4WJR0Ajuw5a0V/o7GRqHethjuaEa5ifZUGPFUxYTD+8S7O7H6A3hYrxXMUJUmnVkR'
    'rHUQbhPPmnZAw2wGCnCNdq4NHgUn5ZFxSXB0J4j3WxAvgQ74odjPxJ3tkWVky5M7R8/yIrt7XDqQI60Vasj6KCN86pmelRPt9Eg2'
    'emy8JzuY/kwt0mSjGn3GvfQquRjVaMjTtETubi91i+91nIKo5MqAZhpKV4RS4YHKVqEf6s4PWBiQ0tU7eN4eNctgJqUMnLReUrBU'
    'smOa+0S98oH9XvqcFIQpl7Aknc4wTtM4beZ6zCQTJHzUflqobRiTQ1gz7rX7nfjd0T66kAHR6I0wwCY3R5gysUkMRmthc0ZPFRJE'
    'mpwFIWpPihqsGNyZSBEU96XhDaCxfi/q4sUsRX335LvaSbBd0jjmE8A3nmc/9vxgEf79sfcWyR+doLiBkOLEyYAIIFNXDbJAYsSp'
    'FAT1q2F80TxDOI36DYpLwQUnWwpWIBLz0+QRTRVAAH8mZ/dD5R0eoiZ5DCbWx/Aboym/N2JLm4FplF9tOdhZVNMeBQdkkt90myPn'
    'io5wouiVv2E+WkSsfKvMRROK72/QXhwv8+MbEObfA6OAJvk7GM7u/HW/E3Vd333tS4sV4iG5Eng3yegKWCk4Qr24k2AM2QEwazfA'
    '3lFgVqjSWer3uqiFAp6S8MWL2m3Aj7ofPl3B4HJl6VZjFNGc4SGh2Tk8ONh+QSq49+7BroZH8fhADuTOaJS55ChF/iVD3VVqh0il'
    'hR0Pu7Cy3Dd3HVRVrwiKlmDOhxDaa1itTT9MroE0YCjka9LhIUSn3+FlcaBcG1vGL84RX2EO/oTZvLSIz5tBOWoRVbsDNELJ0sA0'
    'NIyTR3cx9EYFfFC0jhCFrTN5gQhp5tWQZjeTdj7nl6gve38f5WjRTkCven7rbVM8Crf1+5h9Xj3eFEbFAWulL7uVAs9VuBoZgnSo'
    'tNysQyUGv0iHShxWxqndYruyClGOc2anNIqluE7eE8zsSOHYp31UNpFraxhHFLVsF93+TSMaj/rsBF90GguIpBUVqhMTK25cRgO0'
    'TbPDfS6UWSkWCE4GRkpruLDpZSM2lDDWWahZHI3WXmUNAqfYy1Btwz95SY/sZKxQJdo4MGM1cw/75kJxdkEjqiYq3gs8movSJkwx'
    'MVWnk7VH03z0+hx9F8f393Poo7F4Han4jPpog3hXSacT9zhCrH4Zd7vJIE3ShWwXcLJYazurNu97c6SnXjoekBKITFfMuZ3qwx5P'
    'enWKl+r97hVzAKUU71VCDlMl6+DybrgSzOMpEbaHM5nC8dHx3ge8HTY36U9GOme+23r36BEXE5590+Hgg5z3oKu/pinq0L+OntrE'
    'Hl6RqAalboZZhLIkDd7mJeJFBtsKkrgSxLb81hiFiBjj/TVsCS4bJUbzKAKlqdFl5t/3OWHVV7PSKnNbntzyj2J4Yn05Xo5nTT9L'
    '78flFrtQzmKRioKDZwPO8yc74nzhd01pywpYwhkGnneKSpFsKMMK/X9OLnKghlp/aVNlsOXyFrBMnEMn4nnmcn8uv7k3fc/Zexh5'
    'h9Qh80SW+AF2y05/jAGplYL1i4d5tnNzU8QSSc+dCf3BhnV1ilJYW/6xtbh8GWzpjKecubtQovmuH3Vn8Pm7hGLa5U9HXegAIn1C'
    'KKT+3Z1+OwISyrGtUn9LBxpdDRfFYmE1aMxsFUWpj1oS9dtIAJKUvGm3XiUSpNTCklSzrCfW1tm6kb7zVNGFexgAJkVDdHMfQsmC'
    '7xQtwLxtUlJJ85tNHEF0QpJU7/VvQL4AGpBavxdlNL9GeXOFKxAsG4UYFlK/Yofqds5DaqZwJKgB1wLLQgpd7NGXQ0MLerNq47iW'
    'zLgCjhLUnAGebQzl4JtwkoEEiQSM3GEhrHn28FYor5V2Ww9pmeYeBHU4cGipa2uhjwnOG261dpyQuZRU+xVXW17Ff+FHvv6ZWHNK'
    'BUcs7g8UQm1MQmqiwHdwhFklysNk262QAsAGqKy9tvichkqlOE2PlDipVjMLtFTUl4IkZlfppPZSF2JTvg1CvWCjcOPDgZamjga4'
    'QIvALfozBFOXmfJQJ2V9UobS11x0sSl1Npw9pzbZCu8tZxOtOBtmmquoXm4rXySvL4UpxBtsjLrFI/boD8oYD29lXBNZPv3CDs1e'
    'PyujbjCeYziRugSlolgzHCubMpyMpKCOOvP6k8ef/fIsBFnQqkYqrIoH3aII+ZjXojL3pGp5CUva6SdVoqy30FDsh5QCb3GmlrCo'
    '1dLqGp2Ar1gOnq2JLt/E2q3U19bDTjLkwz3nANclZrGuC8zg561xpzywql5kY8OrhtgsX6LKqw1VTK00h85GBr8cMLqnJVZULFEF'
    'QR96xgxCThu8maUZ2ORSgf7igEobNcaneBteR4+8XmfnKgFOg3vamHAjzmmhWCAKF2rzQ05ilQV9Oigo1PEzckvwC9il5ZOF55un'
    'y5ch+UaZ9GwPkmuUIaPeaMPkY3x4q6nlMya5sIdrq8/CRd06lkMEDILJYGQ1QmGRRDFjNbNqmlmzWjHYy2gIrZm24Mgqi097ts3B'
    'aDn6v25ORf8vJS9seePgnu3LL/kXyJe/PQbh9tq7yJObQid+jaOV2Htvx32zo4p51m7/POoexQgAmytEttu4uuiAHlgMLTEEOYxP'
    'ywOskKWYsjv7qqGzI64GtB6LS+kJaR0aZ7qpUV81dHc36ssjptsydXKZYQYA6njYo8uUo/hy7+Ogdvbjj+dORxZK13+9uPVXD28n'
    '0MXJj6c//kj4/eOPDx8BjkM1GMtl4nPI/jae8s0V7OqLSyTq7lNCLOLkT6zUhaFOOmPyEYY+yla90VUMIlrU1WZOlg1JLntNZkF6'
    'GM05I/Qo0AgcQ2F6YeqLi8rJK9duJtGiXivgN94BjRruRJh7qKHf43UtRnXjxADuCIJMtGksJHf7FZY2xXfHZQnF3XG5GOV+C0wS'
    '8pJZydgkdigdiPnQoeLSaBaa7CxuJXBN04lgk1sC3XGwoULxNN2gPFVVilLYWGSQd3wHkwfgIk9UsLBhfBEDerVj+ZDlvWbk7jHk'
    '96e3dshn4ARs+qKZgmYx17Bl2AZcyeGo62/Rvw2/OxpaJyJqLjRS8iR2dU3dhpNNr3xvUmBXNkqmZ9+sHOUX2MR/gYMfbY9Y3xGj'
    'aQlsVN1R4CbuUw9y6Ne7UUEcADVj/DiGDmBt497Sdy/88vwHAtBKPQM36zpPlaxLufqgfL3vcYdIwkizUEQRWatYXEeoO8LcjEvp'
    'q3xZQUjqlbftUdMwJSsrtlBI/S/XWF4yypi7u3UQBX+9SvIgtlnVBo1TtWGpbu7uvlVtzHD9ud35EMEG7Hg/DBNiH47RzhEI/XcE'
    'KA9lsY7oLNAvpJcAVcIn1oHihTz8KGA/4O0lHfe4qniQ432oQjqzI2e6FUU7gpb0LJYEC5vqxXwRAo9x2HhRg03QDw9/fe5dp4Ie'
    'Qa3yknMXV5sF0dmCSGSRpCRkgNEH2tq9meIEQCOXeP2G14hulAlM6suoPPkVVk+UBhwTxjgyNd0LmsIUdLoEAseEq5QuZS4QWDg+'
    'HQa2LvOzgSBbMQODsgUGdLIiQEi6BtgRC/loELK2UqMqIoS9vFK8bF4z3lYqlGVtiYndKHfutqZwwU6k3fhmZcV7/GTw0cslz8aL'
    'N7x1enhboOna8o/GPdTpwam6tt5YWdEXuSWAFBWSwNEdlihrFkowBzNlLaw9WdEgX1tfmBLivfoCydZmY5TIyHIf8+bJHWGpHyna'
    '5MAOFa8x3dKg3d2tTDyKsQt0WKbNuy2j4ePDB3greVEU930+74nSK1dZC1EbaIovHl0skVoKMCXIpvMHCH0JCJcxBnH0VSampqOt'
    '0oYa2a9v4pvcN8r2mnuL92gplveO+tdRz3yfNfVBK/mb2MVdRz+WRV1B1NU1weJngsWrz2aIX4Y367gT0QG3uEvRp5X1WocNktk9'
    'iBjxoLmwUl+xN0+F7UUxxjuqUgAL/NYYoZH/Ybmmgt27lNJtdgsJR91SkNMkV440URPPUtTgOk0Go8yFdYFaaKKhP9WHy1Ur+lZz'
    'co1KBWb3z6pqqsoTazLrOSF+w68jzHLWQ2ZxXnc+V+2zsMm/TRw2jz+ZsV49LiJKFJDrQHGQjzwteVXyW6pCVRQrI+P4ikPNR646'
    'ETnp/2/vW5vbyLLDvs+vuOLEA2AHAEFK1GhIkTIEghJ2KZImwNHKGlnTABpErxpoTHeDFFbLqq2Us6lKKn6t7SrbW7VxUrGd1CZV'
    'LlclWadSqbJ/xK6/6g9kf0LO497ue/uBh0jNzLoyD6nRfZ/nnvc999xyoTk+d51gKIpn3ykVXpTpw1nb+NDmDwN0qxz41vgf/9py'
    'Ai6LynUTsOQf/9Zz6U2fkmHZ0zDoDemFhbV++df/9Lu//Pkv//aXf/NP/+aX/5neD7HgL/7DL/7wF3/ziz/7xX8pvHghrwjBQG/t'
    'ipBUNBx+p5PEOU5zNWkwfrFo+mgxtX3Nq2AkHkWa/5ILEpXPzqWsJgl2+pwJGuY9mvTJKR7aA7rHhy5rTMoC1Ycfusv2wS4Es49T'
    'bBs7wQOoc+RJQmZ/IQPmszYP33mnmNS6FXeK6bFEf34zdoqvMLyDt088f9bFFO/1sYPxt73dN5Qq39hMLPenHMS9fftqJ3Y6kHGZ'
    'akB3OdCH3aBbpYe8w2PdKjtlKdV8S51jwR8PqgMf+FvwIOsAGR0+jLoXXDIdYQ6DwZmO0PrNX7egW7HkBCpUVDq56bn0JlE7sUUE'
    'yIZ5H7EMbRClG5MfibTx1rjdAr2gMELXmqnvyZwkhjWFnoxPMRS2/OnmxSUe0em9OiePxvaHGxsbO+m77be2tuK4ts25WRlZxJPy'
    'o4+eotpAssrfsSpgRNnykfAP+31KdApLD2atpk3pDSpMmmt/3I7Nj9vZ2RuXvXMqjd8nAG4UpW//9L8v7//IaMaaBiSS3/6rv7xO'
    'O23QFIuVDWzohz+/dkPczt8v3w5dl5JFw1l5GzWMtIIJsNoKreX2xt31Tw1sHAwGOyryGq2UHXJ/V5Dkg22+BWVH109qHIg9SuMf'
    '/HVuJ1AAGNtv7Kh0ufjskXMfpGW43eN9nqh3vJEnunxrkmq+Z00YGU1ExvFTlK/lOufjaMRxlt5NHjHZiSxpTEe3vvXLHIT4UHrV'
    'qnzvUU3SP28Py8HvFjBqvSB9+VmLZDie84u9uQ4zLhNf3TXY8fO8ibwo04Itx2apaLQtiaaGZNlL1eZ8q6WkPKVBySOxhRgYBRl/'
    'nzfwjzeu1lVlnqPyCnyx3HAkJiUGRE1V5Td0UuFk+SXNHq+mKb2hx2rg93YTn3bkFxMr6DYhebu3rMvXTGu7HdAYQjarOl1SZWwz'
    '5zCTvu3i6G5Gkqu1zSWBYu7S0Dg+zlib0m9kvJxHLnPnzILhTS6rzxq6kmbLRWVmyUEtTOd2ZhfZgY65/L88Z5Tf2kge88ud7JtE'
    'BF/OuOaMmDJsaV3lSpo5EF9FW3sg8Tyg5GMT2w9ndJ4ckZ5233E7Hwb0AeNz++HL/eZhs9N82Tg+Omg9ErsC1VZsOZiNPTzRUZHW'
    'RGFb8NVxfARdqBsh2rJcoUxfR8H5NvwV3xcRl4jzdR9ZF865BRN+IGsF0y7VeuZNfaF65h0fTlgsLh3XFV0MmrcpWhts/grodOLC'
    'scTHApXgfQUm2SaWHG+LYkns7smhK4U8tLowU/hTUnCIRfC4lwDyFXpsxI6s5wxEEcqXsFJVDZASUENDKo1a3AFlKdkV+SungIsF'
    'C0Yv+KZEDbCefOgEoeRsxQIPLa6wvg5woHCH+AYtOjkELUVgvLQCTAZ7CfqvrLbUjuTYdvUdZYKimJh8FOYI3BzexkOFRdHGKa7k'
    'WFHwX5UVbmGylArndlmIX5RYhTOuZeOYXmIJHJOIY41ntDm5NAYZM8CohkUjxyuP+DhiYtz7nph5U1iXMfsMYlKJq2RSBkkCvtwn'
    'TRBQAj6hBkTzi5uaM8OhFUghraZphoioi+NK8QlkKCSxiH7yXXLiBz8QGOLB8Rz4S34ERBAffSRIOOLzLaAvyYWoldIcWpVDeWXP'
    '9IEohITXWLjPsWzRDXfw+kVEHqCAsv9CfUb+dmWSarc3j1BpnVl3Mqi02ytBzdhSZUJYiQcwCuECJbgAVweqxSO80AJ+faBRmNTu'
    'gzQ7SJbMYxvzx4SZirqWj8Ik3RQeVu66tgkNOdaSCC6dsDfkM8B0DWSB2UlcPJUAI8EaujCFV33vcryQulTBpYlLOhCjikkSiz4A'
    'kz8P3kHiLKSmvkZLnDAqJib6nUNNJkHI1mSFnhUGWOHNlWyYBg99c/yfE9Df9LaEpIgPUkkUe6K2mAx51AbldPu8xN9BGswQf9eU'
    'ry+7/fbYmmC2xAyCXUhXEQZ9c8gqGtLXSluxirlQ6MYmY75apzsdFwnddspDuTp5gbJT112dCtzCwSMZSHYOplsQ9gWsb9cGQWGD'
    '4JG+UO4Wi/Z963JczSHY2LSLSWQObYT+DJQicuDjDGMjlHMdBgMN5qQNgYTGg3p2ifUJApHqEnDy+Yud+K1hRGbSWeDOVTK7LLkq'
    'rhOEJlIFLuCTey3xpSHTV01nKlKbSGkBBCKCMzgNvyypNtJKLbsH3oUMTYoDFuZS8okF9IasDuc8h9xUkSWoDTR5uv4hpjJWk97Z'
    'bGI8J9DxRcPtQ1bltIvF4R2anSgsim+4e7woRIzsvmPRUyDDMbffXKFdkEkNQOT7Ni04nngiEYAAFGSP6EuYNw6SceojhkaptlD0'
    'FJQhzsONvxr88gOQOJp3oCsPJvN+eVEuJQgvEW/x9AbngDZJc/p5VPYFi+gduQ0TMx6Ukz5fVK5NC5qr6mUSQ5c4RItiNHXrllmz'
    'GENZFF+WksWpZzln7v9W/F11E3QZCyNsa/OkNEAw7OJTDlcfwB8vg66MMOB4vV0RVYhPQhAdNBexMcBe5emMqwKNQEWxRFUoqVcE'
    'KlmyIpRU+cZgaXioJTVm3cUJbSHg6Qtpb5JwFXEVVCM06BJTeKIJIRuBL/CsNULndCJhl0X9qnWaWYkZQU7r8EW2rr4kBXFBy1DI'
    '+yaLASWPFuG2Sgwwrl2SrSTAJSdXMALQs1sHFFIdgFKcYtW8PWCc1FeY18BoE7fImJzGRyVQr9e/FBVZ/Tdf2z10RPMAiL4Soyhp'
    'VIPf5Y52shRv2AdPnXBoSF76c7tQUrTKo42VLb7EPLdR1+nZWe0pzzIt5ZVAF/siZpBsfEcyla8U6gsZlcax4eUcxDZ5G9GWDSY/'
    '/DFHV1hZFMRiFUmTJG9JRI/FhIik9j3o2/Z9DzOPeVO3j6mRlZEbTTyaVqEs7BJzeC1kQHElWU/q71FtqLRJLnKE7gcgkN/+8Q/h'
    'P9EwEtkNbAsQ18bUSw5n0uBiX/1/NMaNKoxvMuP8eh/HWf9CD1Z2aPuaC36EBdHZqaMD1ZvD6HojPAv3qkL7+dF2BVvq2sG+S2K0'
    'MpUeemJPLrHMvGZ9sFcs1+5XJpfYrs4mo9aJdVCeP/FGX8kjT1rTKmqX5oGWhmQrIk4TjA3D2CaXRMgPxBfSH9IaXzihjSk3MZkU'
    'HnbHNq4+H59IGOKryeUVliCVHoUPgYvuD8bNEXqlgZx90OS+tzFcc2DbfdwZr35BfW8v6ptClsYKH4EanAnvcV36DkYsvg6LOJtS'
    'FfodF3VVVYPN25/8mBJo6djQ8yZ4nFYhxS1A9duM6sCtSlWmNb095c/QUSMR9qKyhSsDILQkbuwSyHdE/qZ4aMFKQXmO4FI6aFTe'
    'BvGBKRYBkHij2mSGC2u2xhQct5YFhAZNOjFXIm6gm82qaFIKNYeWQicTes8rlCaVG6KV90Esmmapj9LY6ygWPkyNkvbmEGjPMUAC'
    'PjNprb2QvmrznwdZDS4YniX3aAqGMopOPRhoRr7dgiQTRT9ykXRldnJJwdtE2EjUKbL9AshNhwuiTXZvNMkvHjtlpMdn3rRwgX51'
    'IHjudR5hCzxFqTagnLFov8KnaoqwcUQ4XmIm355ienODo0DVGW50dPEeJ+ArORzmEshe8DFtUFixrc7QGr8KbiF/IeDInMDYelGl'
    'Al6Y/jciittV8Vunose3b56fAx4V0WtEaf171vjCCsQ0wJMJgUNXJ0Jhyz33gDkNRyWdhDpU+7dODfrpeq8XUM+XPmhir/VlxgMm'
    'i+vo2vctaEHXLuXlmsorA181TwvPslhAeGkKfIjae5hU3WUbDwRwlz8Rj50+AqCAaPb2Z3+BsGgA4GKx5UjHSXIo15W4mkyMm36J'
    '6wTwlhDhxQLOR+XU8j5xcNfcxaHiWVwxskBBfi1DhwDXeG2xOkykcm6PbZ+0KmDdvmf1hvEKq+64n1a/TCzfcAwwuuTPU1WNF47f'
    '6LOCMZ8F7AaSlFEI6FLYEKAjzk4PJTkzwVigz9mElPWTFtduO2AIiUu7AAobKgnosBRjOwRqelWmmyosBgUwhGialOlAPPI8JAAM'
    'tg8Dbq3eC6eW684kxMiZhGP70sdBVL8XYE8uihTcuo9AMfXRzv9iGIaTYHt93Zo41S99mMsF5jv0RusXG+ssWisS9OsP8ADF7sbd'
    '2mv4/yMcINBqBucioLPWINF8dD5HYsNXieSj8ypF00Fh6GGHXnBwm/7GcsliNTAbXrMh0AuCDmtWBZlf0bf6zjTYvjN5vROVhXGi'
    '0g6ldO0CYHkAgEQOuk1SO+aEOCVNA+mFyDMYMxCDiBpBDSpsRhuTUARTb7htHBYOBwP4CjvR+1NUMWrlWhnmhf/nVgMlQVXz2Fb/'
    'VD+sJ79h93UMDMQCHBsoHabSAeyxSzvUEzYUcPFh7SkTRxUsKAemsK5mQFWiDd7iZdkhWKkRkt53WRb3amiggFrnfGvjjrRRaekZ'
    'OnPsMy7AKSmOEFWdMeBf+JD2CoqwTmVZJsKOwEcrETBX8Y476EKdAO4rHhBo/J4MJE68DEWKmOvCNDrxxNtcnucPKgWYmaypWAJW'
    'Q80f/06GWkiWzd8SKkmsmj6o0hFAMin1cEkecgM1n69mzMqnr4atKdjzZ7Aj9whLuoKNwSc4HyuYjXsiMSvMvZmeFLFYqXNKo6nV'
    'R6lyS+oML9sHL0+OTztpiQWjnK/3+k4SEobpFVpSiGlxEposk6JDV9/xjC3yZp9RDjeyksYd+RA0ukMeY11aDqiWg/rEObDRpCkg'
    't11nsKxTYyATlXN/BLaQB+pi4eS43YH3QzraH2zDUJSTsNKZTewCFMGUDA7fs7D+vcAbF3ivgzaFQYfaFt9uHx9VA3I4OYMZbgQw'
    'jLdFEuZlgtNLB3pmgLHwLAtrCuPxobM6PUAXrH+rUCKZkyOap1/FkSjrCUHZr3qvSlrMVzaOG0FUIDKDId8zBYRPexah7c6MHSco'
    'shC41MIDOcldxIbkvBPbWCCw45nYgTEXns1YTke1xIPchZryEdDo+YsdOc9Tksl0e2pRun4ybELmYQG7iDaVWRg7+/TyTZRcsBww'
    'F4AsyzHE3A5gnnVuOUDHsiPDW6XfheCNx/KIIFUvSDaEDHULDNDX8SVfSdbE3+R0NK6kgPC8Wq3qcHkRkRP9VJ7MlNuE64M+b1MH'
    'JlWxmvMQFKy+ACmCOcVZHEeaK/dNICtw98en9U7r+EgcHXeabbmXVthN/yM/fcETs8lMMxImJrIWfyHLd/BMNxXW5nVF8yiCsih+'
    'IARKnriETMM13t27NQa2G3juBaZFVhWxwql8m1Upo44cSoGmQICWlZTEHpeFk3aeBIjg0RSLYE7gofQSx+GmJqzTOGATVkW/jA3m'
    '1QwNXPEcxhq9MdMcXb2IrV2TaOPZoN0inp8228eHnzX3XxS0CnxzJeVHxOtsPt64qiJgqsyQCOfroEzMRt40KIAtC4O4wgT8wRXd'
    'p/Mv3oQBGZER4dIJ35fM1/XG4fueWMOmowLSGV8r36uVrtZUK4lKWAMLR70Ux6RaOdEt0ipzUzrm1Q+NVfCzVwFPrcuVeP6i/GYI'
    'xvh2YbPSd84d4BScPiB+cRXxqcRA3/7o72CwvoTcD35QeFC4EkV4E16VtumLMY2r9HQLhchRlRSjXCq+L2hH0ivyIzTQ0Q2MjkGw'
    'yQOPHQyc0JPTkt2Qa5FYUuxQFFFL83yKV9Fg6+bYKJEMKyDRdOEnzFb3ZADlicLLrmuNX+ETmS67n9RqZbZZdu+C5h4pYFBRyUB4'
    'jJI78USLX9y/tX/c6Dw7aYphOHL37ss/+TZt9J3tsb9fqIu46R01d59U7D0U+EZ2xjifR5xjEQ/cRafvNtEmkqeL8Kze5dDBbAZY'
    'ZXvi25VL35oYqRU3qp+wAPtNksgMK/LWvFFt1q7oaP6MUoHz8GUWdcPyWL+PSfM+csMdLRPZ+h69PMeXV3Jq5MPaU1Afu57V38Wz'
    'BvKNzL1x//N1WfL+ukxHTgBUGG1AnByLRbklBtLlvqr7wf1blYp4+yd/AP+J1tFh66gp2ifNw0PReNw6UR8qlb0PjJKPTutPntRP'
    'U4Wi9CvnvjUaWWBED/H2Wrolbw1DXUL8afmOVXGdCzww7YEBFp0M+yBuIJjYrrt6dW2M9bPOceW02Tj+rHn6TDw53q8fZg4V7968'
    'AJWfDzCo3oAT+SGTq+yRj56uYcSCGgOefXTtfncGrYzUGU2AsX66E/ekvddrEm/NDw6Q2dre2z//9//3f/6+nEJGKW6Xxxr1wv5N'
    'YCj9cSHkQx1AtD4e4MbcC3ltIaasqYjPFigSnvcqAH72in07oFwLlYei51vBEDgLyB2M36cu+mI6BnWFjoRjN7Jo9X7XV43WhQKo'
    'CFQIJcX/Y1AgatYeHRch7w3KLPK2ohdIjMBY7tqqOvKjqmwzBZCRHYTWaKIBRb3Z0+eeC4bovK3qwDyfyXEEGfl0+t4pj67NujQd'
    'PP3p3wn5Voxm0gUdHdmc20FAZ3TNLjwy3hmCDaBd3z7wvVEDFwN7e0jetxjGxP6Dd++u7wQjJwhUj9jFd2x7QneVYSIO32w6Aql8'
    'MOhW9macqF4zaaxHMzJJbRUqS7QjSSOajTMoYuxlKDNtgbKLoSulHlteOlBxoglKlYNKnfW+uxWf9dZuQ7q3eTHcMe41wj8qcX5n'
    'vromEj211AU2OlOQvUanxO9NXgs83SpIfEm/XteDlRjlXp0So3OKt5nw0nJhSRn5CXRCPy/l5Go1KSa5C9JIoINf/fQv/hKYlUL4'
    'mWBoapRmzkfrYqO6FcneuNHK7ZJ+BBmLmOJ3aydC+oh5JNGfnM7EYDAJGu1moUdzOgnQV4bRJehOR8oKcJMIr9vAeLwpRyoLVQdb'
    'GdtIx9g4aSkBsUWoDwO03Ooc5pJcQFo7XMU7+p1ZcuWXQBv9lPNtvHdr8eryzShZy7uRA/m1vUOPsiolIfr2h3+VXtOsPjE0ci3i'
    'M5kf6QovAGVo1KdveysAdFMCdGeJS4Qyrxv73hSGMJipBJv0sWKP+zt5YiB9TN9nL02alUj3zQI+nErUxhBBBMXDaBIyyS7pc1sm'
    'YtEYNV4jg1Kyv8c4jiEYXIgskOXGksxBkJ4aua1uRAoAncFwR+rY3bsKgUQzq8iAE67KJ/VWEQH3skXAvW++CMiG1nUkwI//ozrq'
    'aAkJ0PfM//dt1KpAN7wcWhi6jAEsNnpr0cYmaxu0FeTlxK19eQ7T4z17dXlbaFujVRj4HQl+88JDM58GspYNkzkbCVkSLFiH7ycZ'
    '8K1sIoSf6pN8oFKsqPbVfoSxuH2b1U7KoYHCcnftzpogE3PouYAZu2vU6qUNXAIPp/U9mGOZ4Qk2BL1jxb5MYtAAtHDGAUCv/yDC'
    'G2BKOCkADKnyO1pCEDB2cMYIwghlX+tZSXi6wdQfYC6SzVIGlqUy6JhIbu5yfqKZ959KILO0oGPz5cAa4xFy3xnsoLxR8FuArbVc'
    'bDXR884W0cQf/5HYd6zzsRegeuKMObEkOpH7HigRGCIp882rGBXeaVCqB5ElpiF2XIwyCYfwnLhYsoxIPoWJjCnLgklyEz+6za0f'
    'jQOUIbqikblv1ntDNGcUIA8M8jLQEPqZ8yNFAYp/3TKcHtB7s00unLVlJXAs/YCNxEvYimdIMhB5TDYAVhazyKdScohySjLjIoi+'
    'i+hONbqC5DZdJ+2j1slJsyMOWw9P67nOk3xBr3JsKxG/lGxOpcdeQjZvoVy+caOMIYXw4BzjNOU8nCYJjW5FUeO+gqGPAWc1DQeH'
    'm2Y2yO2aqJFdsLb39id/I+TMxaHT9S265nMzJuyMmiiakg7ObO0eN01BShvXqmb7S/MY9KZ2IyfMcSumXcl+byc6tzCPGPa9HoLV'
    'dI4OBEooipF1mPFAsj9KqRFyFB2wN3H/Vbcf3RKaP5a5kmGzlDG25Oh1Hk8r0LG699eh9z25F4fizwlJ5lnj0J1VMb2UTjwxeqiF'
    'o/NhBpIoKpAmkAI94Mf2RoRylRmrFBEyio27iM6x5XePh5jqGI/N4U4KiPq5yMlKzJ3lGK6JvXmLkNQxU6Lz0wxFx7Xxwo2KTDG7'
    'XasiLyc0DX0Qz8hMt6e4i9azAnuejqjUX4YLggHzG8t1yNVCM0UJ5RSTudACsHXC3jBXiggjjR6uK0C/IhFcpdDDoSaULkUDa8nw'
    'XZL3u2tPMACVTtZwqNt6qmAy49rk9c6NkcfdDL5R2tH5Q4FUqIKuQ+VsrHyCkp20Zb7DhTK+7dDq0uEMpQxSf6JW3dgKdlKT9cYU'
    'IwSgxDypHEbF9RpYbbegs5gCypWuO/Xzi0OR9QVLSGuWu34UVxezhdAD4Zy3RJK4kXrlat35/6t1jdXScqbHywULlRrHjYuNLEij'
    'obI8rDcSsL6XBHVv6gfQ/sRzKKWhxmhg5mbOXt6rAGYnM0XLrLv5FeJlBOEWPS9RkfJ5YJpj+GuJ4uqOLbDP5dMSlSheAy9Bpi3d'
    'ZPEolXD8Zln9HaAtxQC6xlR6TOLx0OYgYvFre3TqPKVipxwDsbQ98LxwgRa4UXtnQWsIp1z7ZhlxvFyS0aSanW8lZDj4NCOhU394'
    '2BSnzfr+yvZB6K9kGRg33sy1CmK1nlnw3VrSPljSY/c1WwW/+unv/Uzod/vcmEVQDwKMmLbEhef06G5CGwPto2vppFNtCBowJmLE'
    'AkPb8nmbNrr0zOoLoPhpf45uTJyHHG9ZcDKWQNfEZI5XpaTl0tcCP6gJ83d1DkhcxZEmSCn0EToq+XC0IrHsxz3DjNy1lO9YMGgz'
    '7m5alpJD/9TGcBDsW6qSuAdgqfRzXRswY0y3ZSQQ866S/DCS3/9v79Ax3viidYs/53fy81QnZI1K2C6/ZyUNS9202ALTIob51l1p'
    'LJG9mfSDQ19jMLmCiW290gEjDQvMaM/W2KJts82EayoHexFX9egi6BxxL8lYqMnope26DmZMJJYlMcm0ATNp7UTe/CQwG00WuamN'
    'xPn6aB6j0kCo7piqQE9ridbJ/cuDRj9wsh+5fpqSyQdfatWtgNwBlr9gmu2JbfffmZ0YCvA1+ckCTrupS+WU7yV7P+Bulpl8O4eP'
    '55rOoL0hkBI0oN/j5eNNFTLPO4Be3dFTvRfflrOh3apTQ+Kn+kT8dniKwZv6PRYfzDGGrB4uQCXTP5TFDXy66KfrZnDU23cW8wN0'
    'NSTWRmPBdDMGdAyTwpzqMYRSiNawgiynznJeHNy227irtu0yqQgvWs3dAF9N79z8ddE7DSVuFZ0zEdXXaDTb7dbD1mGrs7pj2trY'
    'mK2ketYBgUFj6jquE4K4H9tLe6bvJjXPu6B5JnFGbf+Cevf2z/6PMHpjpU9DSsB90ME6QxuT1xlIIccB1pRK85UgL1mAb2ql/UTa'
    '2onay5CZsgpBLMQy8p6zPMtMK0irH4Gb3/Ut/1Xaco+tNygJzIUGg9c/+q8KJdMozh5TcInBzWsZLoAPN+wNe3Mz5zYORXj70JNm'
    'fZqKyqpzdHGhl54klb72LO078O+9jFl2u91olofY1Y1NcwitEaPwgY0tPV2j1rWnXQNOL+e8Gc8Z74tQc34M/YmG7O/G5h7YE8da'
    'es5U+tpz3byz0dvYyljie9Zd604tmnEbexPr4qnlj25uwt4grHRB0C8/aVXj+hR8Byi4lzHxO9YnlmXFE4cexUPoMXfW86XsOLwB'
    'dnrK1xNScwvYqe9d6nyU4ztUog2qboR8ZLQQ2OcmbDPWFMqQNUs/6By1zCbCu/4XGGHVtwfW1M0g4sTqYlrFYgEbKZQLslKBrxHF'
    'gOJ+GsuWHJM+GFA5QONYbSxcB4dySE+i2J8F8NKxKgPfgRfurJRBAsZG0RzcIP8/XoN5Awhy1oqbexcEIYczql4ioBZuHEcCPH6l'
    'L0gwWnIxpk4b68J6BCNCi5Hluu+EE6kxjPorj2FE+PDE7jvT0c0Mwj1feRDuOSElapQ3M4bX7spjeO3iGL57eA0CoNQ+bbZHb4AG'
    '9OauwSQpeID16vdBBzw+HfhjjPZZdgFwdHKOdOEJVsWFOKKnd8OG9JB827Ve2/13GpOsW6DAZXq8qVG5HhhN7zQmqkk046Vsw9V4'
    'NmUSugkL6TMnmFquqDv9QCFrBrZim4isGRe+3tMdAImesFqkOvSnwNZHHm2UfWSNJjtCXqtDt2DrdBJFmEbWNs62wjmhTTzXvT69'
    'od17hefQNP2Oa3KvGUsW32oaL5lPI33iabeZUst2P6Hr6TNVQwTVzfaT/llcQDPAVVvPmwY02gRkdone1McULMxJLocYdQmASnGl'
    'G4c29jfMVLiywE3XM6sx/xrC+wDjAwSetjn3rcmQzvv1nZEIAPqo4qNQobPU7xnqFKcAHS8Jdiq+74x+DSGurBB/6to+wXvo+c73'
    'MeG9K86nmClt4LmudxkIDkF4z5CncSzLXLDs+4V5SmBcy9yTrBqzCtnj9yohGig7KXyS4yblpqyj78W+55WkjbMlV5JEfRsr/BqS'
    'ULwty/QTyQzaKKfsj1YAoC8EIph4r+KVf0+Axx6XFxlY+isSGfOIiX3voCkGC1di4fZBvgNiJ08zGVhuYOufE5I083taZ9/Jkgmp'
    'upJvpd7rVJD6aJrMO7kLqFVM+sd3XtLb2bh31iqWdpKApu0utc1wakPjyDck7IJVTyqamznZ2yL73njZ4wZGIFGrc9gUJ/VHTdFp'
    'Pjk5rHea4lH98BDTNqwQUzRxK+eW62qZHJYLLrJHEzzo/ojrrnTwQNu++dVPf/xvhWorkJLhgA6JhKRWqgieOH5niXidRNQzBwfx'
    'UVBhcQhGZWKd2wLA4E1DOiJEKV0C5U1UAxBhNDZ1ME7pwPIMkhbLk7eznh0rhZvrd1NbnXmh11hyTpi1iYYDn9EQFxcvHTRdmPAW'
    '1uPcWsuwMicTd6aWA4jqHN3wCwN2N/OCdp4+qot8X+eCQUf9xoPudnuLBw2FrjXohw8b8sa5mxjyiFPWrs0dsiwkh736kGVe3Dnu'
    '+/eJXRmzxg0rBzO8GvwkMWutUKG09g7TbsQN3MRSjT3HX1uEXVjoWuh14LgjcQSt3MSQg3Dad7y1+UPmQtGgVx9ymxpYvDm0mjaz'
    'cXcldQb5cywYOp7nBnQCkDm2LjLe5RBghjhb5QC/JpaPj5oVFMqn4lHzqHla7xyfriCOQRVAwbRaoO/x2D7BSivE+a5lOfkqnEBU'
    'D7VFAf27AjqoUA83GFHLSRotMUEFP3FLEkXNcmogEtN4iCS6jJp1hBOqNnBstx9UMck1KPQBmHUDEvKY5gpPzlHyeT6Um4q5zZi/'
    'keZJ7nL6o8glmiqPesJatg8dvkqrWBlISqZoPDndIM4HDAm2GzqoqKQ89caJHKgjUxMYB3DajdPWSYdVRC0S7aU3kRk3MBT15g+i'
    '7K0yO0yRG+KFj7OFU+RshIk50sXKB1PXFUfWyP6mzpIZU9YMtYM6EpWscE0zTt/7NAzLWJ432TuQtwOhmIoOmqiPnc+A7lwvTH04'
    'dEZ00UTb9p2sAyp6D+0hRrdntq/uN6LTvIlvoEcCJ8AI8MzjMuoEzCpr88ge+4vp6xxLJXDPrp5XBZ8sEv/wP0Rn6DsoN74GJFyS'
    '+RC7XAU2h945GvdZ0DFSaUBFl4smQFSHSWDgDwZG9mwx9LxXZELxiQi8uQwPBX6lAItyWKwCCCV3loFEIMsmQLH59oc/vq3582n2'
    'lCwLBROBgZOP3P164bEkLlFuc38VGD5E7XEx+LqoyhqQewjsZCAwpRja4j3f7uO9wIBFcbzT145FS0INjRUww1cBG8o1sS7qwIF6'
    'i4VkjzuojEkaGmD8toXxAyM6Ki2ePvnGqgR0cdXSE6VEL4mZUvY5/zfpE95N8k2d6cnQG9tLz3SCpRMz/XhDFLe2tkqiVqtV4P/a'
    'N3WqmASGnKoC0/WfO0HoywwwC2cvKyZm/g//WWzWNrdEXWqFX9O0E5spfKCITI18g0HaIuRmyTccVCm0fdYUNIyXewvCOjJtFTwV'
    'seLpA92yzLCHV/B/c7Z+1d7J/gHlgP3Zv1Z3CMCbd/CBHzWfipPT4283Gx3xtPXb9dP9FWztS+f7eHXqyvn0wLziLMKBHU4nS9ro'
    'T6kz3UKXQ6A0x6aX/K7yksfROfImz3YH3f21bXFocRjAV3BLZzpDC47a5QGY1nLihK+Jg1qtpKMhXbDrQ8lEMBvyh9F5utQIz0iI'
    'wO/trq0PrAvMDl2dYHyV5QJTkCvH5wblYuZu6MWNIvNJmkjZJUneysTSyR3AOdVGdmiBXu57A86JbLnodbbtsdR20k2ltxdNJjzc'
    '3HtquyD0aKdbDSh22KDLZq8xxDgxgVdWYfK6S7qKlhNZe3z+NXaUZPI4afUwqQa012vhlWEAXUpqx6i8BA6QXzDt/OR9Xf6xpteT'
    'PKXSA7jFNAdfHnlH9mWxNH9VoZbMG44erQzgZlUw/EFzysnk4g26rUxYnFyntzRCYBPBtLu29wgjTfrMVwiyPV4tdg6U5dWY7ADr'
    'A/44brAYTXI6tHyirrc/+qM0XuU5pldcG0zBz2BYaXX+5ftZHbr78IQ37VZblgMHL+eD/2mP0JI52aUQUKkIETx43zvQHygjtv/V'
    'LEyCtnybDo7ylQemzDqlT2q4Qe4ZE60Z5NKgatAgEtXl0PgbQfbLKaw5JbenDyZvSggP2b48ypnduT2ahDMj0bLef5RoOckEEz+v'
    'wVSiXelVkPf3fvYekdeSTCXaMF8Vjd1RWXQ+K4Pm3Hc8se9bIwuN6di1RkxnMMVLBuQeuN3/JnMYWqhD2/LHKy3Sj9/PItFAxAqa'
    'QLQ0dEhFXgjO4YYgjXHzAm94oEQIZWHzjXVqAwTv9fgquH+GCtB+5UyWEPABFEueR1i0zFTHNETgNXZIm33YMaIoMWK6Tifv4og5'
    'ke6GLr1Rub2tyWvBRoG4eYUZ83DhGea15CY8JbZaOp1ONsilPh11pvRrmu/Em0yRW/RFdyZewmfaeiuWcJzpEAFdUUX01+wU/JV9'
    'mF8NcOLJHBV4VAKxWc/KeLsmU3LgoChmLhDO+Hucen3RWBLma8ryVMhjIs5Dq/eq40ljiSzOn/yJaFjjnr04YoDmrI520g9oLI2b'
    '2IWWy8ZYVejvhz9nr4A3DZbt0Uykw7jzOkz3fIR3XpVUGMTUFkTNK9OBCh5riwlGpH19JmUUalWhgaxCKDnomEsv1EGGFZpeDy6J'
    'S78Is370BwJfZqwyMVjKTZWQ3+kAfj3ricrFlZWeJy+yJ86JyjmxxHJ5WkRODps05DAYJbS6QYyc0Zs5h6C0cmYsWs8CE30Aisma'
    'MMDbmbgdq1ss4Cc83QRmwf/GC1R423DhoSutPzNqhvoLL9aMeBmtv/BC9vb3oChduyOLo3OyOrJkTA7ixZ/hzOpZMTYr9zgh71Zm'
    'j/hJdvhf5T7qsofFkoQK3a+SoJezrSAeLxkWeW9h6ibJRw6b9dOjr45vLeEWQxXwnyv/+rGYp+G+O+8ygbcSZt1dEbM2UlnBFl1j'
    'sUSCoKVzgy3Kt5VMJ0Saf6Vrh5e2jg352bHyw63wYAalJaQdMt6Fp2uppQL9ILWcC3ST7M6NbE5ExvOwbiewQ7y41JuGReXIw3tU'
    'KUOCH4qncuN3WcVm3lbB4fEjuqYxjspLZUEyK+y36lDnrClOjg9b7cfiYf008yJEvEwxGFJmN/LtExjf/uSvhErvKk6oxHYM4Th5'
    'V1wZFn06Dtf2aolie3xp8cC1zs91Y1ytT7IVJCJjGwd+q5HwQHgzB17HMM2E2JPjw8Nnot4CSLQbh/XWk2YmzIw6jccApfppYxFw'
    '22cPO83vdhYV6zxuPmkuKtQ4Pjo4bDWgsfrJorJPH9c7ldbB4iafnHD0XHtR0ZNWp/FY7Dcb31nYKMCm3ugAFB+2MAfsguKfHbca'
    'Tai0RMsPz/YfNTui2e60niyD2ofHDb7zur7/Wat9vHhZYdhgL5+eNTpnp02E80nzdA5I6o3W0SPxuFnv4JLklsMkuHWZkqzdOIaW'
    '8/GlAWQrTs5OT47bTVE/2291FhUGtOi0js54ovlU3vwMKd08M5O4tbV5BEN7dNbanzPA1tH+GUDoGboVjvbrp/vtefNug94CWJNb'
    '4qj+RC79PDjTHa3oxDhtnhyfzgHIb53hoaDDZqeTbC6H5Z22Hj3uVBpAVYB7zaOzeRR/fLjP6Yxzuz8+aR4hQmzU8ss0j/axSP2o'
    'fvis3ZoDvCet/ZPj1hHhY7PdBvO1PWfmJ6fH+2cNmDXd7j6HL5y2ADZtcXp8/GRO380jpK510T5u4K3xjXlrU+E284tgTj6YR+O4'
    'Pg8VFKc8bS5q78nx0TEvX36X+6fi4LD+aA4k2o+PAbZnjx7NhWv7+OxoH4in3Xo0h7gadeBIsKq5BQ6QZX0GrAcWs95pPppDhe3O'
    'M+CZB9Bc8/TkFBEgfzGb9e8cIW7sNzvNRiIAP4tVdEi25fOI0/pBh2RCfR6PiuTl47OH8t034b8sSp9XPEvsL9vJkl2c7B+I1hPi'
    'WY3HJOaW60A3g4KBitygk7/971m8bcReclShQb0d5fjlFsZsvLLtSV222ZSO97a8ADXjmIUaTEYwB96DeAdvIi33LLdX3KjVLi5F'
    'hZKPlkpZ5zCitpR5p/qNI0iDnDAfbRj6QYbUQY28CzFYj7+dvkxwSzc+OrTNSXvdgQgvvfhmWHkHdvaKcJyEuo5BXoGtzakq6AZl'
    'TG8Xtfgg0vbnn92IJj4/yimGD/pSzU2ICCNGNiBCcu2LlBoLPvCFM5Mcl+6c/oT+oxKZUTmDWIR/BCoFpRVuGSVroT+oOCO61rI3'
    'xHT2ipCyQ6WyCOj7FWfcB8t8E9B5Z7mTv2RMR3n+7xrHgDMOEt01zxHdlfn9f/yfRIuGLoNlcEgcO5Y+KKy1Rp0vZSc/9i5lUAyG'
    'x6jAmInv4clt3uGH7h4sPvQb5c5OHEa+q4V2Jaw4WBe5IIE8NJv0gxhpHi34185I57lpwb924nIWwzrn61HpvhbzQpX06b+8y22q'
    'G/eCcjwc+k18dQRkYSPy5EdSfnjnzp3Cjv41agc+btYwurMQt0U5tPOa4snmt8ZQKiQ92invxea91FLdUzj3u1nhrmn/x+2M1ORm'
    'i7z26kS0xOTlGt9Y6lpNYtRnAfBltRPHd3zLTHSYciFAfCZCdQazaFO5Kg4weTfdYYpbzsIbDLDpxH2ZEaOZj74jz3Vnc3CX09ZX'
    'zhE3offixu2tvn1exsWqbd4Ttd8oy3UTmBy/lIHjd3t3PhkMtra+yVjOY5yDmv2Nrdu1ZRFdzTi3vRWBeg2SePuTv3p3imAk/tCq'
    'fYJph7Po4wliDyigFbx0JaAIlBumEO7BGlvuDGlFkQdiP7leX/M1yJS5RlJIWQRDTP9kCRnjHZD8AXwkQdGzxuICr7Oaia49wEvF'
    'WcJCs9U5w9ePQ9fStyxKWH1ibW3Z9qLbAenWA1icP/9LsBXBWAFjdb+5Lw7A/EHT5bD5XZRcwTyCzrmHNuMygGWjyNW53iro1lKP'
    'eThr9YuFHCWkUJKYLWXpbgH1jULeRSeK1LeQ0nG/00NghLPtWvUuJgjI2OnPv8qVbKT5IePyqNtKp7PlSbqV7me9++t/P+u/w01N'
    'OXfRnp6f43XJGDFc93tD58K+waPkMhITc3oFxo1LSNDn9tj22VQZAsUKgCJQJZ4R57GB6Du1v5wCJGFoJy1hUY6eOTc0NUB0B+nd'
    'P4UamKkhWHunSy+WuMH0a7xTzdyMyti9WuHOCx1gvg1LxGwjl42oRZT4FGgBNwkMwY3M/4XnjGSNd0sHkaTZlS7eiFBi5PKmTqVr'
    '9bVDOwlP72etR+Szbzcb5Krebx42O+S+PmidPhFLuT+CbqUPgiq0r+v3CLr71A5zztU8HXeiW+P496ebF5dLOTiysgZGhWR6g3iW'
    'Ktry1B4BWQl1ZjzjZpr57pFcjrezNpcvJSzT25n3i5pKB8gifQKjQE+tXPdpOxaze/LDpTWmnGM+T5BsTjM/BkaGHlkXzrkVen7K'
    'R5Lp8VldUTLHTGGqmgvIFpIviEvHdUHpEbTTaHOgPKpD3thFZQgjt5H9cfihb1cY3DSHSDt4RzePmmUcM7KM3ye+Uj6F7NmhgXNb'
    '02AkaY/ef7DcXasAlvKHvdrtTze7JaXuoV6sWyFZRZPtp+bUfG33puwrYkJZSgsy9l6PzxqPxUfkeD9ri/bZibbJ9E34j0FQ7/fR'
    '2iXLrkIsTQwBBV3EMVTi2yyExCOvLJ7SuQjQBDBXZRiUCVet8YxbCr1pb7iOKzUFggMtH2r5U7oPUDSBgWOofGPo4/kqvJR9MhGA'
    'BrbE3W8OWG503+A+a1J7H6yv//OZIk4mQu/W0ckZxSE0hSjqyKKeT3z4wVhRlphTohaOQbHlzDROSMHOotU6aFbFkSf60wmQI2qd'
    '1X9ekCsOpmM+AFgsiTeA+oVpYAN0fKcXFnZQG8LpcoDcRlU8BmX4EqQCnlZjS+WrDtPT/4PRASsF9hB0kNQfPxW7olgAMYa/6BrQ'
    'AlI2n54qiR/8QBTHSspWQa+hWifIagKxJ2qlHdngy9GXig/vytpQPOwN8TINS3z0UfplsVCUPGsbBKnlB3apELdHA2pYE0qpuytu'
    '3SpqY8ZhYY/QLPzFbdpBiWpHAlU9SJu7SqILMy5XOWdtsQBSjLoBg4X6KZTNfkuJ1dysClCHbeR7hNpf81pGK4qUKISaDa7AABg2'
    '2EjrkmjFWQso20U11xes7SIhU2mSFLYflPSGyBmHDfHDunhlz7oeOmyhpSJQO2hUlgsoHbwC8wGvlYEO4xaOjw6fYRY4VhcEKG82'
    'JTIDAxOFE4Dt/jAcuXvC4mSkIxIhEV29DOwQAV2kETKRSbyFIeUt8A6VcgYiqiaG2qKDzhWvOCCaML6yokkFaMpY4IoatF2EBP+T'
    '3WJUIa/FqMuraIi3GPiAwNF0vpza/owztHp+sVD1nW7XG2OQc5XjxQulB1UMcwboVDneF0wWUcCEMAVoKVKHcD/NGwjOG31KrXSs'
    'LhdWMC4oqIpkuWJhCOKdKVFoI5b0+7J98BKVoLj+AC9HLxbWrYmzzoUqnFMWyOlNNKiRDVKivy0KJ8ftDnxhwyfYFm8KDdaiKx0Y'
    'd2G7oFHX+vcCGOpVOWoFrZZt8e328VEVGe74HKzz4hvUQbYlOj8QBQa3gL4kfhauSrKFq1K1h8wi4uHF0psrbapXJsHfrorW2Akd'
    'QHXsg85dhf5Mnn5Fld6nvPgYRKquv1bsPpvxvowq7Yrx1HWxa2zxjfHF9XqW2wY0sM5tdBu2QntEmERZPlD1ZgQVPBkbFoNGjuuk'
    'tYMLLoEBHDPxQWKtXCK1usGghV0cx2OJqjGUItrM7IdAecU0Q4MZfal6AKjGqgVvIUdMxQpDCzh4H6NclSK7PUCvGb5QJFbNaAde'
    'U1J1VkqM+ixTVAs0vmpiCprs0Ab+xiwVyx0uZKLInao4RL2HqQj15EtEg2hqnMIxmuA6HVrnuaYQJAExKVcbXWTokc5hx5SH5e1o'
    'BstIPoMJRmJPEoBJ5wlMKIHdGk798Q4vAcDdx6P5AK6RNZ5aristiBhutgFbABz/JbEdQA+DaaKxwrcg2MDzOO8fimGcdsQwGctf'
    'I0c3akcVo+Ky6AwJIougt6riZNoF9kJ+TiTnz3Ajg1mtWKN1XoNFWttnzrEWJ3nIErwSVsGgDTSK0CL1QF8tJNXFNIalEuRF/CZJ'
    'WQp6Bn8IsvlDmVpNcYlIRkohMfQuOx7ueybEgxIO6ntqQMhpf/XTP/yRIKAxf4SKyHZ/9dM//Vt0fUsgRt/KYrNWY53xKqFa3YWF'
    'wf1YpKSe77kuCAh3AgJCFC330pphXlPMmySvJhl7QFhBWBLzFaNYo5hw421quxjYrlqUbPFbl4WqYD43LU1eAMG5CQJ0I6EcDE70'
    'bhhaG4WIdGSteTWwvFYuTSKaol4WuhQDYSvkLEEW+lNbXJUWt4Q6CjS0ZEtXkgPyzDXGqHimCeZClU1nPoGjUDhZ6MMAiADj9nnh'
    '84pVDdelKhUtXwYzQW+QBiRlrhFax4cujM+LexUAng2JxELkwirBdz6pCkApqaJoHhpEcMRnhdwgFlB8kLbMhcHasV/DtyBSrjtD'
    'eyZQw6gfPq0/a+t1i2MvFOd0zhkmxLyna/cs1OHR2YhcO2oHHZQstahkgMq4Px2TNi4EYr0aIyrwFtBcBWiZ2qX2rElQlZhwS0cF'
    'hezcUefSq0hrZOKMoc3ve94oukhA26TixC6Y2iugtMURV6kq1Ynq7zsYGNRDrlnbMb78Nja8KzbMtwc+ZhCUhWN+QM2rtthgQBEa'
    'C97+a6gk3z+vvQAZihEF3xWV6OVG9HInrjXLqvUsq9YzrsXQEk+scFgNvvTDInT8Lez9Y2wMnmYRzdGkUNsH4GlmUHJbmUtUMD8j'
    'UwmpFfw2IlT+uSx/ydA65Hyqrj0+B1XuFrC6TdQyby2hhVBOP2cc6MZRkkniZCnx9a6w5QZNlfalQFSB1ZR8p/Oac7ssqnzlEv4w'
    '1Ztb+CrZWQq1EvgRTbdk1pAoxz3jj4jhVjE8Ema9z5emFDP5Bd3QEjHXBWsiOXXuktxKTALWInuVUuIoZ6y8BnjuXk5Tm/O3AKPy'
    'QATqkzkUA/4aVZaQBfVst64uLKS3RgkT3IqWfRuEdRAm6mXxeeL07Wh5imo2UcMii03Eou5aK4bXC69CQ/dxbbK53BxJs3AYDOSk'
    'IMzqaLE4ewJISHtwoW/1XpEwYSvFQ4N4l+GDXjTknjV8mKkpzJHUi3iO2bycNHURwVBj0er7LPs78d3ciS4aZT4V4pISF7e6QTFr'
    'XCAEYNAlsSc27gF1Rgg4r9IzqjTjSqUYEDjiOfPgxfrEqop9D8wduwLCmgWvJHXyXGISGdygJIcLB0WiTB4BaxZSzKAQqUYaQ5sV'
    'tbK0l3jvCKA1DUgfsV/33Cklb6OGHF9tyQmpwg8wwiQS5yAOwg6Ma0n8yKUm4lLeJbSzD5pPFR6LpbIINcGxoxwHR6RYdcF8eiUc'
    'Ld+QCgGNrSOoeU65h0mHf3jW6RwfkRcl8YW2TgpQS1vQRJF287DZ6GRVxkNN9dNmvTCndr3Ar9O1D+sPm4cFYfZdNKRkUZOPbMgW'
    'StxS9NqiNxnX7srBRAWfc3ZQGab/AiR2QmYn4Cu1etwxZBQh5xmhRd+5CECwAKaMedOIsSSYjeF74OjLkDMZZTPMG7xeHHCqAghW'
    'wZEsW4eRfNnSodWl8aSBcow0JumOiVDeyiGVXyQ1Cr0EWov9w+bc9Z4M/S7RHVZFWqjE5HVf3N6slXKlvEaGUDHNU2KJJ5lKt6r4'
    'gPiuKLKXu2TkwuSQPKGo9jq0zR4xZHrmPJHm8UDJ8sphN0pGzkPGCAWlGRLA4bfZRx7E7GoQepMT3wNN0mKbOR6U14MxQVOoldfD'
    'EHAIIxAKkhEy9RUKcfkRKlZej11lxfWg2+AACo5g+Lz4vLD2ovj8d+DPj0v4/HlpXRs01EbkkK4cs27K35/4DpXBGCktseK9eMUl'
    'DJX3nnPlwXJHnJ7XHhDekyZcLD1kyCXLCgxp2QvKAg1WGVuCP0FyRFwA2AO3iYZq147bIf7CJi53IZ4CC8EMrMO+X6U6oOFEI5F8'
    'B2zJIIwb8W3Xob1FkEwk+XznHI1U6EtKg0Kg2FMkxtSCapPCQ7Xb6I+Ssvl8il7foe3zboHigkNt7iiM1SZc3BBCQrq+oh06AIe0'
    'nfu+MwjFaAoIzt6BYDrB7bSApgYtVq8rQgF2K5CTctlImuLpGfQE7aV50/Wo9Zr0CYBuIJYgxNSSRsCI0KU7E3hMj1avO0OqQNeI'
    '6zIyVkwhBU06QTDFEtGxEYlZM2TzFDNTqahAmQhlZWxNUDUZB+LvkoxjMDYYx+8UP7/8uPR58K3PizqDgFIxg2D/8/PBGOj+Re52'
    'oFGqqO+NzecS/argPUTciwneF9PH7FlLY2m8g2pgJvxONyw3VLED5Z0l0MU/ec81bodraPx3yf3WfHs7uRNLPay0AnXWczhOEpUd'
    'QeHJ2uP7WhhsfPmVUfoY1jLWBl8sR+ZMBJvQJ9bJIxudFMC65u2T4ti+FAfK440fcFvYdYvUe7xj8lrumCyAu01hIRZyCNwPU6qQ'
    '/Ps9qj+bKzBs5camV2VR1X4l1aDN5RYASyppu4QWMaiq1H+czYdUB7ydgpiiNUm9eF+Ao9MYq3oVsZIOJ2oEatABQRkG3ATFnMOV'
    'aJcMjPHC4h2HyLTAVuP5kl0qPafktsOO9OKCuyaAFTV3ltwiNCyWC9Lc3DgyC6bIO12adNTHETBjg7+qPu7INjCEn6ZVKyXa5tYN'
    'hzSfiz/FisnGQe+q8i1lRyAOZeBHQNAEugPlDdQfaxLYRXl5dTKEGAdECkHddakDnDu9BgzhHv1ErSvtlyRsEVG2WQQw+F4tl98m'
    'vSvnVfGZ44dTIPxot59UPlbiaGXsPqObMwYVk87MLSzxgbENf+EE0AFuUuM5scROsvkxg0hAQXS+b+fsgeG6Wfq6GUin+2wpfs/K'
    'duDr5FHSva7Z+2tWlSffguniwItvWJ3fFgU+QgOD7dpD68LxfHgXjDwvHBYQ7ImNN8Mt+QnYAA/Z68CghSYclayeOF2Q8epa7j5S'
    'RlI+JuW0SAPKOEkXe2Eyt0TkMcDSXIVhAbt1ACIcss9mAuOKGNh2HyPwk7+v56AlebQsT5WzAvWsW67KC37LVf1EQbnaG4JxMQA2'
    'Ij92KxabA/RTJuIrV+XRpTIwhYukQQ86Xjc38kUF1M31BT/XhYzhS3+RFRdwkQopSAHSvsgmxfwgBJLc5pgjIssYRBdprDsnCjGe'
    'ec4Oh+70j7Hpe5oL4NKZ2BXXHtABHcWwUy+UlzfozturjNx40T5l0DXCn4JuoLYS4HEW74fAz3favVQtZu4cRJ3k7RvM34fJH9Kc'
    'raBos9mucvhTv5O5dYDj1jfmaKtZ2zvIq/xMVp4Z23DQ431RuVujCNQZPN+hx6i9Pm1U0A70RnWrZGgp0t7hKGqFFklrx/haXDZc'
    '4pNXgGiEYHxdGh31ItSy0ZIG/LJfTyidg+x2UYFo21xhkT1TD4TI+qbSdXaootYyd37ui81NtVc3B/ns97JlNVdJviVHnlaTl8FJ'
    '+3Ui9GFZfLRnGqeGnvaEgYomdQTdprs0E4lUWKyEOiz8nSlnFaPqA7LGRvxcpI73aDKRO4EJEV7NVyNd3W+Cl6CSiognar6PY3WZ'
    '4SJmS91m/meF8D56YeZBLXaOBBr7pWoGB/aZAUv0pe+rEYhqIhvp5/HTuZ0lI9dMLs9VGSSHyB4+3sXZwUAqmQMpAaPDhAlR/WD+'
    '9vJiTjYCTjb00NoFPYjtwr5vnVfw4rO+702y3pmHINx9+FakYgbJckVUIPEB40mxoEnBxidtw1jSqi/Dz8tiMowedfHK9dOgl8HV'
    'YH2M5wk0n/Zj0+Z0COafixeiJIJyfDxsZIalsKsmagIsihPuu2FN8HpuYDFyMK1+hs+G1CqcJjS9I6RQNyS54LknzFZJIzjUeIyT'
    'oUzJ0QuCDqZGAbYgTwkXxMfYRdUbDGCIj+klvCoYiThu64kB/POuVdzYvF3+9E558869cq26sVnaiaI+sTHuTNbHzmrVrYJu+Cxc'
    'oIXRQknvPEJL9kuZgPDuI0FuDPiBFzU8K+JUi7bGxkGn4KmWCqlG5KF7bILSl+iqS2i4C+R2ywFIclrhqIvvluMlK83rINE44R70'
    'gVzdX4h7VJ6Kwt/oaen7uo+DNukcjrlgz8lDXEVnfN6gkZ2Cql4soSUCoAhTmLAuNmN3BH2eWD5UQ/dHFeSQ7YcPKVlOcTLUpgtS'
    'EDt9wKPa5poYvNR2unisN5rB1SpIMZ3kuAJWwojCTvxBQ9GCDtQJHW0Csolni5LAeGFOv+8jLwJChjLSaIni/0XMsHZihmUsIkvv'
    '9iGtYAEWyMbjI/2CJtrbh9AwnSlHVNs/fpLSWVMliqm4ZzZK3GOSrehGfjINaZMJ3tg+WPcZ3j3lKsg76fUhoGUAoiKohPpxDJpX'
    'KZYDkU0WjeIE9wcW6EauHnzNFpaqV5IzqXo8du0TSrfe0HHpiAXLN5AP027o22kV5gCPP1Vca4rhvWMvdAby+NYHujOScCz3YBMb'
    'p1wZVbIYN3PPOiSqlCnUfmcVd+uSZyDMcxCpQw/k0eM4ams8w/Bp3PmjcyWfTzc3Pt0UdNyDjo7CKO/UIicWqRGb8W/yOZpnuq5K'
    'gIP319UR9PvrGIaOf9P5yQ/+HwXZDB/JJCQA'
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
                        pieces.append('\n')
                elif node.tag == _word_qn('lastRenderedPageBreak'):
                    has_page_break = True

            style_name = style_names.get(style_id, style_id)
            text = ''.join(pieces).replace('\u00a0', ' ').strip()
            added_line = False
            for line in (text.splitlines() if text else []):
                cleaned = re.sub(r'[ \t]+', ' ', line).strip()
                if cleaned:
                    paragraphs.append({
                        'text': cleaned, 'style': style_name,
                        'bold': bool(total_chars and bold_chars >= total_chars * .6),
                        'page': page, 'left': left, 'alignment': alignment,
                        'breakBefore': bool(pending_paragraph_break and not added_line),
                    })
                    pending_paragraph_break = False
                    added_line = True
            if not added_line:
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
    text = re.sub(r'\\(?:par|line)\b ?', '\n', text)
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
