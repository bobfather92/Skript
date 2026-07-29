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
    'H4sIAAAAAAACCuy9bVsbOdIw+j2/ouMrs7GDMeAQkoGQ3EDIDHsnIU8gM7sPYZnGbqATY7NuO8BOuK/zI84vPL/kqEpvJanU3bxk'
    'dvacZ67d4NZLqVQqlUqlUun5/VfbG7t/f7+ZnExOBy/uPYc/ySAdHq82smEDErK0L/6cZpM06Z2k4yKbrDY+7r6efdbQycP0NFtt'
    'fM2z87PReNJIeqPhJBuKYud5f3Ky2s++5r1sFj/aST7MJ3k6mC166SBbXejMA5hJPhlkL3a+jPOzSfL//F//d/J+PDrKiiIfDdNB'
    'stMbZ9nwfCwqDo+fz8nC954XPSxejHurjbmv2bA/Gs+NeuO5iaiYjdPepHOaDzufi0bSz46y8Yvnc7KGrZr3VxsFNjrbH/UuZrPh'
    'cT7MGsnk8kx0KD07G+S9dCKQmLuYVeVUkRf35h7dT6BS8mNnqbNwb/ckS95u7SZvRFeHRZY0xUfr3r2N0dnlOD8+mSTNXivpzi8s'
    'Ja9Ggrz37r3Pxqc59jDJi+QkG2eHl8nxOBWk67eTI9HjZHSEFD/O2slklKTDy+QsGxeiwuhwkgo6Do8TMSaihXui5OREgClGR5Pz'
    'dJyJwv0kLYpRL08FPEB0eiqGBDuTHOWDrEiaE4FyY0fVaLSwkX6WDu7lwwTydFZynk9ORtNJMs6KyTjvAQwYx95g2gccdPYgP81V'
    'C1Adu13cE0CnhegB4NlOTkf9/Aj+Ztits+nhIC8EV/RzAH04nYjEAhKRim3ox9xonBTZYHBPQMgF3thXix2WAdTPgKATRaICUs5P'
    'RqduT/Li3tF0PBRNZlinPxIkwxY/Z70JpEDxo9FgMDqHrglO7ufQo2L5Hg5xejj6mmFf5KgORxOBqkQBBuDMjqrKKk7SwSA5zBTB'
    'RLuCvCnpzhiaLyZi4MW0SGAGQXt+Nzui/Z83k53t17u/rn3YTLZ2kvcftn/ZerX5Kmms7YjvRjv5dWv35+2Pu4ko8WHt3e7fk+3X'
    'ydq7vyf/vfXuVTvZ/Nv7D5s7O8n2h3tbb9+/2doUaVvvNt58fLX17qdkXdR7ty0YeEtwrgC6u51AgwrU1uYOAHu7+WHjZ/G5tr71'
    'Zmv37+17r7d23wHM19sfkrXk/dqH3a2Nj2/WPiTvP354v72zKZp/JcC+23r3+oNoZfPt5rvdjmhVpCWbv4iPZOfntTdvoKl7ax8F'
    '9h8Av2Rj+/3fP2z99PNu8vP2m1ebInF9U2C2tv5mUzYlOrXxZm3rbTt5tfZ27adNrLUtoHy4B8UkdsmvP29CErS3Jv63sbu1/Q66'
    'sbH9bveD+GyLXn7YNVV/3drZbCdrH7Z2gCCvP2y/bd8Dcooa2whE1Hu3KaEAqRNnREQR+P64s2kAJq82194IWDtQGbqoC3fuPZq7'
    '9zUdSwmymjSPpkOcV83sAjigaCW/30uShpg5iZxzjRUofnAgRJmQjWeizjbybEckCIEEadl4crlyzylWRMoJxtMlj7PJ9vkQ0l9l'
    'RY9UsBkAGDJBAI7GTM2dy9PD0SBaV2XreidpoTJthbPxaDICsduxubQ/Iv9sq9gcTk+5OmeqtCwhZP/hICOUeDcan6YD1WBzdPi5'
    'nXzJhBD6mg6mWStZfQGfMC1FVvLSUo8U/T3JDOTlZDKeokQbHuXHUycNFin6jU0kV61kGYDvCVj7AgdM1QgWZ2OxxP4CSUDBZtpO'
    'DhEp4IAjIR6aUA66CCgeJt++Jc1DUfD3q1ZLlEiS/ChpUqp2xMo6aB62sY4qk/iUgGYgXzS2B3/3Wyv3NKhgYCUMFxchn5iSzcOW'
    'ZF2LmB06HrGaqCXJlfh3nE2E/E7SlXtXLv00t1vy2UkAaQGjA6YahBiaD2Jtg+rFaDruiYHLLlBam4GAghNYiydI+hVubGTdskHR'
    '0JEAyV/+opvp5MN+drF91JQZz5N5TR3ZpqSDaFkCkJ96wGRacn81GU7FUiOg3m4IVTfccYwiKtvzB9npqB3pit44YyzLkoFGZaH3'
    'Os8G/dg89jkJy4CIEF2FOX5/dTVpFNjPhpjpkDSTNBpidhJAur20uBz2oKWDA1jbgYcESqhHiY/jbCjEgZCHhkUU3sPsHNRXoQZk'
    'zaZQmUaDr4IQ4wxklikrGepoOhC62CDD/theaLpPxpfmdyLWgeysaVrtDLOLiaqj5oegXiLU1d6JGK0WqSibbma2mCT1isFDlrgR'
    'GpOT8ej8rvAA2IDDBbZ/0emPhpkYJkXE5kVHIbesCdzxswQ+2bBp6No2XVONIvYWfdGY7Qro+5fcYLdaktqyg1ct5EnxqzcQKnay'
    'nhbZ304HG6PTM4HucKJ6PPfokezmo2RDCCixKRHKOvBGUB70Z9T1irOslx/lYhz+9vZNkg0yaB13Vx0FSkP8r7N0nJ4m49Fo8t+C'
    'h2cT0E39SoL8neNOO2mcL5818M9Y/pk01IwUSgj8EQuZUDKmPUGEpgJpx030g4cOsgR13p7pCW0Q8wFNsac5O2l1dGOJO5ObktoN'
    '1W7DMAekd3QHV3VXrZSA/yPiyebb97t/P9he/6tQzax2UIidTPP3K4QnB8ohuhhPsWO8/ujRsv/GUSmmQuExySt2rPRse5Ssjcfp'
    'pdxD5kJimlES1J6I3ov9ST8r5O4pnajNV9Ex9S2gXRjkFKGJMT0tkFfVHl9vU0gvhXo/EfN/iEVS0KpEgbEFRyko2gf1Vuy0vkr9'
    'p2lRExtSwUEGNdIBi6Rmqbm5JCsG+VDs4/MC9K9ZmLCzIkXwqVKt08Gc0BSOsvEs6Auj4eByFlaGdvJf8Edqt7MSytxwNCsUccGj'
    '+WRW7LurGJfhWsGIwC44CE2iwDis9X6cCZbJCn8ewZjkk0KO3Dgb4lwCEhfZWGwS83/hLttnPxyn00xsxvtgUoB1WIiSw0scoNew'
    'KE4m2Rg2uWJkvgp9WQ2kbnUCNgfR+5EGmKJGDBtjyYjTsSwuWhcktnLrAkxG+eE4FQtF82QyOSuW5+bOz887w7PTz0VHVJk7S3tf'
    '0uNsThRtabyBT8ZZbzou8q/Z4BJ0hR6YbgrYHtu+AzFOxD9gs0AJKXbJvRSKDfIvmcFV88ksjKzmxQJrZ6dnE5sUki3TVAOuFTt1'
    'scUfj/N+XzQuqCd25yg/MrQp9KbFRCw9/5IsL8ZPDJ82rGiIYrCyC9ExwbRF3s+S7OhIELFI+lNkdWcQtTjogZSB3HE2wIziJD8r'
    'WhERg7NPTBQpYlyAOk9NP4CpzT9iHIUoM7CkwlJoMTVr4MDoypHHOTgdys0jmkyUIpgciRU4GU0nZ9OJj2N2kZ6eDUw7v/32m51h'
    'OlHM2G1J5gyNW/2+Iq3Xm8HoOO/pSoLYZ4KRhQRpql4uJ1sb8ldL/BQZgLtcAZJvBPHfNQiUFRuyJYSNpjebq5Q4lK+dsD090R+p'
    'ySy758htppIR26hYplpYqOyOGJXel87ZtDhBodIi+WJ5MxNh1UqXzmkq1BiYi46mJlV1SBbzGExKPVB8/SWO6mSmw1CppL9GenlV'
    'jCrX6giNS4gXghXiARr311HeFzuaSLeFmm6yFGSL3x5VA/aXDTE6g2x4LMTPyyBlVTS4AJuSZvMgFTTT+Xvz+wIrtUd6qXASmuRB'
    '2jkA4dEisETZxLYlflIVQ/c4ItPX+n3QFeSiqxd+NCxSER/M6z5Ikh4aa1+NwHYIVlNZSQonXFbFF4o3kQd2REFvsayJbyXklRDG'
    'oue5NDuOs1Mhz6TVUayFKMTFxCvIAmKkCuIsZYqnNIAYQKmilms5ZRlJ4uqDsG71TqQUcrUbUXsDmtiUFGpie5YzLafjtJC5HpdA'
    'GU8fRD1v63g4GmdbR5sg9lmlj1H4GG1L27g1qCrti1UPXBCeouBmCmZ1E6q1Brp8szqCNmTAmOUTEA+4GN58WbnF4qEbry0tpfwT'
    'PZ0OQJ+qksko/Bi6untQZB0J092HyvqqNZAfym4gU1xBJA0JspcNsMipTceX7LJochVaSjy1aiOjMqWc4thcUGBNKz2339cwenbJ'
    '9kZxiK3UTyepGvXSTYw/hxooext0B5Nsn0l1PRGL3BkwLqoa2saLmyhUxYDZLQaYXLXLFOqnGI2C19fhT2TKbUiFWU45r9d4NBeb'
    'AmU6+mScDgu7o/I6OC2g6wrhpCl4U82jllXP+4lcdAtQxMhMk5upyPgdiMFTOlPSnA5xKTmiO62iFUxypVGhxo8jhqYzomFCB2C4'
    'MrqZjE30A3+KQ5XC2FXhPzWfBBeO86xommESasZovJn2TprNPWuy22e0IGl5J+qHo/XIdgXjS+sCwte0FnOffkujvZjjX7T5Qf6H'
    'SO9JEMSo76tLV4FyIym4rHp9xc3td2Jw7nBy8+DK57cpn5yll4NR2pejr7fFQI1ZSWM1TYtbTfzbTUSN4rXm4ubFBLwEJCzgZ5hQ'
    'sksocTLBZnZWerNNA/l3T7pbzDY1xyTezhRTmvzv9vhKTK9gQnXGWX/ay5rNtNeDEzI7H1UN52ym6Z50NX+/aieiYgtq4hRbNnXb'
    'ye83mjWGZQuq6THzKFT5fPbsdDrW/LtSZ0lpE/kiOrIMJj3xt9G+Z2XOYDTGdPxFcsBYjRnwg6QXZ2kvwwz8RXP+JZP/RdJAX8FU'
    '+EHSha7f/4AZ+MvPeT+2ee/HXu6O4BCTDR8k/xwzzknKCaacUJxGZxKl0RmFDL4TEiz8IjmHo4nYmWOW/EnyBtmRrAQ/aKuCqTLZ'
    'CfmTUlYwtMqTP0ne8XSi8+RP2hacleeTnuyR+SIlzkYF5om/DU/Ua66E3b7Qpk5Hw8/FT4PRoVBpVvVp1DF+ozqAuqSRI3AuRTKX'
    'dYXzfNgfnTOFVcayCzkK1RYsssERUwyTl/UZpzKeJsfZ5FV2lApFdRM9FF4LCbnxuXiwAIc1kvPVTL2ABfSic3CQFW9H/akQv+K7'
    '4phfHhpeiOnUl400YDt+sWc+YT9+sULoWqQXRmGA7+wrmvtW4aReulBAFxKTL9r7kP1zmguZtYlFnd6NZZbMMcIA1IigXkv3U7bY'
    'Ua3JkQ9KC4QW7PnWBzv+H7KjAUj3VbqReGmSl9FOQWrK9DU4ohJAPqCSoiDJgysJSfcIYamMZdtPCqbblCescEbWy3KxrAqBPD4u'
    'rChUHX2tapPRQ8By0CJAVvyzPdW0GHQQlyuGwG5XRjLb64xFyYUClNBVVINJNigyBFzmilIC0KeVytHUYvZvbEPvQInXdTpiqeml'
    'k1KUdFl7Our06A/Fd4WzcZmG3ks7/eZpPvk1HYMm0jyXf12XAVhfR3L6q58dKNdyvkxV2hTwy7vp6WE23irepe9EL+VXJ8dPoYsb'
    'ZEixrj679viXKC5WRVddM3BwukKXQPOxIGhyB1xXFdNbM63E2BUGAmFacYUp0hEckYly8EfmO03RDxaaU9pOzAMjB6nhoLzwxmg6'
    'BLW7ovBpevEmLyZwXO7DR082KanfuqUW5j06906y3hddojlQP1zGUdJAZ8o1ihEGsGsYi6UPtji7os7meCxUuYdgmWjoyo1E63HJ'
    '6VQov4foVgstWLkmpg7Krr5Mf5jMJB4KvsvCPbJHdR3wmpR8dj2jZCGqYuBUptLFJLRSu8nMYQasQVEDKRwgggwtb4usOilyJImH'
    'OJfQngVp4NwjfpIZhkDcjbQdgQ/p8JgOgZx2Aj5LAzRlT/H8eAwV0WatR0jsWkfD2WF2nE7EsCQSLzJMMEKA4UzS6DTYIwqeG0Ud'
    'byBbDM/DNCeCtekxJ+yTzDQzuyGgVJBlJe17PY+2j6Tw0OVcbqb1xbY3+a+Dg/cfP2weHIh9nYaGJ4VZE/QD0nVa15vQli6ykDeR'
    'mUTRF8fuWCoYBJt5ZDaT3ctqDtl5Pgy4b8jx3rDFz/w43w1vz2VDj8dKKTmMH1B4UhC87hzKTE7Sic9n6cRvwe69fXngjE2JcDCY'
    '+cDpYhYZ6OP4QPvdCdZgpsO5pyRGWs1OndmYwDdyTtc9VgWtU5Tb29ddNb6OOSrh4s9zsxYUyhwvUmdmWlhXHjSZAnv5vhl06aiN'
    'LKYU+K5UUDNIatBicgJ2zbTKzF7DOFKqEveZwbSN6F/gIiordDKZteouvYlVeO+rSgFzHKWiCMVBF3RMFgL58YqzPiBZ1LHqC4qn'
    'aHQsxWmxN7/vVhI55Ow5aEfPXNrWlYfFWDnPyEnd+DiU7h/9BEnQaYg5Cc28TBpJEz4EvwjltUiPM5itLXDnbDRaRDiKeh19trXq'
    'NK2RGfsTXO4ZoVnARo3BHo79PiWlKROfmwH5ldyjVXn1hm7XdEvtRBqeyC4r2CRI9AfoM6CqaYZ3Szhr4zi93BiMhpltSdQhVHQm'
    '1LycUKLESjIzk1PecLA2TYgJxaPuSaZxTEM/SPt9ozjqXScOSNt0pI2Gz2zYd2XDKTNFnaQLUV9sQoyHAq+kmhlnJzmiUTbNV9kD'
    'iBiEa6/6Tu1w3ffZgmDWETPsDdWwuWMSBR9lLklOxNpqaxOjmDZDdt0kTcGOUelfMmnLJo1UbtEjlyrCU1GixzQ6e68c73ZdmB+u'
    'GCyRoHG2OMzMMMNSOiRKIDhY8BKhHBfF/IK6e3ZG6ApgQtvTH3bKEPFNjCfBNKJNd6bgnXY0CWcG0z9SDVdYro75Bbd7QlXBNUpI'
    'kp3CiiRvUCjoZqE6heT7Jh0MDFmsJzITGGpMD++kWDh316H3o6JAx0dnc36anY7Gl0IQpl/ErmOCzuadBJclDzOxNmH6DrrQaB0G'
    'Uq0cFjIOqn8UJMyUKlQEutVkBI4iQiAUmbx02XBmyXkH/YwFC9F6mxe9LBPAlcmm4dbIjKlBX7ugubgtVpqPm9NTIsfrKy3EmYuY'
    'wffXAYJGqVZKVgWqJjqLhbtIhMqpUxiXqGBdwUW8lsI6GnoGGx7ZUhhq+nEd87LupHPA/C1+1QX71K9jONkfexvh+6jhHoGtO9jE'
    'KgEofc+c1jvS5xp/ngu4r4f+JhYhBjNS6aOO9o5y0lFLycbLrCvWYtcJJAlbXt4DIRXaSXgWeMVZRg80tWL6iauWoDduF88ssNPL'
    'ksvgFiEQZlmtRO2EQlv2YSZXVJU5H0svjFU6cp3DfNhvyuZMD1RJu/6Ga5msocZJ5Ksq3mbSSb0qnxpo83SYqxvn4Ao1DEdoNNT1'
    'CfE5Lm+1qnbn5XNxW0AvmY80+3Y9ikzw79U9d47Snvmzt4yVIbWtFZI2HI7mKkwAOAHmx/kwHbzxuKu+ll2xlS7Ze1kqSC20dC8n'
    'C9QD5pQ3U+jbN/xN5hTJ9c2vs7OM0c6XaLexCQaaWD8bCA0lQgF/f+AOf8vV8QEr3BU03GINhzE7PmEiih9RPInhvcTur/lLUGR2'
    'wduh5kqQ6UViVhp/Xsg96+ysqwnqcRTbU3YoRXr1aMJ/PpcrLGj9FacC6UPu5hyK0fxCk64YVRm1dA3ieXQZXOErBHyGFJNafRkH'
    'FeD9lW0Ps6ac8Rogq81r2jqu+a1wP+dupkKLEsuQrAGtFmcGI8Ux59XNpOno6Ciu/bkI1ZDKa4MBa24NczmLqNlVEMGcfzfpWjJS'
    '/Ka6RKPz7IU3l4AV5yKO5PGYMWYSqS25b4s5IOaAq5DeV2WjQ40d1UQH7vki3QuoY7tqubXiF2QksLIPQj1jawc7oUPLL+h8C2WE'
    'mPTXIcyEFcCbx+g/IPaa7n5dui+G8+ILuaBBaRQrH7S28v2P50pHjNpo46qLd15dlJiQSM9jul1gWNaSXMLmp4az+GLBeitwHXzo'
    'aUzcZBA/bht4xiSzFkyHsHtx5eYNzbv+YNqTKAmU7LPi40iL1QFNrYduVTL4fnXZabAS2jqOqmaTpdHwa2As9CHJH3Ya2SoQrYGc'
    'LdiMdkJbl7djauwhB9yCOIitg9oIMnAOHs3wh4aP2HqcnvMrMUm/ZttVFiVdTYsLGyJKO5d47VFe4GFEZYJ2aeSqqW5FDdiqrlNH'
    '2lw8RNmwHxWjrDvvfHuzm8M2NqHrH8r6Z6PV87fmbORu3y5ENJJB1QGN8UX1ZlKlsJyvMdWwm+gY6BzAm9TwmD9c5sBK/9LzTXR8'
    'aEA+aHnmy20iN8TPdjJ0xxXC8DlxFuw2hDur9E8qoTpu+6AdooCY681nl6z/o78HwpBIFjNsekWmJjPJApyS2k2QypiZad2jW689'
    'TDVbIFN5nxov6F1pDydf/ooeubQaZ25IClHAFbo8zUS1mPomsij1nAXEJajHemPXru9YA63MgDOMgL9obCUjD4MYS0QnMUwLRzhG'
    'vcjG3vZdCz5PDQEc2jr80NjRznUwozF/kEW2arJyM9xFeLKa2TTFpEYUYeWR0nb72+JtCYkJrLS33ymAp6XYJnGP2INVmLa7qBmt'
    'HQ9HxSTvrZEjBmcALfHgmg8MsPRzJLfiJC3wxOq+9alx+5v2+3gG97N0TNg6crx1TYtOp0savGLuayTO0VGd1oyXxNEgpV7zzNAq'
    'gws/nHXpacbWa7j0ROJ6g0WOu27XJyiPINDkz881nO5uuxXnyKZiSbWoRVHXhtEFotSYaLEqqnlDZCp6fT/bclr4E5lrhkKPzuQB'
    'bZ6QI662xV2nFUolntOOvhD3nlaAWA6NXqLRF3zy4Uk2zifFwaHAs0C1q/pqz5ZXibvk45eJXffxy5mLPz5m0StAW2EXFuzFF0Uk'
    'x2wQZcZYm1Qx02WacKOxLS8ybkxGwbkDmyHUIYiBh3kHOtgCFFrxixj90FqHlM3D1LFl2h67kzuXy15WIj13l7GVtpdFHeXlIalX'
    'wAu86uWGoVqdAnQmsQsFexXnzzEmMAN2s9OzDRnOkL00kNgzYvhPF3eGkhm80qFHyaEANVvxoh0y5BCOx0H/irtoVGOaXdW4mvhv'
    'upiosH2wEBdYKtCZKGAKE96xdxp7ae8k6+9kk938NBtNJ276xiBLxyTH0EOhJuuJTMMKVuQrj6bCgAaxhVGHDrNsqCNNSOPnFQOb'
    'th0H3yOlKhpoBnxLo44ScUlQji/cPuGAvR0qsisiU8snpbeSMWFOawO5KuulQ7mqfm44hZ26FX31ajKDW7fDdSHh1eiWlBd2YZ4O'
    'NS+JNLoch9RcpUMZ7A9tFkBqm6BjVwYiD9IfItjD3vdLYsBmrvFa7FYLQ8oO2gzhAfeqMSPixuuNgJGCDU4pUJFtk/hsFma3VReQ'
    'tGz6gJzb8HS4Hflxmo6/2PN0O+wb/iSgnB0MfY8BGRn8ADDDroQDNpxm4TYri0ftyVgT4SgvbMQrXo8bKCDKDw7MevwQgpIc4YMK'
    '4iP8c5pNM3NvB2/ajFV4k1V7cwJXvel4LDYL/wsqrNDaW2gs054g9qapQGn48Qxi3+zmvS+Omn/fNILDTCD7fEVHhMNMMSyBoM1q'
    'BpDuolNI3QjHvBarXjJ9o7z8T7YtRBFbaHrBKOwSTooQkujOlREAg+Ab3iZi26O1aprQyzpz2psptAcy7/wkF1pZE66d2GlFqKYr'
    'rXiUtedhCsLMDKEe3lLxFW5+zP0G9yyY/Y7ob7PkFJIdryTaV1nN650N+sDzmi861WAYNUpplhiuHAaCbgjI0kruy1GLsOcWMJss'
    'tCyLB9kvRLZr9K532c7SGu+P5dCONCPbq3ecxUCSEO8QANJbk+xUroV4nYhgSmltw4HeZxjcMrCdFHTaOPKENijoZbVe8FmeDiWp'
    'V2yajJitLlbpAQIg9FhR1/N0XwVTuSJLqWyByuFeIeONT2KBx7/aUDRoprU+6Fmoc7LhV7Ph0GmCml/NlNKJKmAotNBg0u22xVBr'
    'OIKzCuwPZUyEAXlOk44Lv5+rnIaDZPS08lMDb1a+gOdY5RdSd0795NArP1LC8xX2S3FH2E163uEc8zujA47cSipwFYMtmF8vl5sw'
    'sdmH7abZgdEmeud9jicVTo25RljjpJ87tgfxWYmRrFQDn+lpWnwpwWje1CDb702znQ622Cvm4QDVAm7VfW+emFHBhd/SzRaTcZae'
    'rluro2eY3PHzfaukUyBmknQKGXtk0HYSbdlaIAsv2YuA1AkjjsRaM4aP6dGRNNPawUiLbGnxr65Vg+C2rvI5gui8GC10viHDIQGW'
    'cK3YzuuincPLSfZGLRSJ/fBKTUbrImtNyXPy5ZWDqIG0pPNNtJ/R6Mv0jKgt8nz26xsufW08tkGjPubDyTMJPYzbRTKXE6/J3qiP'
    'y8Pa+sarzdc//bz11/9+8/bd9vv/9WFn9+Mvv/7t7/87PewJWMcn+ecvg9Ph6Oyf42Iy/Xp+cfmv+YXu48UnS0+f/Tgzp26NuSfF'
    'baXjQCN2qaeXg82KK7suj42huHPqrgiwh3Dg4cMN8WNt0sxb+9ZHWpsIdeHGbIOWnceyS90Vv9gBV+yx528gJr1gADHJlxY9V9ps'
    'CO4jIt3zr0DHOMj8IVnEO/LsCYsSfVvDr+kg76sY2p1EcZ6NR3EqxE1+NsCDlsUw6ARgghDeIL0BG/0cU2O14YRBtsVWQRlt0XqA'
    'L3VNOxukvezn0aAvViRZwqmN3XuJsdIXha5m8kSPvR3tns5r+zD32YNWO+FYihf4Oo8dkRWeDFCS+IzzPcJCC76LhyXTjF+nlTxK'
    'Hidz2GUvi+3LgduZdhKlRWC5uEMsiGwKSTqx4fq/P4XlFmNsdxjNa1DIQURskaBT1GGWTEkfEelvZJCfFaRbNp+0ft51/F7yrnJ6'
    '6UrB1cWfM6vJojOlT89wrdRiBaYglVRdIVeeP08WniXfykqBZ48q2a0sqWAuVRZ83CKuaOCBoyg3MwPCDlB/IfZsS8lfku6TJ9Ul'
    'n9Uq6JShXuYBhwhR0r0BLbu1SCnwXbxLTBduMurzdUd9sdagiz51v+sw6ccUdfQTX5iMYS2a7I6kAiW2oaeB7FILOrzLCcwFyCw9'
    '3hcd8DK6kYwlLh2TWJSyISgHGyfT4ZfmFPQdeD8qHcPVQz/mhyft5Es1kQBBMPcRjpr/Apie/o9DRpAt7+VdOerQhYWlpwsLS8/m'
    '4Tq/yUb/PSiCVHnSDbMFBBwYYlWSeKrHYLwBEM23YheUVL3Po3zYbDR4xyZHH5V4VK0QQBks6Ok9MmrKZJwCvEIpFUIleOwsEqnc'
    'grme8KfpBQ6g0bsXlh4/e8wPitQtu13dwCxplMhqI6xd2M6NQcBFkpVhohyuRsGIeMi9UM2/VH+XuVLhmMiQIpY6vECRjKD6tUBk'
    'N8GVuvjICaKmfZfMGUhCqaLnUmN1tXEviKBCPYtd5LpRJlfYSVZ/Bvx7K6wX5j20QW77IkB1p0u6w/XG5X/ZOsf+zPbQ+BhlWfb0'
    'yWJse7ols1knIpkV9R2S2dZlyEJKmBaIY5BM6ECgdGrzkJtruLx4dFTA/ZW8eLPZTk5RfRriSHo+720v6pHU0mRRoVU+E6N3KjWk'
    'BafcWwys3FyAIchQBfVLrOcpXkaCkjCmNHO4nuOUn33q6FqwfxMIi3mkEBAwxWRyFLq+LTQLmQ5ctORIGuxJEgi+sJvHHCa/iUuA'
    '7iyCe2QnZhEnpxuFwHtVZeg0ibkAkxFFUflyy7wXoB8C7EzQr/tkSWDAoNRWyLRVrdnVhEhZzbWnCKYExawMxdNSFAH26e1RRDkR'
    '3g0EAiyAIAY24EQLVgHmYA4LT8XgQgTf5aRZmHGGTc7W8AjCbl5GHRZkp2aSt+nkpHM2Om92JffTy8pIUx8zb6/lNgtkohAzNSvc'
    'azl6UoKPWcbOSvRcu97kbCe9f8P8HIMKdGr08ceCGrT/s91FgOckPX3a8qcqmc9gFrBzOjKfgd6zwXyWgTpVpE/5gdwGpzULYtNr'
    '81/60gLLSjTTw6Kp3222jIuBonU8aAe85rSWx1xODa9BxVuCoFH+NPgciVVs3MSfg9GxBjgnM9+863qO7xKxR0mzpwFousML3M9d'
    'vUE0MzvruNolj1bpJsG9ew/hECU3vFj1Acl2hRQQHDFnWZF1vKZl3fliBEH0/r/uXw9w6HqdmZlxOzNXtzO+eJFDOO9cn/ZGzBNS'
    'ccqcmlewEe1ZKSlK5I6WPDOu5GFJeWr43hM8iEzdtubjp9BqOcApLvr2bIVbAFCW4s7DLgWnSP0nS20ldtg1QXZUSB4s882qGCi+'
    '+JUpU2aZGCaZj0lmMMnimISwBPX6+8k3WPofiQ3nM0eEh3rYFXMcgTDZwwjMiR5FYK49iDBgkhC6VfWsy6M6mHqw4K4SUmO1ZzP2'
    'RMSRxbJLXVvO6KauFQ2ePN0awgu6E/nkgD1X0N/uCxL2XQaZv9cQI9rYDx+acLKbDXi9+XPRmU7yQSeXDXZk842W87BFkpiedwx1'
    '5I9uWGJnMDo3pexHWHDr3c77zY3dg7drfztY//vu5o4o/8RZv/4b895svvtp92eR2V1YfLr47PHS4tMQ2BeIoad3qrSeLqrw7ez+'
    '/f3mq4O1Dx/W/n6w8/H9++0Pu4rAfdxv78gjzqazTN0vq23pr19S8A99ghIkSHDEY5SWo/u0Br42o10FBmnvSyGRVy9/N+3xUksf'
    '14K3Te8EznAV5+Fr079J/v8t+fqkcyFDGdqkxc4FdPxyNNV1ktGgb9pVgDsl+z1rngpJS3exjtubb4+2nWkutHxvenTPkFHZRqPl'
    'mEe9kSmLTkjEK9fV3jxG70SAxxbaBAvrEtKqro1XYbGCdyNRW/M6Au9mC7mAIsd5B8bCFIcLC//ageZfcuGjAY+TDifOg1ixdw7K'
    'XjrwZkheKCGMkcNb3PuY4VXkQ0dEcI/y1e+WXGn+HN0S+vY2olPWNesJiddzVDuDwDSmzjClvYuKuOu99NCAm18m1OlDjL2fqxNP'
    'UAVG+Kxn0ijyf2WNh61Y+G8xZOEk9W4qx2aGqNtOgrEL4z2KclGxoqqDv1tb2pvz4fH2eFtt7XjykZc0VslbBvE7vx5cWUueCwd3'
    'fbmbet79JnlxT9WP39vTB8/ujT2J7EMHZMmVYSllBoNR7+OwSI8y/8phEP58PDqtoKY/GGYIR6PBjmAXwRDPFn7sBoyNoNXe+5pD'
    'ZTeEPNkJ8ipeb6Sd6M4HOVf2RMzyX/LsXG0Gow1hDVKwfE+l3jKPTdIIrzSAU47yMbwDGbDJ0GcVPZvaCemN+sDXnfHX7CD/kukp'
    '6TFXw14HRbT50N5u//JiS70goIlOWifbeaH++EWVxHdrlBNcycUqNoohq1XkE7Hq9QlATlljehbUq9m/sN4f0k0ybVgZV8l/UlIh'
    'GF9QydthhgOD91giwiq6kmAj20d6x93R34KsTkKTM8lsw9OIOMFM+e0j+4gYS2sttqxY2j66JqlxBVSuY3JCBbIAUDy0m002+oza'
    '0DEsKHM6k9H7MUQOh4dvSD/pKO+FRffrxLJxqHAvuN/LgW0aGexe3A1I574qgGSs4oQKjvzTyMPoIohvEROj8zXWO7oC1534/hPc'
    'norFaMal25hSKLRuqLamhdgSTmD9b4LOGFnIIct5QKpaID2UOmhcT1JCpsXaDrHB52GUyhraMVa9kW4cqKmogCEubXw+2I6sc8PC'
    'I6ErLGRPViMxpZxdg1fbXRug/aoIVZ7i62heyUumMXiFetD0u7ZcWrJMDY13x59wSFo646qoTHVivnAwudxxVIq0z+Xx0Yv1SZ2W'
    'wKEMRtfO+grot+BaptdfiYLf61gvKcJB3xi4YK67E9iO6q8Ucy2auaFh9lxSWGjWg2iHDk/6z62YTLGSTo6eNWKTgOzoN1WdpsGo'
    'WiY1Pg6/DEfnQ9PgsnxDxOcgX1kYhN7rDEG+UVuC3WVzhgG3XNqbTPHZalFBnn+G0L1HGmSN+9Jz2FuQEtUwQMOIU835tmqjbO6W'
    '7deNgvtGLLpN52pWQCPM1TfDwqlCs29Is8gbWcolfiY4bBIwTRC1FKPRed58N6MFbiJT/cufEGRTYco4S3ErMJ2SUHvELGNbWKne'
    'eQAIs32RH8aMRRLexJVjH7AdcQeHOFkUJqlU12jzvK3AltDH1JJFyLWR5wRMHY1AmxHVy5RF3ke1Q12eORwJbb14GF1pS5sH50LF'
    '299A3tdCR1a4ATpqRqzECEaeRhUbC3Ibk1MSWKNf6qiFbizim4Kjo14ebawejNLN3PczUpLt4ejws8+2gW0ZyoRzWt3aUcJPlOFF'
    'X5nwa/lBu0Gwx0O5c33zDYyABwgDSaf5tvIB5SSMA8WdKLY3pYHclWrglXaeoiUv0BISRfrl0Ge+yojqCjIYpLLuyLhLgJ6Ej9t5'
    'ue3KC8meUKyfTtIKU5BuTpatsdnQPFJ+drB63cODxtpkkp2eTeBBM1T9IAKasp4NIGbhGB6qHYK7bX46PcXt03IyfwGKEW2qMxkp'
    'VXBhST6oBhO0aJQtIlpQho8km17bM+ZIx2cMz7CqjlE75kvwcJRlDTGqqusZ7YQY07P8kNGoD6l157BzYAGsyuvgmI5cH4ikqGLf'
    'G53CGR9FQiU1UyEcy9QNT81I7YG/tBeJAmlHu9GlvELgwTz0YB76MEWBQwPzMA4zPJNL0Rgbph+2bmT1FPJqodHGv11rfShYe5Ma'
    'JqFO2s49rGM8T3ForYHQU2LBeTBlH4MF/e4wyOGveqKH0mk+hMhoYomO3PY0KIFeCyx2CHH8PcmJCHnPPyQSmSC19sM4EPTj0pCA'
    'PhEEuZci96LFxN72SRZwvt3buTMw3PGRXhbnOR67Kxlligix9WZ0no030iJrehzVg7cdGyfZRWM5SMVtKJs8y6WnRS/PmfRBOsmH'
    'C0zGYT5Mx5dcBjogcU33ii6fPNvlMV1YGmSRPgRZzNvA+kEUvKDPlo15M4SyDOLwuKIMI/PI2N684L/vLrtQtFXH7AgFGbOjWOLk'
    'vW0x+SVeJVsA/0Gl+VIjvFxW5qMafL7CLeUxvZpb0cI3X5xo54FAMFBmyANZwaOhV/EdB/SLiHhqM2JNGGejwsX4evha5Vdh66u8'
    'dCkClTW6jzZPcEmvfBtHR3WqwykR/kkAtNEyCrI0oguQLVdQMvsZ+I+z1MP2REbs8gobH8s2lxEmCiy8NB+pewGC/LILXazjBHHT'
    'CRWhD4xJOWFpD3AcV8lAlttsqE9jaM0sNd5VbO5kBV7lVw4fcQQjjgoKJmg/hL01apVn66pZP6BG9FRZlncMszdSsOIOMCUnefrU'
    'TlEgHs5aVqxz8iyVpAjx8Q6kwOstOuOtJkxgrS5o5TYeVnffqOuexmrhSBuLXhF43W8A2kbWB33DDStGvLVXEpfyWnnh2LFMxyjR'
    'Mkr0DHeDtsJUCpSfuPpD3ykStXYxNkKheZtZdKLqTFyhKVNpKpQa2lO4rcVh4iuAXq0X9HpPhaYWXIWsQw9Ww1KqgmWmcMWyF74M'
    'g6prV3VHwhW23klMs+GcjbiKtA/H5Xpfh7yKWj+0oC2NEUSfhREN7Y48JZ+/n15jOuL5LFSlhlQhjmVacPysivKmBgvrhXrqmlE0'
    'dHyv6AGX6IGHC6SUQMQKNLsMcvQYmkcIm37xwumw6qKXShrAAtfs9X0r+EqOAlXYSXxO7Abis2Sai6wdPCiT8VQJN92tdLxGI5yw'
    't0e4kHkNYDdfH7DiNVqqIxOvQ+o/dpFQdWshWFdq3+4cOpTK5vcMHKN/X6ls9y/EpunAsYL5PD0DI+CwnZz6MjhHO9OQbOrgCxNP'
    'ncTTffpOcxwbaGxhidoTZEqTOZSOSUe1E09+SOSLdHVcjdShgHQx4iOKLSzNHuaTiFk8cnCtTq27vlQzz9DneG8vWWjVfYh2pZR0'
    'j7s+6R53b0a6xbsk3ePujUm3WEW6x87coPlAV/mne0fkxeuEDnmXFm9G3md3Sd6lxRuT91kVeZ/WIO9SWZmu/POkrMxj+WfxDoZJ'
    'n2XRgTLnW1HPlrLRIpZCRt0pexE6oh/MM6feeudPlGAVvVjWsY/K1aLBm1EvHWSGEnEyxYFk/5wKldp5uRJTmsEBFX/Aw66Oa4Gp'
    'SbXc8A6ToNfeSYy7yHmGWn2AJql1KG/vzdeglbph6z46hEkBt4j9long7MRjAqFbcn+WqthjzWyGJ1F7RaYASK3OOMOAas25Zuf3'
    '7lVrTuyBGg8WElAIxvlpk6GTNXwgBGxFTO1G0ul0kkZAssZzJVFAMcGySeNFIyCVjPIe3HqmRAmoucdU2Gf5T9G4WiEoOSzVb1Fb'
    'RU5G+d6R3/Bz0902evZmDSBqcpYF/ANR8wa2fN5aH42qzwonrMjtRax7s2NRWbfCasedh5bY6iTMOuel/ib7mvtqd1fMboDlGLzU'
    '9FXMvhyHaXggCpmUKAezWYKeya+zRzd2B7Lxd/ojki1WqpxuocRIwKsM8MCEGMUxJMkHcxutamq9WDUtwks9Os0zvSSMdbQaIguB'
    'Hiyz5pZ442xN3oLB2ToIikzOJlPDWZTUdC3xEdBgZm1TobtAhgWKMJP1EnBKANQN6VSKvFEY/cKTfl41RFxXlAwoq7K74ajuyPop'
    'aJy0u4JtLOK3QCqE7gtO7T+JH4M9cMr7+TjD3+lgSwWRpuGsXCdHa84kof2Jzx85vvR0Rx9nJZ89R1H+1IfYFrgb74kDxZnO9nSR'
    'FHlBAn14/qIUThgNJAbweTJrCj8rgUhKcbPeKTvD9RRfSCaOiMSHtaRZeF9BOrh7IzSbROWW6/HccgF6YGaSGK6U6Kulx9v48lA+'
    'ZtklkUQvQ8HtSWSQ5iNNxrhHtVsp4+01vhIextzgZmi7/GIHe84rqrXCnojUOg63Ll2v2LAh6eV1BQFLe58s7LU8SRb417vv4JCW'
    '9VdQIe8rHkg3o/w7b08tAy3dIWJEqOdqUdbMIC0mWzdp6iZDCEH592sOYumlWbi0bVRzfYguBxfUcn8bHN5YpOhhDJv6y4x8EFpU'
    'VdEgFrxbSuPxG3LHhz1yF42ZMnbS+OdE5IoYr9GbFancm89naPeOGZ4dhFfP5MkBk67ODdgceWrAsb+lRIJh1L+RfkNKdG7MLsT5'
    'LnHGwTu0tuMwF+RZ+od5RBL7mZxmRKKzpX3pdJV3Q9FIEF0NLl5R3xwI5V3pHWSLY3Dej1vDycLS+iaEa39kadKq48TmOd0FYgrK'
    'HMHVm/A1Ocd/jSy/6sE1Rf7gpTXdFBIM514uLUyYgPOQNohvhijdAeLq2bxWyDR4A9iv3HI7kK8wlVzIYI2VW1XNKEYpIIUIqWuJ'
    'YQ+5+wq5HKIKuu37GJYMQEwSMzh4ysgMmQYv7Hh5uoidRrO2fA0OeCH3OLOz/iAZhmKO2sgm6bPcJH0WrGSbTT6HrBQwk+jY5xZS'
    '1zLU5xbnF6LR8NwdojujUP5c3WMH2MbarpqCgZS7KjGu9gbTfuY96S7TmtHli7mHgXtc/VhPSUXJoLXMvkoLoohVgg/vh3D7QGmD'
    'Llmd0c+hBpJE0aGIkuQ/AFnktJKb5CfZxa94sRkXEq3YjKIXQ0d6mr5D3ac5Unc/vwUXhsfZqXnEkzj8zioQni9f6RUiA6r0zqIp'
    'rlALTmm8YG8GasRFm203vq4J2r0p83x02laF53w9xDRtC1zjVDDuw32WjosMJA/+EKu3cj/rFNND8UuI00dw1NdttZOFpYBkdPct'
    'IbV4gQPqhBvfVhYvORjMoyozHLxdizf1RBnkE7VrDP3t2hwvtjA1AB1X5sHN55aoIQzPF/CaaEivnVviwbpDXhMR0OhvP1Kgyt/d'
    'YIXy2A9gn7gRHVx4cRf0kX/Du3bIjKTixJpI1/l6F79J1KrRNeyJo8CWeEvE8uI1hJXP9HLgtmwqqx/guDsfXiRRICJ3jA2GWob6'
    'QJitph6f0jFhdWdSg/PPNciEkUpLFWL/UUQ3OKHywecDjWgG3dMcut+S78cmg9Hw2EYPzvqNOk76dHWmp9D88hwynljvuYW0bOmU'
    'J0NkbcTn6iAwIIlJIuCOiOnSfl77FI1cr5YzX0d4cMI7xE/W6vm+ft+bBeWusVLkandIVuberZvsDRv8DvcjyAp8bXTquMLelLR/'
    'sFusWXevgem/yz/2u95aKPOm+uvO9jvXnwxSmow+4ggVUXnZRJugF/4gboR6Y5g6GMI5rDRoo6A6gHjrygugLUSZxbnkXJK4YStN'
    'irs+4TpuoAjVjhhWX2LP3WUD7lPNeOGwdGNVUTk8gq4TVcO61ZX0VPqQmJN02zv/qFsuae5ze9bH2TujV/cVcvnWIWN9hICY6tVV'
    'GaJqJQgI1c/ej/IhKDX0RQdzZRaU2PfZeCf751SwPC4LBuiLpPv4x+Qlvs3qpOKDRI+91IUfwRbZpU+CWRPiTNjSc8brQm1Qs95o'
    '2Aew6F8wVj+PRtPx5EQlixVzQ/fNnZR6wfIbDM1cKLsWlgPrlgyWqHsGr78+42xkiUNdUyG0ll3Vs58hOt0QHUsOPcz4ZOUKi3eT'
    'lP6LGJOuNCBHu+AQEqSf7fhfkscLLf2mrQN26fEKAwpPBB1w8KLoU75dl3glwxkj4XWI+vgWRDUMSMp1r0181B4tqFuPzMKTlnmX'
    'uOmNjRkz2l79IevOLz6V6DoZz5MnT7o/LuFK4dV48vTx4uPWn2CcF/+AcbZSiBR8fLcMgZmkoTtjl2cxdpGM5DKM4SMHk/qMtPTk'
    'yeMnuPH3GGlhYWFxYaH7hzBM7DAe3Y5tQ2yUfhcV6M7j8EDUWz0XVvjwCT2fMPGmZmVbSyvewaZ6tZVAwqdaYXjnxYr8TU5QX90n'
    'PXiy9LgLj1/bNFk17nPiN+kaXDGwgkeCEgNqP8MHfTUsFZVFNBKYxEAJALf2tQ8/fXy7+W53xz4CtTj/41KgjvKQDdYFf3XG5kcv'
    '0AgdhcODVVnVbQrQOjfUM+HqasWO2u0QhOLWjoLx/c9dexZRCyHknocMxruII+Nwh8KM5xjt7ZmrN99YSlSZcBRxBFrlRupKDVtS'
    'Z+JRp7be7RxE6EfE9RviwUkENMRTsalCwf4FVZvSHk+iPaaXYv9junzTzpqr0RU9lZOSC9SCRi65j3Sv1jNu/8og1tf+744rPM4W'
    'ST8nboV6ed4j9PXoB/UF/XRv3+Aj2bvw6NSepN9+Cf1E5bLTJXuluIKGh+qZd3azu1IhabizOgRI3TjZi6ZxoSN3YTBh1A5Q6V/y'
    '3eNrSgzmsiT00bkr6Xe6/qVJzUz/8z/eLlwyjBdXAZ+aF3vd//kfYAf+DgZ3R2Vm1Q+Z4lXhrrKQVw1UfIhA7utqDnAmfgN3+YXH'
    'yRSX/efxIfMqvFJTiYuK9CBLM/cThhlE9jR3D6aH6JzI8zQfxVdCqBXIVxaN27wwuqr0W2hqu2V2EQ0+p04DfkgW5BVc/8AgcqNG'
    'lsDzkkkyFauwf2PRnFqLtiXpsXEe3O74EoyaELi118uKIjnMLoXur08WVFTpGkeS6EsnsHmzyV6z0652mO34/clUQzB7a63bFl1c'
    'w6cTWLcN/giO1HfCvHT9grgO2Aa4wXNwoWc2gUeq4kDlMbDvB4kahK6uvMYmFg0lUzXWsNEDAI/wKd1W6H094zQtnRUeQZslolPU'
    'q+H1o4d0vXxI19khXf/3D6kTh/Nmw3tVPtCC2rOzBEzVwKtRdrqgDg6vN8Zuq3c83s9Kh/sZN9rPDFFvML41ZuJCbICIW54/+Wr0'
    'dGGpQlypAkF/If07d7l7jS5LUx7hD6E/PX+ePLsWKdarSLEeIcX6n4oU0G+GHtcgxeNuBVeoAgEpIP07k2KxghTNOmwRpHcxXQZd'
    'd3Meg3BZWHr69Gl3YelaNFyvouF6hIbr/24aOiS0vYdnOThyLixF6BnS+fF+qyYNWVXp/2hKf5ympCAtdJ8Fj0qCf77IbiHQWWVp'
    'ORudN0XfnwmIBKmQueovxaxq9efQrG7BArnbUI3x57UuepJtzJ03Vab+9IzwjOGDf5vOhXXdheYveOzUKlPH7BLVffJEhSMw9SHw'
    'mCBYrRsTqvucavZv1sx4EVelnFGOgCP17tOlZ8lL/PqWLHZ/XPxxfuHpElzhuhbLcPrav1ldi83mBY9Gfwh9OCXuz6HD3UqFY3QO'
    'yOguXocy6zxl/lyaGfYqQp9r6WQ1KfN6MEoZpUwl/5spk2dZ9vTJYhcxVT6UJh7UGB4M7j5uk7h2dfq6zvd1/c/cV3RZvmZnX42m'
    'h4MsHFmd/p27++zWQ/sE9I3r9XY90tv1P3Nv1eBGuuva4eFiGJ6FqfeyHYM8hKcT/+bDbo0QgviIBf9sxaF6wC2NRROEEH4Y4u0h'
    '9za9CpSnbvRPwZNQ4hR54xELkdbkW4/4zmPwwCNzEkA9avnTAHlNmgbtatS9jVRi+5f5wY6WJDe9Qarc10hyrSYz+GPlj7Qkq1CL'
    '6+ogtUznd8PaJJYxzV3XaKd1C+0k/uZPnd2ys2KuKrp5oVputqMOttIa+hwiVvX8ranJbAZLJJjhtfUKXlvneW39//DajXjN27a7'
    'rbHMGOUPnvvEJhzjHvypme5ZOc89Y1numc9xd8hk3IIbHXSxoRfkcUe5jnzwibdwHZJFj1gMffyNvJPxZ6GdmCbolHl96gXbE10O'
    '0HkWp3L3elRer6TyeozK6/+JVPaoF6VyBS9fi8rRgyFDTN+o4GT8Wags9ldoNll62v0xTmppOqDktjaEJNxb04ILS9dn/5sIosXr'
    'Dd565eCtxwZv/T9s8OoO3ELdgevWnHmP737w+I3DH7pvqFDRBvlpPinXz0Bhat1QP5PgZ2H9nsXfpVrafI0jlWJ6+EdtE+xm97lU'
    '7rBtfdnT0+egk/vcgxSJQjka/ZJRDJtUM4TxBB0ZwHxPLZHfefyhG4//JGa93paiinXvbp9xPa6d+f8A1z7jmPbPtHVZ6D4VLAXH'
    'jJwlDT1mNSZwwDijvmYie9K73+3EtjJ/vp0MHKEBMfEo7c+2nYntVf58W5VrkfGP3q/ENiN/vr2IjdPeduKwfx++vOHGpWQrdBvF'
    'lt1y/Pl2HNVDFJHEdqtyDYH8H7Rl8c6cNjc3nz5ZvMm5050e1TggS+6S1DnucVkTD4DZ/g3yyWSQbQ77eTr8o9TZSqLz77iZI8Zz'
    'G+ivtDfuaXIZX5RPeMaDgKbXmfCqaTIY7JyV58IGQF2JxBz70/Q7RFAd5cYxdBGQh9P/OYz37G4Yzz3pDhnvWU3G4zwcnIzrjqwa'
    'j7vkPc4vwcm4Sxwr2Y97/w3fKiKPv51dei+wqReP4qGuSt5bY2OUmZP+4mQ0HfTL3im8r65Klt14VtG11E615FlvDNZhu4TPZ9FH'
    'wlq0w4mX6TVMSvrVmNe9X9ggYOW3P+mbbapc+AiW7YfztooOZsa/dDQfp8Pzeg+l0iqOg0ajVetZtoK+WXZrPcBc0+UBFKPpuAcS'
    'J46qHRwHoVoMZK+Gu4QkT47FH9vjK8/4vHDF3OBmnzRj3k4jcWfZN15gmv+ai0rD0odqkAq2bDMmEEqj07EICHklY/E5hiUleO55'
    'AYr4O9BtpiqiVjM2B7mmXSIgj/LBgApI+JZh4em7mLFYxLUeYSIFbdRAvqgTsdFjA3od3gu8W8LT3ONIWgLVwMGJAlDdVOzdmftc'
    'xGQnN4YLu8KYmtZzTVcvQ8dvl9IA8CIL3aYqY+PD1kLsGuE5r8qf0lrgIghCDBv1gFBPRaJYmzTnWxVhmGXEWeghAsDIf+FrPioW'
    'bBi+Sjq/Q9VrPENy+7e4SgAdjkaDLB2ykNTjA/BeWa1liy6pavEOk4OIjvyqtH2Nh0NxgVvl1hLmxe7wmc5V+1yn/1onE9SD9mZZ'
    'P+kZaFtAM0VF7zwuXykVe+zAmmdiKmPMKNuGPgWpHc2bhoZhH6xTFy6W672A58TrIQFimAcs+NfuWHdbeGRY7uUaD6U5Sfz7sAFu'
    'sPlQfIkRAkoZpVn5yz6MCgtD13lDU6MzxGmr9Y993TmR9AN0dr/mgzXsA/JAsK13v6y92Xp1sL62s7m0ePAB9kJze/+YmZuf/XFt'
    '9n+ns/+aPdifO44E2+3BRIaw5BRt+dC3+LdTnIm9ZbOx2mjtze+vMAXkq97m2e8AmXbS8JVCqEbfIWOepVfHbqTkD8kid1hmEIFn'
    'wFcbJeqIKFP60ob/8sJ0mLsR3jBBNCb/ChG1NTyCiP2X7lTthWEFFVubh02411FkmbS/MxVse5xiGEg3si6dbTTI77XeQqFx+xQm'
    'ZCXLg5dPaHxBiAP4RK9iJnrn08eLi9xjY/ed3vBvSDnQlx4v/MjFbsSAl5Los6vJ45YoC494SQmBcQS7j39sQ5xg8c+zH1thOMfe'
    'aCiW1mkQQpc+4GAeIOOiR393RPzw3x4j9GKhKnmA4RtZzohBuEZ+PG7TuzvFmbJp04U8qwLGwn0tN+rkrO7aTBjo0nlEpIQvb0OF'
    'q3txavhBsv1BYeKvuqhAyGR8kjeMUkuQ4yNqsvFCn0NE3opGu7UavReLsypUHLhRt/Bjtx0tA5FfoUz3mVOkDv44yJUDeMsOYATb'
    'bnexXd5L243v0tVIaFu3s4u37yxcdOwuzrcrKFKnt9+DLDF1z1i1pD6Hu6yzkRflrFS7QgKVhxIlCgIXHxEtMDWWZqvTMMuzASTH'
    'Cso6y7Pco5VZXQyEqsCPpDuMsoOaTDs5ydvJYLTyfTpbU9b0lKYZ1VNOoMFe4p7WwhsamPwDOGqtxGk8GLVKck/y2xE7eF2MewVM'
    'visxGZFXJTzdvOQNNPuEWDEWI9YvJmUPj11LWdSK0cg85i6ga4VcKMDoEydaNbbdYOxE+T0LAfY+orjznsQ13sPLiy11L7I5Ovzc'
    'RjNWl6GnyDQ3KMUuGYthmESRfl8uxaDFis+O0EUEeae9iSBLPKszTE+zyny0DkNb+BntBX1LUMCJ4A9bHfGXi2DNhILFuOyqgaY/'
    'jdPB2Ul6KOP9zi90Hy8+WXr67Mf0sNfPjryA0BMFDGSqZEQ3mirHPQtLkScX84UlePsXYyEFz9d6D85KIJ+DrTPGuc0xitJn4B7d'
    'Fxn51Xx9rr2JBoCGqC398I74JS/lqm/72rNIgyQABChPJzlYZ37HDThSTAx44aQUJ+lp8WBBf56kxYfsn9N8nPV3bA65Q415KsuM'
    'Hcy8sKbZKpM2EqYF6zxamAQbNzktdi5PD0eDoktYhViVZK40CptzCzTJyXwVEfU4m2yfD9+PR2fZeHKpQHq1GOZ2Xge7irXeySfZ'
    'OIVZKW3EmMiBo08j0UkCc0iPinECvjwF08ij5L8ODt5//LB5cJA8mlMNNhtCPhN1QZXfRjCyx03xbfLpmQKAjVjQqzqtaElfa1LR'
    'jvHwBlqUJN0bYUmF7f4dN7J9+PmW7Sh6/YLGy0Xjbyig7YlkFPyYa6xQWggcCFGd8HKwilVUv75kl4V3ygYymuSinNXrVmBEul5r'
    'Ltu/E5K+pHGm8M1xUSQuDEPyUxAboGwKdWiDC3hYLBL35qX/OXJZfXrcD/jpTGGwVWyK1U1MXCFkJW/hOg3w74rgr7KiN87PjGRg'
    'RQ1Qqk8KJnTTM/dICABoIvk9BHolJAIpW4GC7d49ZtcCXbFYdKQNWtEb5okYBZKdGcphGXxjmzuV8F5X9J8XC8TilbOikYXjiq5X'
    'sdUqulaVrlTuOsWvUnaNUu3qRQnfznQXRbKWeSvZrpJku+mxi5Z9JtJZ7uCQ8b5aYia2bpRUlFBZIdlhbTJiCbbp5/uEcwrECOgU'
    'MoQM2k6iLVvCZl6y/HI6GcC1ncU9Nd9PmxV2UebFeyfzSccssIRrhXbHpOAPryMWju7DQaYOs7wOmHQfe8yIoY6ZBm8DIwkgW4z1'
    '56b4E6JsQGh88diSwfeDTvfxxYwYvphp8DWwkwCyxXesPu2RqoOwgWEQzo44dGVqgGx2FEU1O7KIZkchmtkRQRI/RFI2hoeBGDQl'
    'BCPfLoeT9IITcCYjkHCYExVxmGtlnAGThNCJJq6/ZUaItoVzRfYWDN67KtnHGtJjOEOejbOoACQ+VIvtRH6ZY1QHU13fbIrGOYPm'
    'R5nqYymSY0iKLIOjgpl4EC2GU/z4+GErxE/V1eilh5wUWztkBZhIjqEnsgx6CmbiQbTopYcm9Iop69bV6B0NRhJ/D8HXOt1HETNi'
    'SGKmQdPATgLIFtUj9YnIkho+DI3wKTub3vJT6W18Hr0lk+iUmUFv6fQ5xQ/5OpEu69Y16OVDDj2ZGqCXD6Po5UOLXj4M0QPfPoMe'
    'fujHk1z05LdG72x0zqD3Xqb66InkGHoiy6CnYCYeRIveGX7ou7sOeurbiHRw4+SEuk4PxDpkRAU7ZFrRrmEkAWQi3tUnIktq+DDM'
    'Ip+DJY1b5U1GsMxjTnSdx1y70BswSQidLPX6W7o/deSnUPGJ9VKkdJtpoKGmqPCnnA5qGzerWX7MsfeOSg5WMpEeXcdEnl3FFIDE'
    'h+rq6Q90N30rikdatebJ+vYVJfHdbUoDqGt6knBNlqCb/Bn6+ehXdTB7hd/9qLrP0fVqdsE+Hexp+KrPmrbH2+9fMbT9SSX7tIX0'
    'GG0hz9BWw018qJa2x/KrYr/pYK+hGuxHZ9zE/UklB9iL9Cj2Is9irwAkPlSPM1QXIowhibViWsPidlwn40syxpjZ3NtvJ43gKaGk'
    'l+IzzM7uWDdOT9klT8h/jyW6D+xIeJ2z255X2VE+zDTt2e1PWCTcBrll4tshtxzZFoWNJGVYeIPR9zMVZ3npIJ+sPQHHpe8hFBkh'
    't1jz9ysxVmmjnfwufe3EjEuuqgYtQJKxCF2prV/QW6+2txkMqXd1z7c0MGP7s5Ppj6rNjY2nLdEK7Q/BGNrS7uiNxvmxMsKvJoxR'
    'XqyA2L0+mhplDmNKAYNI1JhyQtumFpV36ST/mvn9dAxzBL87MvffHo7Fqdk4Go0aypwdPzioAhg7JjhMxzcE7jMEjIg5gHL41+UZ'
    'zbliyzsQc/jg2HmKjt+ARwoye3KmZMk2nSltOD3ebFKNnZ0B0Xw1MCqfmwoqq+NVRW1CLwyVyGpyS4lZTe1oOZ/YbMEYrdnChtTR'
    'NpNKzLyFQpaJr9uezVLWjAF+YPWXKvpHe6DJn5+eDTJwyE6Bhgzdt4ICPsHdEjFKu6UMicP2k3jrLlE3P3zY/nDwdnNnZ+0ncMZu'
    'vFaIkSOTw1zscuCIJOsnsDkY9kanZwIW2P8bFhTaqO3yHR7h2aIYE9rfIqOBQbSurDvmeE9jtE/a6o2GYpmeeNdVZZrYt7STQyvp'
    '0K4yHjseQJxzQGq8f/B9V+dSjagvrxykxCHk6l7cSeDQAPvMAvsMLgGqDLrZE78ATwiL4o7gxa3VIO9d+o++Qs/H4zf5F3MN+BpE'
    '0G44nwlBJDCPLO1Yj5A8sgpDpJLOfB7lQ9oZ6EUbU+nWC7uNDGad79lhHI9LBhK971fVeLrnX9KtmgII3fdFVYlX5amWceFXHc39'
    'SWi9osT0ak5OUm+01OXNVecyBVn0VT7j+gDTTb10ri5fYyk9t2ivuFsorkiYUQ2xD9SLHNDJkPma+lZK0Sax1dAJz1pGVAJcdxrT'
    'EQ/uSp7glRfjF3UojTO+2844K6YDcj2bed4dL8d7/tpSTgDCAleDduQdd+qX0JQNtnCrr3+7bkD26WaRGfO4rri1ZRyA+E4Br7Tv'
    'XadDLfYyDhL1jb7rATK5Od8O7iUDUP8tA1N7TTJAuWAl7YiEmRlKMgNFitfGA7gDGbjVHSpDm14KhGqLLCQ2cQ2txurp1AQIKFKa'
    'Brgo1m6Ar32j9btxmEIIep4Al1jCrSRXjVZTlnDdaCRx7BPK3kn+5umZuyhhQtfh7ys75JhroVlGNkkrLqWcsuhNDBCarTKQoaHB'
    'Oo3Zmelq9aFGYY4AVM/Wc9b2+trLDg4ESH70XICUsccDHuAk1qqr37gdIQf2vsKlzhdcQDFlCPxJXcDuMYSHq0+7jXQwKKGdzo7R'
    'DvKraAdlAtppwEmsVXLQ4qYyhOilnprst+L3eg1mWkm3TX6s31igquNYKOi5gZ1EWw77rpOZzqcWXqwlcvAMu7dY7z942ZFtb2nf'
    'aRl6OO0ATmKtOsfVNLX2JpbuZ0PK+IiYs87eZJoOYnRZc3ODs0+bHT0DtUXsWagLNYm06MqQQykMWAlGtqepqslzLSnYk3OKndWk'
    'mDcaLD+oA1wHc7eiEFWAv3Rxw6bbClXXf9ijjB4kqAA9xYyfs8FZxvrZbESK+cPGlYuNH1fWDGQMr6QKqxsNrVGO48YH6dFw/VF2'
    'x47jblm4x/fF7n5V/npa5D3UBF17KFHjwIed+EhDjnav5O2adpfwgIZuoueFGvN+GF9PjRjtKapW7USxIyLLaSGxQTbHSNmEO0WS'
    'qcEhUjaJniFlNraSgpl4EF220YgRfYLnbFsFjnO6JWdOeMTlWMbR2LTW62VFoY/T6MGGXwJhG3fR35ODA1yuDg5eLuuR9gLvJFfE'
    'hXRvv2Nq4PbGK6zGhzkdkcG3CENJr9CGNN/glvR+swH33BrgP53hkSmEHeqrgmLDefD+w/bu9sHaxobYdjK8x560aNdZ0fP79wNy'
    'iDVJ0lz/0Fso3z6lt1KEel+yS3UZx/r2mvKEaA1DssY9ss9yrZXUlVGePtazRarTVuQ97KaNhgOfHcxxd/8vLWc293Sh/VZiOCBo'
    '26/fDIkhNN3ReNJ82JkTlR+2SPfNFBMZr0AzGMsIdswpg9ewiqS6qq4pvVRRL5Y1KRQcT5ZAR8hxhTtjiVDAhnjJYLIY8YB5JTIC'
    '86mgMMASrhVXZKhFmWRWnGu4Z2z5MB2EdSNmeiJ19MDoijHxA8LRMJxtxcX5pTPimNZtbgdOIl41UUILj+WwL1UwpRc/vdLjShc7'
    'KbZrrWBkAdPtLSfD0SRJ8WoHwIytYD7uTsc8StcklVvLARgcQ1CGIyfEo/MhfzqsMpiTYZFTcioscumJsAKThNDDNbFqp4jiT8DZ'
    'xsrBQYHMcY/J62lpJxohq+sqVVfCbPlnlqpXRGhsDeGQQihPvOBwshnhYfJLBIgpQ4WIAziJterS2uzCHtz6fAxrVui21lOe1tGO'
    '4iUeVtJHnVSy3trxWspTnNZyHKhLamaO8HtA3JfjlbQD9S3Vfe3dG6+C3sS2RnpYlOiD6NtLzsXAsbWkuPKzDU7YIsXfuh2GcN0l'
    'hfMhLXw2Oi8pjF6gZNUDA2NJceWRSQ62wO2uZLDQR5CQXQsDInmc1Q+4dCB2guTuNDl2yC7OxkJbFD+1ozzvQqSVGGN/ftiYFhkG'
    'JRLrxYrObz7E8OYuTLQ60xvYK41Ws9Td6Mo/IKvyV/P2DqGzUnRe+65f5DQXVkw6EZizGnZf2ArO93Z9ULI/L9l74C7hjUkeZXqW'
    'Me+lU9gBVWUtRMAJGeG2QrRUcOYjB1kNCUAMoNkXOvCh/CSAXoGdf2YId7tBRWcKR++bUf8uT+GTyoYtajXbYK346f32NZTJB0pV'
    'dWpVq693bRgbZlm/2JS3lX6nbCZa7utgH0HAWxXc0povYVtqqfWSrqlSnVNKmwVBcNh6t/th693O1sYOIKFG02wGpfKm95WNH9aO'
    'j8cZBFfCkf2hYTfkTkaAoo+UW5zAB+wALP7w0mXADdqoTa1u0Zb1wG6pS+9m0KEFyqqw7SbktQTd29/zLs7vN1swAUjTpLHicth7'
    'PR6dCmnaYxstqaY4CEoZrvHK/JQNJcxahepAZJHkCgs1LO8VdGRkSvWoyHIW1Hp+LDRFAkkmVAKSxXw4S4uGoRxwKr0mVFXaAQ5z'
    'iYVOMuqAJ8UJfBnoFQCrnzbvVTpJf8mzc9KqTqpsTxd0oOGgwl+b2s/ApCX0QMgyH0z+xuj0bDTM5ICFqbYGxh3VEM0Hk+9ADFNt'
    'DSOAHngiBDR1rExYdG4uyYqBIPVsPy/gtves+MjEZnkWSlmYeiMg4eovCxsfyVhY8oedJlcOAi3sQX7cZSGr5HqQVWEPcsiqNLke'
    '5IBNX4MJIf8XHht/yI5zoRY6LTDZ1S0xlUiLRGgZFdZm1xVuW3odJNhuRZdXH0VT0gEYcoVNrAMy4Ah8WYqBWZcbbFELMy9eQ+xU'
    'nPL6N819l76TWeIHweTGC2TVUhldK/+6s/2OdBs+ZYe1seylTItUf5uekdriq5JaooxTne1zCTzQwShJ6upkTX9DA3sQ0YAgDkcw'
    'iuPkBHCCvzZV3oODdPnL5kidGCeO/OlnRe8/YR3YHtgaZ+m4kC8GQab98kqolVz/trmikdO8oDRVKZXjpMo5oC4uXUAXl3XAXJB5'
    'YY052Fn7SYo4lhtZzElyig4UrT3Hgyq0VDkK6njzAnlZ/rI5OxltYCerBr6TTZzqZSzOwbtTFt8BM30Fi++cpGO1DwpU/yCvuvt+'
    'DdIQOnUDdPnLz7m5AGw0rrNDkEV94C/1dZ1oLWMbRLYk37aQa7mAcm4KKWk2n1jKfLklbHMMCLvRJCNWsoH1h8oW9WBuDNJTih0F'
    'TfPqtUBruA2FizlJrQU8WM7ls/Yc2LoLOilLwCpjLQ6F/rDZv2bpF3cxVCmVralyLighnzxQGCSkBihRzgXlyi+VUguUI8cihzRI'
    'Djw3KSuJ5hwsir+CFdG1PmJBN4lbQ4ntiKy2P73fdtduCFAB+WA893LQRA550lbu5Z6mF5CHz1N6OTkqvGAD93LORrhfBIO3l4Nm'
    'bciT9m0vF2zYkIm27GCB43prDWvOlYGjxOqCMQspWJo6GWv8DLyTsZg+3OX0TXLinhAb157aOFom+KEB3toWXtQ9Y6QMdebETKZ0'
    'mxB31L3w4LxdCH03kUoDcw739iFr7G82UqhJvMNF1St6RduEsCatMTuia7So23pUr7GYgenGfbxRuz8EQemO4ExFj1YJmu4lmqNh'
    '8M4OYn405Hzar6oxZLQIH9PjrAzVAEUoTlUPHmE6PQjurfjFHzJfoBPmzd0V98ifpBHj9ZvNn9Y2/n6w9mZrbWeznlHZ6mSOhrXX'
    'IDlwQcLg3tj3anP1atQ4yOBUOiuitcSHKhIBcDQab6a9kzIAqkgEAETKLKsN+ZGqSP/SyrKEU52KH59qNC9OvcDWrGoGU6omCA6L'
    'ClgxwMpa6kFUqdFa2izqVdPJZfWysE4cu02zyNgKmBavoU2Qfi2dHq1JbYFeZZpVXl9Z/Lj6Kiten2exStbwGKs+T8XY6YacZIx8'
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
    'iFoo2pc90Q7gVMMf48u+/LKk/4gvqQQj2z0qT0+HqlkFhHMmxpcNTylUKVdG0o757DUVo9Bn+yM17+u+tioWdcfXA+NLg7p0LtkZ'
    'ToXtfDxer8SSG2vNZC/+1VFawB/VZrnQKDsgpJuk+peSAmxaw0E3zwfd7DTnWiXHUGvelMyI9cHBAlRughlzKcU0dsSmmwhbvNto'
    'ZDu7cgxyqb8dw1/S8weLMItiVJ9CGEb7ZKtjuFQDvQ5a9Eo05X3N+w3MlMhiDdMU6wUnKbJ3ptcmHjoz7oMCTZuFhTst+7vJeX8H'
    'bDGuinPE7EDptNEofljrzU5UDQouwkPss2NYSdCuMJpzttPcn15EoA31eOdMTrQ6zwE8L7Kd7Vi7wj5o1Qgol49vRXjNkwjHeRZP'
    'Y852oYiuPrw2R4O968ywZRPCr+89XYcsog75bLdL2jEQLz1YqpbqBX/A3Eler9Lh0MLMbDMoin+t0cvuN7I1qle9L3m84IGHROeK'
    'amcaouRltZmXyTfJX8vt8teXJMPyZA1j9cuR2SQrMp8omQ/ga48omU/yPCs9omR/kI/yNCRK0mxC8u8gVQlWPlHSeDYf+UTJajSd'
    'TEYeUXJMTs5o5BElh1VRDUYeUXJUnqRhUbI/6mZZLhjOMChKGs/2U68oWWUjtS6WKJkP81SR3hIlTSpYomRWZnk68kiTpM9hlnqk'
    'yWJc9kdlQJqELKBhvwsTbJAmxZYUrlDnqLI9qU4hm1FDa1KMtFtjU256WwiP9tujdJaeBEVHZyc3dSVkxg8OEi2QPyAutu9JyIl2'
    'V33C1kZ+MdHtSKwFPykNHUsR0RYWGEPBy5DoffY7kV3c5B9a7hNDbvPsvMbx5c3jExKbTQLGNiO60MnOuVdkn6hBT/DktuQSQtuH'
    'toMRchoKdaLPlFZmbzsqJat9aLs5hZB2yIt4yKXc2C1noctkH7AasRFSkGwsJP3cd9eZ4g/h+8l3i32VPKnuqqQm8td81Ul+fVGH'
    'jKs3JuMKmM2qrMh94g4REKt84rOclfmwP/SIO3maV4OQuAOeGiiOk+cpr+bmF3fMZ/OhT9yZjKajWeoRd0ZlaRh/DHGnSIdQ/g0X'
    'd07Ho5OwuENEl6xfxIk7xrMBcSfPJvnIZzkjX/VHHnHHpIJtOZtkg9xnPMvSbJSPfOJOeppORgFxh56YQTdP00ZxR9uWKvrL1OvY'
    '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'
    'QnQFixXJ13MPcB84BG/PKTiLaVFlHK5Fe+2qr7lgfNgFXtu+mSQvk2E4qvEUO9NzG25B6gRzGpjFMagmKpiG6kbncw0WdIJtCqM2'
    'KBW9zp5KM98GCe0ivMq8swQJKtJcJCrp1eScI6h6lnLcyfso/dSt7ySp0vESlKVrpQ73ltvSl1Y1KHlMKAUfPjU4a0SnwdgaWMd7'
    'OOqdJ6lLuhHjDCiYeFc2AwFktAJS99NPpZV8wkxbdFNFmLKbRbsxRsHXVqf2+eoWJtqukbcHjNNgD+RdpNm1axD+zsP3MRoC+dkw'
    'AcETlpfOMXwxCdEY0cULi/aytQhpt5/z5X+B4swisVV7Ay2VkL6q63bSO+zg6UtcgHM5m7czZjQBMvrTEMrZlFKxNIqKO+jNfAKi'
    'N/rWT+DUIJWZQUERyYUEWUbC/UXprRSdTW9VoTy9hfea3ubLlNJbVcGit/l6OXq78/yZd7CLe9EpPYvoqjLlRFd9zRFd008l7VU1'
    'b0N7pU4wp4FZtFc1UUF7qxudT3st6ISxJopAqi7CtzteBbnQQKmK/T4w3+jBK5y5veE046by0BMnDjPrEbWgvOBcGS0/ucGaCZnS'
    'EGUTlJLzmoJQM/eXGctRj0oHVrjmS75GW2Qf6MKzd4Iplt8LfFNYXqZ0L3AFaycU6+X2wt7zo+bKzu+Pmt7+wfbW0d7Bc6/hPdv6'
    'Q672rL1hSpUqUszn2yC5rhUE8xqZheimmQpUn9XwfGTPQVmO1xYMd2xScpsjEJ1gChBbR+Cs822HWQg8CRY45tSWgTMO9dZZ0YPG'
    'Ysk/7rnmrVqxeT7EHkG2Mt5RiYVWDnY19JFjLkrK3ePj1mrd/71/Uj9+VPf36Md63f8a/96HF/SjBT98zg2Plz6pNiGidISis3hf'
    'z05wwqHdQJkDjDAXITo8QJ3lDS/reCOvAW+YNZIhp7nr8UOH4H07HY5F/IXORDLDf6DCfnQW9q5g0ePhHacFEwS4DzUnxUt2yTf6'
    'jL7m88DCav3YjCkcONlxccy63Jv2Tn5rxTSm/7Y/uZZ2bt7OtLXJug0Yl/Lty5+/3I01Cf4ijQ2zs0JTb6WpH/78jwIa5Tm6+eHP'
    '/3VzIQizabcI3x4cUxxIGkSWdHKRpO9AlOCkMazZ4SMP0Pxd5l3EgwHeFo3RdHkETQyuxPa831xoYLLUaFxVNVeLtBNRGHlJYruQ'
    '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'
    'aqpoHmeC6b7FeL7kLJWD52J4XKR4EcCuj/sAxIsw5Op93d+YCNqeF52bcqcCkDMhVrbQRZP6JYHiNEfe8g0Lb0pNC4Ege0ivhbW/'
    '7vUHeScXsLgr2jchlUlqLAwJYREThJjKFLGKPgnBC2WygWkBrO8a/z1BPNaMNweizjhos2ih4K49mvxc0tNkg9Rwor9SvoFfC1GS'
    'w2osxV6A1r29l/41CkPfbf7wbm1jJfl9svO3jc2tnbWdZGV5bXdz+6sUh8LZ5usUOTTtznB03WJ5ODJi1N3D1tb9HUEF97h+DNZ4'
    'yBUUYJpSmdydCPs/DBL4z3WF3IX64QQh5URkWttQ4la+lZCBvTjaGOF4RsbRRkzAijXgYYQh7Q3cLA/T05EflDHnVv0inkVQ9w6I'
    'RJs08bXGijfdbg1qMV8Un3sNKcDSBU9QeH1X2+qUUNv5dQ1qqbZNgWLjo+FdjWMAptEF+SCYw8ZHQH6NhqpxW8C1jg8+qMu+Rz6c'
    '+CtQ11/TVye8q4XidlJ177O8ghto3f+WKuMCKqJ3iI+Mfiv65b7XMzS7Dq+EZUSa7qGyxdp3JHgTUwME1D49An4FtD8mNxdKOz6E'
    'aYl/QWbDxF1PknuC9YJABAMBa8iZplvJfeHXtKIasdvYujecFloZ3/Ea07BkhHqoq3d1subZBI0mXTyuorqsrk4m1KDm1d6w1upJ'
    '8Xlz1QcClvaaZyZCc4n419zPp5oFa0xlS3h1EpjJcHsL/NcaFHtu8imrIm61v0YSbfft9srK9OLSbrKzu/1+aff99kqy+deV7XeL'
    'f/vKiDTifKQYaBJZl8MsQ/EuPFzPMHp6H6OyUzz16ptu+jFLdnrXbbKyMTyXWovWi2THs3CUB4Nk9h9//x/PXkBa9dmL39Vc9rPF'
    'FmY/ewH5LyC/+nzmdzXSxrnotAf9Tg9NYZP/+uKFqvKGqrzAKi9NFZf9nDt8idmzszPSIZ8KVDzY2t5E3e61zQ3Wq8thhDONZy/q'
    'Sf4sxZ/PZ/Dnsf35HH/NvvApU34kaaGrOvRojTjpkTTqkbi8z1UdwWlrUHDWoosgfAj5NQ3RAU1OtOEokxJ7xndBI7FLyncDU2xT'
    'saNK5qJ4zZHZ/Lb6b6Y1h42HKTGRS7cm7U9TGfUIoG+vLXph49ok/W47GXQGOamaY6iVCNkLTRLDfBoKKsKXmclZV3s+lqscjxm8'
    '4DsXsLiPlBjF6NM9zEsvhYZF3zIf5EogI1DTnO9B+UaXnJpPqt2I4tV97hB2QOE7LaamcXK59sM5W+ffFKagqrpvJs9mZtyqCGuW'
    'kRDppqJJDYlf4SfRwYN+3kG4lEkDHURLKTMm0RYX1wIWu7qLw6EvoTJL5OmmUQssNuM6VrdUt+0R+tgGCwlQImHqTyWzuhRdniu5'
    'dVHKy1HVlZtu04yjhG/VfplO7axVO7Z1XlQ+ybKu5xkcCVgcGPyQjFnhpHbOehR28Bppwjz51EkVdrcbCoWRLbOIRUL/S5at3UB9'
    'SmOvhrcIvJ34h3MzajeZSaokz87wSOZ0D2Qd4poS/95KUpL+EM3y+YZSV5LssxqZ2WeS1qF7I1H6HECb6cnI14WkEjldC6hincyI'
    'djX/OJYfz+UvjR1+JuOoluZDjmpUyimmZxFF0sN60omo4TgNJ1aaPliIKXYmbqakfocOrYIUdh9jQdS3EjEevIpauFDNA+rBbOI3'
    'Dot6wAqgJoHGdQCAjFcw2mpbN1i2kWdIQqsqsCEH8YLHQcHjkoLPE7/g87DcYZ4h8OwIHFYHgKVgHPjPMfzzvK6QmdLuWGy3ReYr'
    'l4JBRBcG7c08ZE9Ntal5jTubxYX3hZ+Dk5F2m/zHP9aTqm2rqUfODoIC2emgM7ifJi26KB/4qrTeXadLeT6YcYDwYPidLcF3p+97'
    'fOBpmnh0Srg7AVXXyGG3Cmm4e8XE40hiuLvRzQV0iUJjRKwJu01TN/Y/Xwv+AfdWBNbybhF3dGJ3Wt6txWBL3dLsI80HNmwqelnN'
    'ssHmzP8OAOfIjpzc3FvSQghTuGbdWvDZiq2FuY5j5853yMF+a+4gTrmQilNL3zWp7M9ahigTV7QleoZxnsM7d3SJBBc5k1FewwFR'
    'DToBh+Bo0ECvWzzfMUz4vz69cXNGPyv66fAgDGuYXBv94UXa7eRZwZsk3DRTdFNM0TUwhTje3EaQ1zTuFamM/jrWX8/dxyMF8WRI'
    'Gw5QOc/qtMlN0x5BI9p04V+y66Ifx/LjeUXV6R6Tp0uqA7+npRr+NDXp97H77dfvwQngFsQOzFqAWdsvMfuywTkFLgjmcFru7hn4'
    'd4+QpLiuDKpzYeCOMoCBpQCyQ/kydR7INWjSHwZMl3fVaaMlD/QrOWNNRR9P6BUX03Ur+6YfGkwFDwy9rDE7eXpCT77QhQwE/Q1D'
    'TWFuAV7ArADYn97wDkC346QKoE79jQe1IzNuniNMJ4ih8VWxxHYW/7rSfLe5uJy83dz8y06yurmtzTqdMPPrY5BtoYWx0vxB1ru4'
    'iHP2laj757HLTfjo/rBztuPqzquG5h7lOsP3aVDNO10GQRKXWtS4QtZgfl9JJ0f9JBgXvaqQa5Uew9joNYl9fKFcALor9JN24dpu'
    'X5tOWNtKSSqcwWUwdZkQno85ta6oMMkPPXpW4qM0uzjuov/XXsmik5vYTtZt59jMB6jfZzXM42vABtAoEmy23RNW3YQb9wQoFasg'
    'hquituiHjDTDRItL3EOcucQ5XIyL9Bo9SyXZZ4ozDW9WeEsnadLunJ5mxLQASmPYB0yLA1uDxmGp6sl5vw8P7x5KbIjkgQU2ul2s'
    'Is5KHLCi3X7a1qNaKpSfL7Yx9+gkUszCkdMeizfJBQKFEq3JSAxL+GnV3MxLWyueOTaAp3zWBop3lGkNtBqtJDkUeWQUEwvabq6r'
    'wIaRwfMBICxKKSa15go0Dk0nO710kJ/3iZTqwjN1a9jHif0VGRx2YnV0LK28flnVGzkgv17QTBOPSppjsrhiaWHbhoeL3NDok0A6'
    'hnCAP2XDYaftnZVP6bBDto5yCq9JQADnLtNH0RzRnCt1el2ydL2CavB0SpPBMJumXhHwH1UtJGrOOSOHnQAfJslDMSLtxVqPUAcB'
    '7e/tjvCRw7mhJib8gFw40TlrB5i6H7JKt4sYpINR3RL0l9gfwjJ0FS7xNTmh3RyV/MjbG6AUBaE8K1twPqjJABm0po7qp7RbT8Rg'
    'dlhPSNHFaV8jqEAJBBX408BQ3biVr5Kdv2yvbdHb9s8r8Mb968r2DjxwTTlWV5cPUs3QCt2wAruIOuE/RKsOWAQdI5Lr8PICXTRM'
    'DeI19bHRuPqrvxaB+qunH/3AA23Wolw/AwcVnpcSHQ1+JF4DVUiVAAug8AKJwnfWsgLZ2+Jn5JDcQPmq6951Z+cb3Ut5eM49st36'
    'bbBDFjkb7sKkSoHzkggc+SNQTkUwAFPVhGD6qsjSD2tONJu831pe3F1J1jZ2N5OVH9d2dtc2fmBy9esjSoWBLhK15Oo866HXMc2n'
    'YqFdrukJ0WSAMvgyYjb5PDl76p9K+SATWfcGP1WShWihlgSPwUNZ1g3jnGgXSXBBJKVjrU4WcZqXV7A2Rnokhup6PTZ7yLlaxdxF'
    'YvL0XcLcI/WhR9m1QqVIG5w79yg+SO9yDvWAkBZExUMlgUkcAU5bLHXozjbGm03C6d5zI2x4vtAXPD2Khdw9BN//UbWefystrPJ2'
    '4A4g3+y/XUP3nx3da3wcd96x4OwSHbp20Bcl3XYms9HOjHJscErNKfLKRLQAhHXd3UL90Imqfl2jQ+ooaqlWM/VLwyopNtMQ+bAT'
    'GZ/ooXdayuneJKlm2igxvxhPhDPYzY9oe/2rAdY2dP99jZ5LPmdzvkQUEABawlAEF6SksUwC5AraYNrDj4m5Dy5insXVKQDcllQO'
    'oaO0pMJQXxeVsLS5sVtZBmS6vgnkwuL73c31RZQBMWfrJO3lyrBTrFsZFJBsrFuJjyDhdift9s8ugfof9uEpRFwIePZ86gxHl0Cf'
    's+ICMiLT4XWdOENMQefJ2XkfPVmnw49AvDe+MqrEsvxLHUTaixMmrtmsnZyXnCLXZm32RNZIyL8O1gTimwzzgPhdgjcjVkXtnV5+'
    '2h9ecHNV+AkvlPRiAK/XN2+Wku203YHXX3Zy3uvAKw1tD/jtm9fqaB8LF/DFJZqHEdk0zMgnFLfVwScg+mu/yEZpm97++C7K66SM'
    'kF2kvVHnBP3HQinYRUu94/wWjBntAjyDzoBixy5XgTyieSwsSCE9e5vo5ouRmVi3klEnAvDyIUEva+GiBckOelA93Fr8YaWVvHhZ'
    't++5xe/I+6S1UJ5FiO4PmhJUF6APxpVLI4dvV9Z+eAuPxx9byez3rpHZZ/ACB6Jr2EH1iVHyx+/bgw5O9bKHPtTFiKP+yNOVO+xm'
    'Z+nJtYkr2Ru119Fi9ssjo07Q83K6WXh0iSOHmFHOFp06QtTi0+su56gXMNBprFwnxbW2/JYzzbIxaq/eoN+9ywuMLHVxD00v31Hr'
    'F0iHlUO0x11P0uqvx3qWEm8YVhHx0JDiFwAYn1PUZEJemPsp7XSRyVPHPewmxym7cVJibbyOcmZwWBsS1AiVqBrJy5nBZwSpOoqM'
    '4KdAFjobevkMEy5z5iKNKLgMJFzAvc7D4ObfXI6QX4TsU9LoohcL7p9hoCZV3BGYQ1cYUoRrk1/6GIwGjmw3r9mlxSNwSCeCQqqa'
    'o9LwDwmtEkrHBISNuH5mTkAervvLbkpY341J6uD8Ny4xBMEstYPYpooZHW6hk7xK9NZAytSUr3kmDm2o1F7nwFO0wTPPWVH/Z6ok'
    '2uZLSW2v71RTVmQbk/P+FZyG3nXyBAuw5lz+hBnlGdMzSf/k5HLQyfJgmG+L6+jwhO9HVkBMhlQSEbzBW4+CWmq+oDX3nuNglOgK'
    '2l6aXL3mu4RDImmb9xTDPKjdlZg1er+n5l2PyltLp43gyDCW+jf4QtCVVrrjUBR6AE0Fjd7OobFGsao3tqCupX5t1dd2AI6FZ2T9'
    'hJzoRMNB78Au9/C2+vmSnDaRIIh2HidvtCcsTNsOpgS8DV/11AtpQRAMbVj6h0gbUg9kEEYEQDqjNAKitppMeykWZpVhGIlS01AF'
    'IUMlI8a1eeSdAps3ymevk5mAg7naEc8bsDwnGbG04a0/BDwI94yasWhpQZZRK6k4LqA90j+jp5RkGpYCfr6m4/3z9LTvBYOEyXSS'
    'fz7wHWfQDGzvgfOMRHdu60c0b0f99/jOWYJ24cv4UGzu59/uVxvfLuzX4NfTZh2dzXlYwnrpQGjQSWPlj0Mv3Rq5tkiquFe1Mkix'
    'IVggEwV9E7R40NOgdstkqvjaPPa2rURKBhFleGixgqhZMoLZH1+O8O027KTT5512O0M/RxX01agHIr6+yIWHaaE2F1sLd9cD6uiG'
    'azA4Hj5g+lDan3mRoKj4pQ0wDRhXHNG5ZK0DOKwmipEp/aAlsAtHz8kq1C8sADH6qeseuQJJiMaBR2Z/MD1EHF7n3GdJv3eFpvO1'
    'YHmg2g5Vuf8amSr+QgVUVqT4g+ZuaxXUO8zKNoKl5UUy9eKgsvR2cRtdWiOKq8krHfEQbawnrDDn3scHjiZuP/BcJa6Wv26Oeq3E'
    'S/sLYPHRVPLEzuRJvOaDFlwvom2iNleChraz3FFmwr9GDie6RUv6pxT5EjfK+RLyibjwTg9YXdLLRn/kLi+UbNH1yN594NrPL49H'
    '3ezrPf8aBf5TD/+zLzj9zx54/J992fl/9qUI4JlergD6vM/ppKoeJN86ks13eTUuMbL6Jz+bJ745zdmYdqyL6bx/OTzxAobQO8Zo'
    'EBpCSMNtyPV4PE8CohoDoONyBO+YYk1xbs06JPcqS4UibvUmTMxo7d2xNqqmbe10mJ6xWfFEHsC/E+vh7gll0132lxwGhbHNFZcy'
    'Us1a9SwmHuluOf6oXABA86mTI1+CPcglb3BKiO0xmC2AMzLcTvrdywviTSEbDl59qLcNC9y9hqzh8BLjpML92hkSn3z6+HqaNDHS'
    'buesR8jmfuyWE9QEhyeNNWrLbBQcb85l7vLgtVJSzps/STIqNtjNZP7Nw1gZD3qtO9bB5qkcOtze4KzcOQkMlxi8zR5xiMQIO0IP'
    'UB1222+Jm3eHDHsAFqvwQu4qEz7zGIZKq6ghLvLp9LLd6auXlmiLYeou80t47k42a/XCXBn/2YZbHGQOUuz3PBshO7li9s7YOIz9'
    'uOijt5mEkynniyw0PM7IjIufyyxa28SME4SJsIciJV0MLpHHjpKwEgmglfFxmUI1f0GCXqukxrPa7aejKovbuMBuf1CzdmNlhd4Q'
    'R1DK6RXCSaj1obe8rGSB+3OSdbpVXXrKG2PN8IPgyp1pzLwI2EKoccMsIfEE3Eqe1ZHGEx/xrQT6SU84ZBz8tJtPXyRe6HDm82S8'
    'pyHoQG2XjB2tEqRDa1RiYbnnYH0N7W2qRNaaTfJYiUzwIhtmMkvRXbxWskKK8XYxO3rRJW16tjg2c5TJAeZ7PHT+6KxRMQzOO5P5'
    'HpUzuvhfOAuPq6nWWGn5O8Bnebh/Do1MnPMU08jjgPAMpgpTsJ1462QNQ+JL9Q7g5z/6SkUxlnsL3bke5uHX6TnX7ONoJ2rJ79Gq'
    '2hVvya0tFbVRD5moY70Plsm3ZE5slczYogeKcpiZ1xFmXkcz875gWePMPSUD9I/kr+DljaMHwHFNPdgPd7tsqY2qhF5ScXCLNcTL'
    'Lav0IrGnMKPlmtaJwbsulu5aG9fEnG6rqISiwyE1wrV/MFPxvizFezIUv4SdSPNjJ8iKl6jYGg/lFdyfT3AHj8AwCB7EHFDTUXyB'
    'L2LoPYCZ93BG3mQmnn3Aq+mE7DsNiHh8PNAOIfPhfLn78+Qm8ePcWYsy5b6IIafWJOTGCchq7lCj0aAKSgXrsTu/wcOBfNBEnoUW'
    'zUSFrjHBKicZ/EZ37GZPu/ZwojT1BEiqNEhDG6MieUxzjl+CnZz+ovK4ZV8taOXzlDxYoLZ4RAF9AV/I0KkLDi8vIyAITf9cXgYX'
    'jmPBz/YaqMBj9KLCr8V/pojZ6eJEJMvFl1JRTOu/zZRXhB45pujDo53e9ShKPUe/HTnA4glcPvj4F6lqI/lLlg2IWU76GVQTVgQS'
    'THOj/gBZv4Tk+r1sTsIqd1Pksm9kV+QE6jhDZRapaaqkCUVwpqqNQHzb6V/m8irsiCG3f+0jsXBQE+9mymw+B0Rylr2R8YvUNHiJ'
    'ojZiRYADQE4RDTC9ioUSTmLv+lju8R7lo6eRjDwlVQ4aYuyWV/WgazV1IlVTphr2EAyUxKfe6fPkp3L+pqYsrTOBFICCFqHEDjRx'
    '68pPr0U1xCryIu8hIXzNgmsFEyeCFo+zbv8q6YwaUM0Jdk8uLaio2shN8kghklI7ltQ5xWxITZiFUyyfKkjBE/cRQJPG70sWiqRg'
    'GCBBrkw+a4VnXyfwsYAFTDdUB+lT1LH3yWfMOvDcKYjAZPgpS4aoEIOoIkWz7xQPMrpxE/5X/1QCUlzJcud9lHN0L8+0eBeaYy24'
    'HMci+o9kbZKcQk2vKSdhd0uWxBcMbi/7pH9ed7O1Bi0koLmbtlZRMUwfkVerW1w9GFXr1bzmri3orFbkbdfxb0fiWwSnKDjicp49'
    'VQY1H/tSCM/jlBrxa/3y+fc9pGUzDsbutjs+drmygydETAdkIfqyM5jYweomwLE9z3DU07NhOjg3TGaoT4pkeIgaqMHSYf1StP1F'
    '4Wzas3cMtTbMUOncALTIcHErAL3U+VF/blnXfBfBUTklhMQGvnA0XHNw0/UwIrhYVbKQgVAQmpaaZDT5ZfNEOI0ZLFEbo+kYtazG'
    '5Ic22YrGNhBDo04gaidqQpkisYbjJYvsARUNxXjsyoFcznqkpC/lU+apicKJ3NsYB9FgGKOuKU3xroh+Dzyekfpuk+B9cWl3RUnf'
    'Yb/IKF0C8DR8+Et7SzLeZQM6USjUpzRQOtJZsWUC7P1Ml3n82NsIC8LF04xs7eIA9c7dceCDN3qdIpU6NkIoCr8v+hj/BmjkDpgr'
    'ZSbdPHoIQIaXyZ2cwthFc8d0XHT2t9agH6HN6h6zABe9EmV0u1adYjRaQsclu2QZ4lwOsM3ZGsZgFMOQ5QxpZoxsgxoLsJx58v3M'
    'zEUuqKqLdz6a4I+G/Y9IASfppz48XQbZcNolI85CUkueWIejzgXJktlwLzG9H+Yn51n7suuk0DHzPDLeN8H2uCkBGduuisYXiLUx'
    'Xt6Mtdf7Ss1Stxa3VzZ2367sri0tvkt23v/ww8oOGpwky9ubW8ubH8Ty5Lx/JSYl4hOK7jAiRzUBS886ollRdReDWif9IbUgrx8i'
    'fCvVCkEImhBSM8fdy2E9WclP0kEmpgti/t/4KkNN0KIfusVGEeoewNmT6l8bm43akzr82mzsyC/DVcHfW9sr0+8Wt/gDvdrAL6r4'
    'L5edbNS95oxh1uIfZKd5Aat56r6zoXxTvaGEIaZsQhSDcyBO+Jtlzlmbv/LOxWUXrks4KzlWh1e7zGfQFmOPrMsWtti2WJVZ+4tE'
    'djVrr7U/t5LpWUxi9+xcxTPQAEJntIWwtTzsD9CETc70oN2YbAJIADndllrKaS7V1O586W2C+tpARGUXuWm8EFl0YOJZAwJuNq1b'
    'GXh9YETtR0lxO1V49cuzmB8r7PB+DuawZMChbE9jYkXlqzi2yCxQOT7LDkaj8iYHfb13fEha8MWTkwwd51yeBdE4J/VEMUFNWEv7'
    'gmg3FJy46SSiwr/V3jHIIQxzy9unXehh79Egbujo2QcvJ73X0BIBwzkGFMXBkhR/2HQZR4f8SEvf77BHmLNQ6TkrO3p6g5Xpczz4'
    'fBQWQ+6SKiZWL1PJM79wwBlFdljFdCnH18aSD6NOxQ5n/JyFfRn9nJLuCF1El5Slwm7tmSTQA4us950DiykcyRFzakYUS1GfY29G'
    'xhk61DMjxgC2RCn6s4gC46C9kX7qnKHtc7sztHjOn3w1SJlCO0H4t4h8jMrO70rzSkHTG5U614hGNCloQl7LVtzeJsrVtKdBVEC4'
    'JFMESk2sWC3nzDLUAIecoYUXO80ONHAQHEWFjhpagkGOFkcrvbZjBEegMx4546sj5pbXFt9t/vB+JdnZXdxFryJLO8n65vLiu6/V'
    'fhdRCHJgMHBXvt5vp91/mgnnG4zDR28Vx9fNsdtHTncpZUfd4zlhVeKNjZZGN/wIrLNL9bp9vrG/2rFzDo+0NM5HDH7uUoz0dP1K'
    '1F7vssa7v23fo/spGPjTIM7El+sVKD06ahCZFbTOeyr1oJYU00ibipadPKPTyivH6OoZfreZV6iwgJwr15Wv6fTbDC+JVGH/WD4z'
    'ZiJDwrqz4LA7tBMPCrlTOpIrE40Bmg6UxWO88hi/ORVHPV6i02UrBSg4F8wMRTMMpOSw7Sa35tgfmszK2UTehgOAtoadjHSiRiJZ'
    'NWtQ3asn+QFd87lMEnnJMMZcvJOhSIqrYLPValpPjqn88d6sWZfpJLUfPBDyQ0LDMFw6YoGaOaoowRt9JTeyvONTJA2Tazi0GL/M'
    '3ajjR77bYRNPQ/qCp9slHLQqoByY2CeZGBANnxqCiWbCYBiGc3Z3C4LSdAsX6WceQWJb2Js5cAvD7o+9p9ewf5UrsoIcmpW+7U5y'
    '8lIjQUSQ8iIVfXyGuSFfpAPYxx4xF/OD2Our4DF8AZCA2e+mjl8hXrEBga12PgPdMEs8/pnGjCdwPU6HH4IgGa41sya+Z3uJVoGh'
    'xoC060Ded39Aiu359zNBy0v9LrngZmpyxioCVD6lw+r0dIrmL7WKFfMfnefd6tMbaHlcf/Hid/j/2pGnAHr0Cp6XCRGv809gRWEH'
    'nryW+q9QSUTnpb2PT14/vemg4t/4VROzy8riij9JRp1RN5t/8vQmy0/eji66VUyujbERPyVozB8TzJu0uZ+8LmY8YSXh+SfknLn1'
    '9AaXf/y7OfQOcEbLz2m0cOM5aKIJbci/JWOnzcIxyr4VoomNk6vJs6fTME3mYNwOJYyTbm9yPYBFLA9/xr/TJXm4R/xcaPzc7/Sq'
    'FReUZBdBNMfD459exJHq9DpMPulIUc0crl59mI4eRbaFSqJm1KiwMZz1Ke3ibNxYxrL4scLdYyhs5Wd5YZt+Tecf4rt412isxIXq'
    '/6YjIsR6/wFQ8WAAR7T95VsJS0mjyacvkBSGHS154Otn3km3n2dRGvoBHS1MeN5/lZGRV35YXPqbku39efP99sbK35L1xa1kZWN3'
    '+2/J1ubaxu7X/O76cx9uk+x6PR1ooMGcrWEfqAYs+PbyGADhcuTU7BSpY49+8jM3lSe9PipxfMJ4EMkmV0t+n2DcJIwBpSijdHiS'
    'N6KgHB9WKSxL19NANfxnBWbyTLr47l2yCkCcrK4sYhTJnf8czknZv6USZbK3ShYtije2JnmzIrf56KmGHoOJETAUfXRyM/OJJx/t'
    'e1mTHXRSKcfOQiWF2ICG2TGxJMSW/3rAmiGXOTnJKReTwuO1NLNqeyzOVBTSuB+U/fVEwlcUAT6KWNveZewhVMxdzoXoYcnt8NuR'
    'f1fVe7GEt++9+03ZEl6hvCJ12ZKSgRtz7YgVIalsGYldSl6koqtY4vn1V7t9dSvxFe0Phf+xEoTaF+zXX7Jr2hoUj8I5RydeQ6Ct'
    'mzC5bNiEdwveR3ede9PIvN+o2SWXbfcJtbY8qVNxFhSvBuMW8DIu4rCWSa6ZYAybolBOCxNmMZK6MAuUUWPY3vsBtnaP9qZnHfMh'
    '3h6L8Lk5aC+2B5Mb2E2PWflYN9ojO1fAW4EIBJVQa7UHiigLMpG9SKuo4eentpIZZ2XlGDBG2yaJQILdX+urdPuy56HwPoYrkPAk'
    '7DJVg9WiOMSVMBJKZ98khi6vdWbB1bVqjtfMa8pBZaftObdW1TBLArhNUJp5ppRmHnF0kc4oRIIw6eXNdUEgGFQjaydVDFpipOvn'
    '6N7/tDN0ykQSvQEOab/2yAtNTDXw+SIIDGOTAG6tBKRfUQodDgGFdqHAF3fP4aSoPPhrJArX1jH6YNIECpB+0C4ghbixu7i2kfyv'
    '/y9ZXdtYfJcsby+u7ibV1eUfa5i4tbz69RGJ//g//g7/AU2UIjjiriOEJedZF11GcO6/y3/Kn6kZ1Ztu/7h6DP/U4fR0s57Vq2XE'
    'cjlE5Zn32+9E5YRZ4vBNdRQrNyUebpmCSsqPubRxPsxOCSXOY9OcZhdo3g6BM066nZOPjJUVAmH1DxwSYO/+RzUkaLFWT57PEEIZ'
    'q634av6jo2YPFR81VrgbZCet5Hw0GuStZhPZ/ygFbHT6zfwafn7+GtfCAjP7K16VSf+GEt0bX9IyMuEJuMNKQJyYHj+Z3pbwJ8VZ'
    'CTsSrS42hCJH5VCDW6WvlR66hm1XY2520fJYuLod49SLTT5MQE3stkGM9VoihnVkHnlEFVoY4tIVGR+5SJyUyr6qa17FRUpzNblM'
    'oWqbg9R4VTlKDd75rjqVK9SmhT8ZzfpdL3Gqq2yKFeqTI698Nuh/qT+4phzXghRUDfi+a3R9ZKLjWh93095H0VfNhhfoMAl2g1ZQ'
    'Ft/JD61v8F/nFZmMSAHHiU0fk2eIC137gVujiAQ/6/ovNrTGFFFqRJZf5t8869Z8sT5TnyyzVZJX6MdIb1vaA9ti9wrN2GC0GG9L'
    'm8dxgHSY5mnnM+v0NHBHMBadIe3IkwRFKsbstY3d5sqPu57rN7VXnmvC5k9VKH4LxW/h735jH2vi534T09fgu9bEILC5qCz5PgxV'
    '00W1BO3wL7RCYNetONlpCbdM82slYkYM9+Qo3k+lUUmmksm9PQpcoXqLL3vb8tbBQtFjJUmvlS5dMG+VE+vR6XS07twUsyyKM/up'
    'kyZ/wlF2RpXc2/e0252G52Eea7X5097i9H+Zmf5jsj9daTxe+NM3B1NPm2on0fgVYbqVVP5klvSOiViNCA90rYSFTQgvLjIoN8q6'
    '18JIszNpenyQOkxFIY0vXFufteKNa539H4snsrblOOR+JDGEJDpA+Qc4PVVirBgDoKzXltRaZTLoTwZ2jW6rT2+wwrh2dG+QVUoc'
    'D4AgV4vxwmucb7uf5b3KKMkoMkWyuxlgoa6qlpOP9tcG90BxQ0FEB/E6ufNkxiZH0U6C4/hYX/y10KPxPU7lUfPbRNY5+bZ5VLu7'
    'cvTg9rvtaRJUtPz9SM/usRF6OK9hNAQnRjvH6mxVptH2OwHw8ldtnLw6umN4cKjEPYg/PGMR3gpLP2zQFXj6V2pzXz7PysbKh2Rx'
    'abfy8KkBeE4/eMBB7ysby8nm6oMH0GZeV6uAJUrPf8X3fTsBMyiPPIpuMWqDno7ViVXP5fZYYWFf9LuFJiHiCp+KilyluTMFVHFF'
    'T0l1EotSIacyuPdTOv0LXBP704fJQfOsA8B4aJUGMUh3w7yVqDX/WYzG5fRjT4Z7UIcnAc4HbhWcfBN66fTm8AoAAmv+cnQ6/bIC'
    'E63zgEIB5j/+r/83WfksEVjSnBCKKfj1Plc/bK/trmwvv1/ZTaqNq/YvSTP5gBFphsuXQOBiqMeacI++xhVg+HRrcLj7t62VQxT7'
    'W/3C02GW/ZJV8fgZ2tn8qNs0Qy+X5iH95Wd1L88iSfTA8JMNzWh/UWo742MWyTpDdigSJH4yhoUL0xR1qD/8PLRwjuTnA8Bc0ZpM'
    'qpHCdCQXDeWTyUU4FzMs1afSeTR+ThdekSd5WQ2D0Ir5ejD3KkQdFYsEpGCY4MqU5Enrk4roUUwqpwk274tzATGGUIBUEKYxNWST'
    '8iDNaH74qXlm4VOnSlDEIJmuVUckcFcYZy6SjlSipJsb2bSRCOWhyRCGWSCaEiaaNAXFM08JovAPDxG91bjwXHTqMGnaJdUf0bVY'
    'wBJLGPn1cHVt5d3yThxT0EVH3dEP3n8O753E8phlQzPiXyo1D5MxZBhAanJ8HeacDBFKwlTxOA2px0CCtDdlQegj4Zl7GcQAIhin'
    'Hy6NGEWUgX85vZAiHCDeAWYGmQzh9WCWcHnMEjvW95W9fTbQwVG3k2dIqlQpNhuTQaL6KnqAlMGRy0SX29IX1T2mLw5qVXyQHtSa'
    'Z0BiPJ1Nnj4zZZnWkN/9d/0rQ6cFTe0dTh9MUfWk0A0q3kuOr8KkJrOFtAhxa2i8dSD1Bqg4btTGSQRGSa+Tl0hG8bRQAoasJT/F'
    'Ovaq+c4VladeV7jCoZqtbr6fyR73rTw/srTGgYyb76vjIRp7NBdeM82GhGGx0N5Prw++fU0LE8n+fe84H8xx/SSWn16Y7N/Hsrsj'
    'yX0Vyz0zua9juf9y2Tf5T2L53zz/49zt79NBP+dSTypPiqX2h/u9BZqdnr5TnhjLfvju33hFg9XmsIOo6c6WxK/jgIOZBm6mktma'
    'ViR2/RW3mCOqVzw3pYzSUCgPZff4VqiTHzHuzH4cmixqEH+wEw/8ZS7MA99mRtAhoLtRn56b52m+eYV6hPAIGl03MHa9OQUwgprE'
    'iL/M9uDrgLhg6rB77lKZD1p+rKgFvUZzkZeU8bZrnff7j6PY+qD3C5wxanTTD+PJHX/DRRcuQWTTaWi1f5c5jR95TlhLMNQS2gu5'
    'bu+FapveawGjZSLDS/EPkcAj116DIekdTCNX56x7PTjnUIlLM6YdBKZhvwuXGlALjWT3HNYeiBvrV8nFxEQupPLvM7JOdxS23r+c'
    'gf9N05+X9O8x/XtC/2aUMXuK//7hlD7+CB/PoNQ0/aGPZyl9PMvw3+9n6ON7yMm45dOXp6fyaHWrscFx/E7Os5OPAzidozxBPYh8'
    'hLp64syJxBTEGCRvhT0KJYAupICyI3Ux41zOzdF6m2ok72Chdz4i6c9r3SElR/IHAysFsEuGFMZHVKP8qnrkIazxHXfwmsQmJcFG'
    'lSkK+h0aEjv3u8Ep8OosJOozaUENZ/E4TK/eFWJ9PDap7hYzKY89JKe1eTzzZnPwGo2G1KwbL93EM5DERuA7cUF5OfQL2eoAgK34'
    'SbLF8ZDW3QBsBod8XQfYVkG2I5kakdvjv5DcJK5MC77c3HTlsWLxQqmxjGSsnKxaLcDYAhpPkNbFpxbIkdvKOT8mS4nzMNPOQmOi'
    'oaMp1hDUiG52ddI4eXpjxzs+igJ3xPDUtuFWRmPjSHaDYZScKK70bLBJV2AhKKEYcRJct6ywX/LuvguesQKdNY/zZxUw2ZWG8hCe'
    'lx50vrRJBK3xPwEHo/2QfNTHDjPjhI5Hn8auVqOUssuPocQmHI5Uis51GfYH8RHq5MmWNFTcfRySRExjaLq44JOdGJnzqrixs3WA'
    '1qgutK7av9z+nPd7tadNvgM8S15qBI80cTzlqLyaT2ZfusATlDf3wGt6O72i9xCcc7dF/tpTFnpMTK+sG7n55JntF9L3Zg6sSgV8'
    '+lg1ilEnbCE594XauAP4+3AkH+JXcNf/tNn2VtsNE2wR85eMBGmHyeutv784H0s62reRrIDL4VhQag0wx5DOdkq5e9DjFy2mWSpM'
    '0Ca/s7Y5zJE1vd8Wyu1Qx4HsWjH9w/cySjfi5GYPag/d4bK2bEM4iBO4ojP/spI0fUeZIVNOY+TvjK+ETkXauxPIYNWQ0kt39ewE'
    'XJIN3vBljx3zstHvHuJ9wd/7vwUeDJsBIpq8JPyg8JBO/Ckw9kC8Zyi6tkiASjkuBjK1RfjoBLWs/oLK3IVTwo7MSdH7dXmr9OIj'
    'toY3EH1T6W4Wyuevilm/2WVvm37vE7w9kTDiU8fhOSz3RTw48YT9NdH4du43WUXR/YlIHfb8Zg/mfL211U7Wbfs1NScyVpuOP3WI'
    'vjZcKxZMjCPGMpBztOxdCMyhGw8OTQdWE8zv/0ZNrc79j+eUT61/uaQIbWs4b0RcOI04hlTYrUAtL5gXLKFRtMpqI0I0X4cd+8m/'
    'nOuSR8bfvoJPPqbuCYCj5l9E2qsxL4hbkLV2y5vLWNPhHglvrGqI+msxrzcbtmHRK3UrJB6RIcMuPVv0SwQW7RQekz2sOTszY5J7'
    'WdbOt4HEzK6U/z4mIzExaxeS0xyd5R6tfB50OyfwxFSv/H/8/V+f3rjlpL0f/+Pv/1PU75Dhc1T3pkFEbIvPnDw96tak4I7jyntM'
    'Lv0URepDgOTCvj2mn0GYuwDG/UeqrxZ6MzaqfcPspH/W63DgARc1op8bx2aUxt1Zt2LMoZOgQN7zlRh7xm13/1RcBgYUdCHPUKg1'
    '1/GUBKxQonpcKhpmCcLTo1JPPlvTf/Kpibu++PBK+YY+xvR7L5Z3QKoBJt1dR6SgpF4rbhzuycJUixsJHk731fRCtpmlqSWvkpnG'
    'sxeFbbeYRhz03M3eoIK1Ok+urrsuh1nm/CxZxk+1g4afdTxYXXRmscsav0r52RalcFFQeKHh0nx4XU8HFKPF5C6Q2qjnmg2LOBgy'
    'KZMfaVKqVnJS7oYtbkYIAaKUcteo1tmWdvCIOpiIxaR0irR43o6Hae/knJB/RSmUuIXYhq1hJzkujdZmBzlubjfW2LMRR8QOK7vL'
    'I9LwZA76kIohXekvQqGhWtEzvSmxlZIgyKBUKq9BgfLlBPg5hwPJqlSCEA9EG3mrssVHBpLh/do83m9W935qHkzV9puKWQnP2v3m'
    '7dNa06MrqZbmlahtobw9wwEKQq35TGjZUzYxay/aCJNx8ClxgKZrWyxgE+vJBsmzqNICPxoWGiQ94xRXPUw6TFXaCUfGrPlBehVz'
    'QDbLO9y0EQaR6BuT1bWdYtMd5SLXEhIWAY6ty1jGBcJE5MxiTkCl+NY1nBXAgXtmM1V2IvjukVIlayXBcTW5Dh28EWBoWbAolnlv'
    'lr3lNlAogYMYKQCXBQoQ3Nosm6FH0Sqih9iCbvFKVBTlQNX1ZUvf/nN4dD7sX1HwkpXhEJ0GqyYRtyQXot2bkoJUwhXR03VK6FWr'
    'yfWCayF4Ktzr0jCYK2zL4cwgQ0FQ2mt32umoQPGgZTJjdpznBziyO5nY2OIhlewNiac3o5QDKQv9XIkIb8Doq/IU3r+w/xnKOrg3'
    'T8jtc/Pvx1I0AvHZZyT/1mN6nbxACY9Pu2DTUgqFjgETksuYfHShw/leOrfOlM+jCeK8WiRo270uS91nQFhFhIMC3Xtw/u3aHqBp'
    'Hfr9rtZIaBzn4spz3PgB5FtCRdGwgMFUmI9iBLnI5o4LgRlYYl1K99JaSioFyRudj/ee3lCB8cGRghNPnh03yH7kBy5a1CCml6XO'
    'o/Kij8F9SQiUx4sIbJNSjDYFv/76xbQ19m+nCnWMb8SQKnNlVBWjQWsThPepilhmZz5XAmg0Lnrbmt4cpWL7D5huj8soPB9aqWmC'
    'VfrFygdtEyUbaux12gcFZ5JzXwTx0lcZzBcg0cKoB5EuhizfaxNlF640wl7LAmFDxkJkvn2ljmMxNMWvZNHRpD7A4vgv5dUmL+Vo'
    '1cUlG3n/IiMnlMQhZG+L/vZQho6t9thvCzbUNKaYv5FklCwwPvwyrGSaY3eL3oi9Mf777h6TiJF9o3elTMFiJWSQejNhtEQJDi81'
    'nt5AufFR3ccuBcREdJYgNryk7a0cv5YKNMTueaZJE6MMiCGi+n3Yp4tBN/uMonxmByV5epp1mZZ45ASxVIlXzLwaG6Yphxz8dA9F'
    'LASZLf6eC/swdFXJRnkjoculpCCvFfkU1zSN6y8nO/wljwGjgEowkE3BfXxsv/wnpN16r7Qc3zTPO2e9ququ7vphkrqm6DbWrl7S'
    '5NMdoyoZlHZdm2U9IbgsscU5ljK3VFrYvwNr20+R0yTdwDxTuEEzPWYZFJ5v86A6MmJ0AJoxK8x4gnWjX0ZZsxWNpVwX6EwXpkXk'
    'lk0NSC4qgPSWK+BZtwqoubFaW5JqYRm09A21SNx2uloeCAP64HdVIgQIOT89qvlMNPXO8iAEkZgPJEZtQlu92PegYXtOGrVS3wia'
    'djOITis6P6XYUdpaecWHPEnV+9GQjILMVXeWZ2Zejz78CcpWTD7XpuEDFTDnRl+rQrmjQoaFijenhm1Z0VAK7nv2uCzvMssO9N/J'
    'HtDg28P0szdzYObm+qYHq3G8Vv5aRQRanguoIc2veycuHvoh2ta6kqsdwKCo06D5hqQgJ2jkPTz2XvINnl6l8CzDwg16hb65PD0F'
    'FOXYcKxYh/++M6HlXsyQG+Nn38mfB11b3XR4piIbYmPrb8zt1e1cdEbeQzh8sNNIUVfjLrWKUtg0r3vlsiH/Lx0kyXmqjmL6Du9G'
    'SoTNZM/Ln1/MuMRZk/jdsboI02u0NVNOHYiRj11oAe/jw6yXA0qDXf280jtDhjuLIgBYPi80/rxD5aPrenyJ3sm8OaVDIE8wvCrZ'
    'DMFILoEKJIVHtBJuVDy09QtNljcee+POGjjqRYQr3nKvSoGqFa4bNIWXGj9hbsaW8sfyJM99TL8aGNHE3QMhbYreou5B+5hJiscF'
    'poAu0t51wkOIEkFuDggdK3YeMgajWxeOG4AKyz81jgR4GuxIB3cJ8o2RwM1s/eU4VtBqdwdO4sPX+mDY6cMsUTZOFo/YPUC0nJlb'
    'gz1u+Xq4lTdiLRghj20hmQGUPuse7IK2TB/VVCYx7ZKO3bw4F0ABHSYvAXEJ94nJnwvIZ4JitajlmLhkH9Gum4BUNpSgF12kMHvM'
    '4AxkndmtVDx03isgW/UY8m4HUMIMOyALXzXt7KSLF+RO5xdEJcLzpXYWGofYz0IDUCpMe5jluZQjhq5+xXitIOyGyDCMNOrJyPnY'
    'MZQQFq9acV2ok6HPx1194FLcWNxjLlrct1biQLJOi9mi9UVGQp6J8gfsaTKGW5fcfxzCuo3j/i+9qeAOozx/Ge7SNnpSY1NZNKc9'
    'hW66Ih1G1+VtKuIhFhqxdc0XG7dF9SXDdjfAT/uXqyurqxw8pOYeeHpGZqGKwAmXUkecVDgQVPBK9q0GaAH+CDrZr4+Fy7Efh4E5'
    'q+uie44+WMwMibsmX3DSH6npNxgC+ZgfdnqnfdJ+9TKP1XNN5zSOQ+2FGgv7EH598RyPTW5BiSfnj9cbw4J58x0aH166GSb0zOU8'
    'sRn5GPnvON0MOyS6ZztsqVb6ANWUtZGeR2auDZ1gZQslECtG2vCmHW1DlbBteLTMI5+MnvjMtQsTGYTJ06NYiJQwfbU8kWjxBSnU'
    'IslkNEGKR2YdnoH6sRt5mDpAl4eng3VF/WjQZa0ub8f9d6DGFIL6mTZm9tQEoY/uJiYdIf6Paavh3hRm7CYldmsrYabAmvWTVxRy'
    'BcLWYJVh1p0uhX83xRcKR+B4obFnsg/gaEudlj3c7u7wWl0Q7+VtWmaKs+wtbjiY4PwEbRF94ik6xbpWOgs2TrdZG/PyVSXnYuW8'
    't7WfWjcPSD3iccwxTWRHNoW1H5+fZekXvE55BxEZ5v6YFqyHtZsHzyYVP2xeF9H5uCVea/s9FSwuggOMLu9dVb3iHBXRVISpC1kU'
    'Wbv3WgoOBPtrU9YaIpSW9UebFIaXq+G5B7M30LH6HULwOIBlzcuyE/mtWFkWJO5iYE1kYkU4I4VpRwmZseWEhItYjrb+DVblXitS'
    'uhqTVoIn60pEn1NKPrXojndaOPl4tvcvT+F//uuQar5RiOEeNeVtxZ0GjyZur+50t5Es7sEMhp2TFuHhL2ZqXQ6EqRFnb1nGFdpP'
    'jpC6VbSsR7ZGWVoFdlXIbGLn6K5N5rFUyem2Zjgh+Y4P7U+E9pHrM2JeAdxkbPLgZYnlsTJJf8wsLAc/lFhk9/D7174WapGAakvn'
    '/X6OihchWR+S83USxHj7a2wCHBmiGt4W339FXtc//v5/Q2svZ4JoXx3DkTJPwVLenc9p7kqAViI4TCONEGJQ6QGJh+xKaFiMbqJ0'
    'gR35l8QamUT3mCf0iMeBlBd/bC2vMp25SjY2VR+zBMJftsNB/GMaakgSHi+Y94VVNuDx7abHq8P+BTlcdVcI6jF0UNV45y/ba1u7'
    'h1vbm39eWdo9/OvK9s7a5oaTBE5SiLZSRZ84cdk8srq6W6DfVnCru2xyWII2qXXf01crQLYum6cIW4Ub3vKuSDvD2bpKnTwdk/8u'
    'PcYY7JUiUHqFjUI471srviV+8+IL39QIF8hXJTeEhG3WZTJRoCsaaERdL8R3yxhrAH2gre1smshdrvzYynLrHmHuTkk9kiosewv4'
    'HtoLrtzwvIr//fRYnvDorR9OB/xB3X+krUN3wFaHW7WAMUPVIDVVpIo1guOuP+fuqGDo9+gkA/VKg2IwYtKHzi/psG3oeYfhjiwL'
    '/elNKdoZa/zH7/MJpa0UroKm0ZW8Mk7Qky5bCETHjXYCjaN68r3BppYgyvBajCB8NR7hCZ8ChY8WC+ifjWo1LrI8T8/gwvujbfY/'
    'g4Pxr9ctW0CiGM+fhkCJESceYaKtW0PaI4vTKUadO+VXJWIuvMG3KaEqVBb+bvSNO/zsEyIOhkozRPbH/Mn0Mczyy+6oHhd27f3U'
    'QLe4zOtUHeCfxZxawnqQz/zYwEtDpGMyROLL8G3HEHEu5MEWclxFGuz8ksNLNDtF9xSnnSFyD5wrbXL7i9pNyV+y61byV1qwQQrF'
    'atKkr6m8zCxSKxe2A6EL6H2PvtuVxBrZHPfb1zYGvK9j/QaHti5a7MQkFt31n6pANe7tXyUHU629n/Z7B1P7vdpUbb/XtPR30IBv'
    'bspzng97sSrsagzr6LKSytvO+ebZz7+tNqaQZL3wqDtmAKwXajErAMad1xZKK5OHrUiX5KJ97zA5WCA37WXVxdfWeljdeGgvrze4'
    'Xk+K3TrP7MWadpHXa4aawr1vGJ+gZnnXMVhwGE9KFqmmK3IaVZTsWE1eIb9L9kvG4S0oO1bRrE1NVTS+ydhKibLjVWF5aonXp/gu'
    'Y9+nkB3WU2AtcqwQ2GYOnHqQyBvcMd3tf8xQo4HbgePTd/5f8vDgqZx5qmCjgfduntXHzZpEr1fHet5VAkIQf4/6Q8cLPn0XMZDL'
    'Lljnm6wN2eBRaFSOIc2VtAqgKsnhhxDjtKTSQgO/JOPapV5L0meXJBaDh6ewSSipczkmhQJRP6s7J7YY8Y7iB12kaCCckRN7G32b'
    'xK6fR4KCOj3rQnyexVzUBIknyQ4wxehmaUJiGrPUPkbBdLZOxZIFCHqM+VrQZ/z7IDU8sG6tYfN62TWQbqgLyK/2pPktshmTb5uP'
    'nM/8/eb+t3v7+f7Owbf73+43jVt16kRFZfM2xHjFFU+M4rEGqwh8Pqsn08+sFMORzrHVsUS1kluO/Tnt7R0c8CtKD3xvf88M/GD/'
    '4D/KwO3Ii3EP1jZ2GxQzif40Vje3l1aWHz0kfMEeJOcHhrPBgCAyJJJF8UyUA/gGO4B/XMyAnIIcXEYrJ7rQ0IJeKQp2jt9mIexu'
    'sZdadgSY5Jen6G8dyKSzRvKEVmB7c3M9mU6WF/+WfDP7zZOJGyV+a2WjZHyO6Plm76dvDr79Bm4UoXt+i53bVU7jcdsIyWW9NnvX'
    'QjfzyB16zfEt2mr/Xu8l+6MDudweAI3ap2oRJGd/9TkS6FpdXF5JNt8DaN3Sz7WNFv+AGd0uvd+lvzvriztvE/O1vri7ZL8cS+1X'
    'zeo32KEl1FyAlyfpGySvd+GQvALo7/V7067XWnFn0IXkFP989aAdMt5t9TyckoG0LhDonMaZjljt7FchE+GtWXSSfFNPvqH/f6Om'
    '+c3NbP35eD//lajQzeybKThav8X4yX0vUAFCxqgxz//q4f4Wx8QM9C0H+LyAV1aHovNogghVpdFMz7kjnArC2045sqDTIx98RATX'
    'tKzl8tgQRDx6Iq/EGb4FcO0rm5AQhoPtsp17HWOlJJcYAoACDFQ5NEmfnHejP0DB4n+yXgRN9JDTfrfbv4KDc3ztDRQtFRQRt7mN'
    'iWoNTLwp90iGlx371LPzIbVWRaoYDUo3lXlzUfz0p6ZhzUs7pOlQ8j8YP2NaVtD9k7RSdbE+THSYAxUlZp/DxHz7tNgV3IfYaCHg'
    'jC3ieOao01me/yr53ivwWF/hcF0TdkXMyliVsent8trOzua7v67UYiNTbe03ImPHgaNCkruOAAo6/XZSvSLVTjQiJVTRDBFhktSU'
    'BaLZNZ/zBiujNuyuo6icrMtxdCvkUMifJqMPFHjddSjXA0ikA3Fi5muHMWVBGq7nAUozbYIDYGjuh0ugilu4DPmoAydJjecYQ3yj'
    'ZEyOmzsTkJYSF8dzY4++HPLMoTPVFKzl/z6LfPfYX5N3shtH66E8CEvxvsDyZHA6YVV8hAg7YTbhkZWdGEVNqI3vINNV0Vw1HzGC'
    'iaqUPM5HRXVH+zioNr7dt1RYHsb6iq914Pxe1hsGMZ4cESnemnPoX9JQYANbujGFrZgARBgwidhu8jK34EOQSvI1GZYfwOqfAoPl'
    'W23v7P/ke/5gVLjIdCAiQLTZvuYglTi6R5MIHlcTSRj0NMfX+0BICn7ofMyyAZpeXGC4GsGADnN+CWX82IOJsTF6eGzaMuoMQehN'
    'ERXZuEFWa8HG7yEOuB+SUzHd2QmVIbMOT7vp2fveSTZ0TP+sLdFq86qMhXxBSnAgbWZCkszlu6XbXq/UwCGFsl9eZU9ZIkfzitUt'
    '30dYgeL/y/C5WyEvtP7IiZ/tmDjRSoDtLHS6kfxa7pCRvUkpHpbIQSs8YsdK4jWr1K1WihIDYpgjlGokTyTgphvt+AlH5+bWnt74'
    'u46HSmzYRWDAEgiAu6OvO6KvDo3dOG1/runYvqvLPxKx0Ut+XH8nW91IPmQJi4AgP/ljc3YmqYoiwPyT2Se1r3GpcE7okUCck7P1'
    '3T/+23+nFXKEGaVLSBXI0RGXbsjuNesBSLv/VZgx91YCLNUl1D1qVLgyiy6ajb38TH5lyQsuZFC+rV5Z1pF8vPsFy1S2CiF2HKku'
    'jVR2/Sg7okCiBviDxGSyUWoktF8kV0XWi+S2L9PutI6D5I2eQvEmpR2H8W1a3sq52H3RyjYsXjF37EVwgROykp/AhT70Yghggmjk'
    'Bk7pf09euyniRyHvFed1R8Usji2CsT4KWU84iwJ9FDIr0h3G9xChqgPHncXVlcOtxZ2d3bfbm+9/eKvU4vdwFeQagm9EfHmlXnlL'
    'UtvFXnu13ycgA4g5AwR+3b8EFFz5QEaiJI+ALxTTym9sbT09GfaxkUUMNYw/lgBJwx8Ceta72SQ+AeYhms/l9w6yIVRLH1IMfJwO'
    'P9IhqawDfs5hTEtCl7SxzjsgDbI2jo5agNLimrmym57hNVB5dFALt3KZoGVJfNxWe/02vKJcIHrZXBVHGUugkzKugDu+5zyJnLCL'
    'DPEqwaqW1oDDBdvzRoBrtn3Zy6sWiXhdRwZpC8I+k4NfdpSDI8O+jYSKKCBMJH3YJeeypQL0EXmclmzA44sjoG/huZlVKzvki7qm'
    'taqGsjPoBStSw2zc2rKthrpAqCseKb2EOX77aO1wNkSqKlrjjc127aN0LFp4FTL81nMSq8VmChm66LgW2R6kEYx5A7uep91hQzbZ'
    'I2XwxQ7WJOr1Al6n1P7NuBKarlm11vEcK/R43e5wvHiv57qNEuI8ftHDCp5fJkfZXdkk38kfaUibsNw4vnkePxvldE6vq7aX4mrg'
    '6omPmNwD05gXmVxQkxwOdLzCPozYXYn1ieX5jXbJFBjKS7G4lf24sM2davIIqDpMHM8D9WcQtRfsqTZ+cqQDC4Xz2zJHC6gdTxrs'
    'FhM2jF1TkLezCt0VmOCi6ibGgOWmKMcWf8qmuYafAaCiiYY9HMEBAdCiC5suiuCXI3TtNp/sHbHnh95o/MoOn6fPu8XogNzper0Z'
    'b4ItOxgWktWTxW7nrIf3gMtKTRKfqR2SxW1kV4huXalcJ9cThxhcEYdL6MSNXx8d6NheYiBGcjYN1w1K8iXTLNmbD8rwE5OXR4LX'
    '2gVKkld09UiwJoBUb6HYc0CLmpFnQT2hGXISSfUTfpZwCj8scBbavICy8ssLuIKua6VDwcFwmddu42if5p8I8fHk9StE8K8dNPtt'
    'j181Kf9V0zYAv02rZkyla9EMFkNqOG/q/WHnrNNLu3g/wUL73p3clkIuimO9BIp6o1TPuAXdoGEgwS57yXi4oTgeaPjTsEGHK+7g'
    'spGYkdws+ONE949kAcLxCrBJG3uHmy1dEFzM4tGhG7GFY6Fb04NrTHUgXU/odqNUugHribu8KNVddXyQ8LqiDLzQ6gmpgFBP8EMO'
    'YsudCyXERL3UbQo3SLrycpgcoARLZyDlyHnM8AOB81TdphKRb8kbWT9MDBdQWETBIcNHErb8ANDGxu2Q8aMMvF3jR+zmxUJtfGN1'
    '9SNtUcLFi7cAeabZMaY/Vec+27vy9kyAFhuN0sWZNLElJXCkChVpfj5zP5+7n9/BTxs7Un49qxy4W0/iD8ilxu6pKcyCnJBCtCCr'
    'hKDNoWZPw8vv+BKIS7h7jJVWNbjQ2PCEvlZ6aHnertY8d8/sG4HW6Yxpl3zJpFVDnXPjN5mzgxgsvtOiM3TnJnycQjuizRjovJsw'
    'g/i3TOtd5IFAEw/hSd07y7gFptgcDYV680Qj+U7GTHKLPHrZ5j5fdH3tMpMgwcxfLUBC4jgljZknSdY76ePTf/7J+93V6ZdP0BVK'
    'rw2P3h6clV7/SbLwmhmAfltHr1YR4ZH2ZGI2jQ+YO1Fqela73dAZFeO2d/wk2c0uAGpGpXVHks+R5/tU569mFvEqMkmq8QIryMkL'
    'VqRiVdpEO9A8UyTurtMHDCoCkpGir6UN9UazkGXfaQ6FZV3fxDvrNk66aZ6/6+SjhnHZUvUZEdMYiq6iGPiFwcBwHI5xBpiRclBy'
    'Gdo2fA1VWE0ABvUvl9nweocMWfrDxW63Wmn4Y4L7BR3ycSp8wPich7h+9/Ki55uDe+uD2ZHF8Z1RK0EHPRpi68SscZK6VSJmpdYt'
    'sUIm4vDTvkHc9cbaFLFWPIceA4QtDDXBIIwrTPrh9DorCGp08Bh/PxqNRoHm96x/i8NEcA6kKvWSZ2I9qVg2lf8+UH3UtDSmYE9b'
    'BkDNEgiKgWUzBpfF+Gq0TSVnYcIeR3cXmrnf3t57O8IWcRusqKcMHLKuAYbIFkFmPfp40xQFI5Yi5mlq1HM3Ttt1JgmBejOKuDaF'
    'dqVS+Nggz5cK+Zr0Hy9YLgorXEakMGEcydUNGmKZiqjgX5GhGIxXWAK0TiobpKE35nyvPMVltN3E15HA119pG2WHO4wP78hHx0J2'
    'UmdFolO3FiM3j7zow1zad6Fwn87ZQsL0/sEGOC/t8EuaDSclw7zvrIhifcikiPZA+8eyAXCLk/v3rDss8cT1DdEsXhfN97Pg+3nw'
    '/d2Bx3bS3p2VtUQg8b33rMXgxM3Za48clvMiGHr799/MPp+r3LEMUcw9EctggfAAjUuRkYcABoDi0WL/8uw8fOAZsssjkSRR3KoA'
    '+olJEtifgljQMgPdkdEmHcnfeHDKKIZR1TRSETdWIZrdGWTdLkUJWDvr9YcZ3mJ5QgGrOkPWMlxdRu97xxkyDTvt2iTqMtraBETl'
    'SjXLN+wBjUYTXzUd1W/oXnk72ZLyyusVZD9sUBlKJJnXZlR5Ky2r4y5iSHfPOtGjp4JjJY6KMCpIGouKLU7I6Ktm5+f9EQzi8tiM'
    'qA5PQOIYuKGgccv1sHOS6z6JIkhEtKjEjHWS/CUk27MywDoJ/FAHiNON9K8o60NlAntitehFvBOX83hdVGtf7EBCqVqcq4vyoKA2'
    'fjdG/Xf9q2y4lGJYhAJXrUSMpN09o7yN5EN3CZQClmClJtamRnGKWIvSlGtWaJKgXZuP7XLNoL2esBfuHJRh+VhZ16gg6/KEdCMS'
    '9hitmjfXu+kZCuKqIjDzJWZxIZljN7JsyFwopm/Lr9K4SeITKWmBuM7TjHdKYmZ7qwxKmDfvS7IsE760luXcByIwj11fVtlj6pdK'
    'AMtqR6SAXBWAUmaMm103zuYtpxwBpBYw8e3CdRVLfqMowmOOvRMLDiyzPlK4OK2RY+VHynNUZn8hGYpb+hws6Ke1yvgNAdCyeKNh'
    'GlsR7L4nmOTAeyu5wzIs4bS7Pus27jZu+rDfvqRG3nfa1SNofNoEPDmSkpBmpTyFyI83og9WgVKVuhfi8d6DVz47MPqjDvvI4R1t'
    'uEfzSWEeKzbKI92dCbPMfI2dRiUaslHQv35tV5HdMgn5l2AzrlaxN4ngMVE4IE7MmnF3Lxah4d3DRY/MusMGuGqwC49IpV554rm8'
    'oMthDyMV7R0cGKt0wxtKZtSVvoS6dSZimZtLCWPICJ7V895RBHgXTE0FLb9GdW3bsw3xSGPc478Hk6K73xCcB+pBouWJ574cTKmK'
    'glXTa7DXJL3X/G+gpzj48o12Qin6Msub6+RtYFitsdwfff8IT14qIj0yQMBLyf4BUt0TFhry+XvVCrUyJIcfjHGwjOHZChZZUAol'
    'JA53xGCldpfHWKJ4vSNgvf1oBdNhvz9it2th717gxBFLvxXiw4qao4iMeA+9+cowFcF0FV8eQL65oo6ZUc2OvGEU3DGnRj834B17'
    '8/LDokYOqPQenFEblqJI+AUu3RDO7iZkNCqxpJAeI649trRwD+zTug+BOld2Yv2zZIIDaoLGpWElgjjBxTUd4TQ4sbGQs8rrhHC4'
    'fgXk2FdvJYxcuGQB03UF2Ej1ZdN/FajqzmqF5iUjwl53l04APBIzu3qPJwPK88LHQBjfOv4cmHzdFwz7ldSZ6CAXYtsw3/wYIUEI'
    'XL8JkZASSwAHiW01f7qyjDBry0uDMk2n1p/wpLaJzURyVlOPvWbcUU34NlDp17KbrDMMcU0xXDDuWsZRkCmu5E00hkEEl+hmIuSE'
    'B2DWDx3dkr8GKIzTsS94f4gHr2LEBfb2Tt15/lqGWbszWpP49TboFRxRSlORD35C94oMQLfOw+TtCK5U+kHawAn+rO3nUwrEVM+1'
    'WLCbqh4DGl0umHEAvl5gDYWWN7RwVnadBH9kyHyr1LiuF6uQGJK6OwomGUC/6V0XnEpmzVhUc8bi5ALuRfackHkBB2xIWb8pAPHZ'
    'mrcNrHmAbj9MW8FEaflPjBOd2//1/9TKlxcnyQ2aqRkXM/PSkYqfrbwFTep+/5iK7B9P7laY2j5aoL+FLuU4T+qUpkylbv90uz+1'
    'sN/e228n1dr0wc339fEdKyA1fxN0I78bZWjH8WtSDLwGNYruc+1tX/NYhg+2NHLuM/F1YR1nBvUxYAVbPKHiEjnQTFqFQvxtcCZs'
    '8s7qj/vHt/vH6+931pZa9HNxY2Pz/cbSyrbbe54lXBu2d7hw2p1+RfuAHwKp0/nFuj/7cf3djk3TPDXNHZ9Ap3gyBkM9lDLGfbKi'
    'ptRYndY2RZPwC9aRrdtyY2/Yn7t9eW5ghdq4VitwBoxnzhLXo4n3IhdOSBBZy8UlgomR0jX50fSCYOmnvvEQemP6nq17vWjjr0rs'
    'KeJYA+K6Mw4g9cDBp6QqBkFYz2XVlQfPMgeeY8fRMHeomREBgX/niSaM3Hiz1hOp1riJ1dNaO1JZdHLq9uJmvZtYbaOzIzU3+sT9'
    'sqBb1wGwRTDbclTxQjIRqEZOANxSvlU9yXHrBHWUxH8vOc+rClzcjGtOSlNkqcDjeR2AtuvUdO5Un0afgeLgwaAv5YerFdfT8G1B'
    '76M04ra9Wq0VnQorrm5c5cNXr/An5dRjUWus0WhYXpnYU+0diC/9ca1aC15TTtmbHowxVaeITYpV2mwHvBtCMvfQ9LjR7mH1ZEhB'
    'sx2s+WOt5qE1Mc3uMa7yo5oaurx0SHFFLN28JXMnsojsThL3pxVY9HyZuhXib6tqdT9FK74vvDv47o1QCkNhC+G2FI+C3hbdEBH+'
    'sjPxgRFxYLx1KFe843vp0Ka9fg+FfbTzznDmTk5ELcLgLuyq2UZuyjA7BfC9bZGiVjLvjYuWdhyV21DDYr6jmRjDe6jCa7uFodN0'
    'F2X1gpo8aau3BPXalTeK2weFm528KrjLEz2Y9vpKbzRhaAhY3MlfO3kHQ0axBatpicumw0xUfOGyh/ZESVuxguvJ1Xnn5Dwh3fVp'
    '8qwG5ViA2QhQcaj1hSSfYGOYr9p+haZrSjhRshRF5eYkeKL2ogYtzubtbqOVEqFXxHwllHEVRCrVGyNpUZMwlnfWmsAkq858mwIu'
    'ABSeEqK1SvT0tWjU0oehVr0RV4pEiyySA+nbgkX9In/z843lhha6BSUGbi2FtgwKOCLT4mYjXAtKSrLmJ0g8oSJ9QVxuoIqAXt1G'
    'QN0FOHUceYBwIhtJUWIeW1DGfPHgB6VyAS/spLTLevKuCwocrSmeyZrxvrPdkxFzlK2n8a6nYeTjMTidac8fQUlJ3cdFJyd/uERz'
    'cQMAeO1LOGKAQC+RxURmc4rnba9RlOpMJdXAdJCt7OjOCXJ4PnvU0AFaC83CJs7AwGdY4xIaI+5EepxXZSgCZdOyFtqnrAoK0v/Y'
    '0vOYJ8GWS6m73Rwrl+zWI7ttCNphuaGqDA8YdsLe8lyxFyw2xZH38o//dkFGHuLRmwaPnC32ZqvijdgArFiW4twaOYuNveJ7Bdd0'
    'cTHgmY0iGBwawUXWAzi6DRekXiuPoyE2qNaVEC+uOePkPgZVqXIaN4eYH2WeTQfT10wjwQBcUxncC+125gvEnJZJzhA/yMiAqEvh'
    'O/l6xNhVp9kQX5INb+o0FJh7FAMVrGvogWPn5naEWmn0P8L50BENCBt2PW8lntuJvHGEkcDJWYepRe7pUEaMLTqQHuv1u0qHyOeq'
    '5jUvbEHklCgXK64XORvQi388oK0/UFvmCVjm/D0wQuIlhvar+uzcwxJpTpvgoKfoSdZMTuIIhQvOftiF0agv/fhOfe612dBq/SFo'
    '33/91pRA1AADywt6p53hRfVo2xFgaifZJ1Fsu9udUwFY3OZkhcE47V1fpdcLR7UiTnmI5ZVlmQeMo1yMi5T70Z84DvH+9GFy0DzD'
    '4NeHntTpsN2/Iizzpts/riI+ox97sJwHGJSKHwKBTH0O9QzgqTPPMQTgaSLkBlwnFSTfK4GDoMqKpXJhvYaFtTShNwqNfL0OgLaW'
    'VyXYRsJ2MtPd9BogQCJOknZE9zJPiCuZbC5tkye1/CTtock+Eno5evyhtgDRwxqeXbdMbRb3oSWeRLT/XE+umWScvuq04cKnekv4'
    'BgYyAZV0e8i761LM+8/T/dNT2F50Vn46+l2NNs2oHwzSEWB6oLm5Zz0ees8MEXuL4i/MsfFzznuenfTPetQ8zQiwOw6MGtnFeMo4'
    'bCjcSJznL6JmYdKqLs2rm6WfMnf/XMJ4Gl+l8yM+7rCKh3/eOXy3ubT4DqmTJtAs7f6wOWif/pzjv4B44KX9cw5ki6vxYXP7Lyvb'
    'k2pd9YcfYeVilaG7peUNrHY+Gg3yVrN50u7B5px0+5ftUwxwDa//i2b6c/q52e0cc3vQ7HeNZ43v/3DXmH5t04WBP0IZyCHNLJmX'
    'mKcuaQsoG4x8EOZ8oGa2EC/HsxATvh92C7lMIgCBf5J1u0T9i5c9KsA4Gw4sN+LX7p8Mly6HqJSNz14jcJ2ZK8TRO0ScDGv2552q'
    '4+DwfCyrhj/nvEyZbFBGUgnhB2tS5Y41hanw9rs+uxFGbAUkENyiHLnu+zByHWKFiwFHChb6ak8Dbr0AlDYQ2p6DuHoAJlJG9HVw'
    'BQFjjVaEsHbBbZWTyb2Lfvuym8G+weuMdgB+HpDOuQyxpp7ZIykjrdXR1aG35yqAeuCjEjsyXWxn+QASswMbuE8WuAGYrrpXiGRW'
    'tYP0wpydZkj92VHj/XuSAj1BDv2GJ9k0feF9aysdhM4x/QEBHVPU7DrC3ZR5M5gAEL/d3d0CSiaono/S0WU+PioEJ+ZyS6yRzlMO'
    'qiKq1hahbmXfb79rnABNOsrYfw18K8rDtewIkKSCrTV/Tj+lQuMkY23E6TYRmuFzV5X+VBu86JW6RJCv5MSSm4YDMc0NVDw/nVC8'
    '8QM0kna5RfGZJehH8AZ/3LfSzvCEY+LgyFylAjYKW43hpGgrhABhDC5V8IBKs68M7RpVnyvlVJUdLvFwUPFhCEiXRHfWrZKNOquC'
    'EPPIarTRw+xT/6PaaJMZRJvjp22oguheyvQQFnqCERFTjFU78AXzECJS+LL3sQeUbSK6ncJBZ3h0p1kWR2JthqgyHkcufqm44VNh'
    'Gy/OIXRA/WtIkOFDe5ve4lV+KCOZsyE+gFCVGhFEHSm9rieNY2rOj6CTto2ATsJ0HR/3P9dVnMWENFsc74BV1Yy88X5MXmVzzJo0'
    '2phY3n8z0KpEdMQhLDQgZWEh4d9IReKXf2NcF+pcqzqj/qBY5fNsoZtZLFWF3qb8DKJyJbq0322hjWtu47rQxnmGajJ+I7QLgQSM'
    'AxeNhi3+9bkFw2nyBgLZ3bp2X1KDBteyakGzdZjBbDINy1gzRe29YEMU2eIvofg1Fr8uKY6B1SoAboDpjvtdo5iPznwX0Z1va0aY'
    'xwrwpDamfKDBGUDkheQKb2k9XBavj6lLtI3TBeCGG518tdODRavKyjrQrCE7spiK/Mm6Fns5aCc3xEUxEJ6ihQZnYpvEtpGyxh0S'
    'f1rhrMRre53wr4ayIwjEuFq375ENr8NKeF3DbdYVjCxPjqYTp7DmRoNPqAjQ3FrU2KyQLfsJxpyfJjHn5HmO8k9RY057LbdzuQfX'
    '04E5vLQkUDPQWnJRM6yrJkBgBQm8s2qAbBurYlTxAplKIRcWYfYZLo2xNpg5YJHoC9J5fmySZ22Us9D/hDHVv+YQp9S2DLeevDDa'
    'U61KEJFV1MZ4ISiuPTRByho3LOVCu4zPM601WHqAS3gUX+uPz7N4Oq7pX6XYsneQjP1+EKfNW+jlyXx/gHyQ/iBM/wOm0zkKc15i'
    'Dh+jMOuPjrJzmm2MeNTiwT3MuZ9n5hlBwKqYlDoO0pa4LpS4nqnDaINuPs/OW0xjUqihKZqBa65Q7noWm5vi6QSturXkKQSTnZ05'
    'gAMgm5bzptW5qmGNyl8ucudhE/CAS4zPmkFSwbmzcpf88kKkLsysv7yAy0CkMIRlNbIOGxEJSS3wbx4eY7l15Riru9ccgJvAKiF3'
    'VzUfYFIbDI4wypv4Wn+daLPImCG+bpyROfTgZvbM0R/m7lMTf/FCdM/MlKaS78ytyOnWbIPRnbPYMNvD6db4fCa4ZZJv+TKDv43Z'
    '7+lkVjtGWbYGqWrc3/o3Kpzb8rZefkdH2rb1fFJb47oNTS0RHVVU6u9e1JzbM6NvhNtMnMrwCQ8XIlCs5Bq3CkSjpvRy96h/fEXO'
    'fBuWC7YgjyMm+EsMc44vUfaFttSndAiQQch0sQRFQaKZZOwNZ0GBzJPe5QWNKHmdPIc3fLF1w9LDRyK22slhrS46yLwd9bGOMPsG'
    '8ODi16z0gITxu/5Z9WjTjQmlFGrWVo6i+ZixEpEo0EZH8cjrrMKTgZleJ7DmFLfFMgUTw75YAbqnk58bTiJtzwUKCZCboTjr9h3J'
    'LwLHmNQ7Uq1kZCDvcjdX1hca73Z215GQnDUQLu9EOD8ty30DkGgq9tXPGMWqm/bOiqUwlVRuhlkxE1NFgH/lnoXb74TU4zPZPztD'
    'h+XmVaSudYQFSV6QJz7TFLI+v5AwBi1mEW+FlJzUxBjcZ0P4HYnfgR75SCJZ2NcFh1Dgio3xwxDbRiq22ErSPXV3MtR8pRGwhj2J'
    'FQCL4auQBjCVhEONNo3Y4MX3tfBF6gIdRFh67oFuJML4oFvznmjuman5I3i9oQHJBYAz+rpE0SaA0afskESoeL8d5gN4iuUt1GpN'
    'LiHzUDz1HrYHHUh9OeMYFcT5KmUrxhmOryKLEC86NeWrI0a4nxqDLG+ur3w+yYjlAScTEIhILE9M6Qb6gFg8hrQVfpj7VJUblw89'
    'e7HBHRTr2pOLmO4so7JV107QGwLJX+XWkP6wkkmCvaF7oTWr2EJdimGfkvzNmnIGNptx3cLT6W7/anqANmQURnO28eIFQPWzYBad'
    'z1mXwu6qwdkrzUs8924v81fT5NLY6+TF4czMDP6/ZgrLvZ//C8zT5uLxoCrBQrFM5x5LpRZKng5p71Oa67ViTCorVa1wAQUH9C0T'
    'lkGeZJ1u1R9DwxCjUv7co2ZiFQKyVNnUEktE2iHpK6VVK8/aFWQept3BeWre0FedbheVPVbRvw0pKbRQqcCfN5FhQH51yYUtijq+'
    'OT09rcx5edtwmSEKxIeGmnPdn5FtVsAa150nVr2RkjLeljTuaLiWvwJ17fC9cnUOqBzRCOJGw/AyqJVvcbj76Uzp+3mMjHRIUITE'
    'GO7QowLAuHvWZw83zBWTVXn4dfLsLY8zXMu6PNblA16t4RIrZOt82EXYa2oUjSKrTZ8lw24rA8PZIqDNerIB3pkTpLQvB3HuKCll'
    'JKeo+dK91ro8/vrcwWMtFS85x2KP9fqYK65A5uH2OkoRTa5IWwRVO+BK6pBaG0uReyRp9STPEyg+qxNRHMVYxLcca+pf/4fnFVgV'
    'n4toecFlYrS8+Er6lA6tfpen24WaXRHlLVfKV/MyAZrkWjvvI4vBask4Yr60GGyg2OEsr1JKncWBpIcjwk8UaS0f/rj+7nBjx4g+'
    'W81mfnKeXQBQYdiWzxddNp+Bz+EZEoltOJlABmAMrotu89nMzPdNtJCzElVudHnJb3NwOexSC+2Tpomt1JxtzDYrno8lbP/Hi64N'
    'gMVuLpyt1MQ4HDEXKxs7C42qnqfXGjPJAn11GQOa10zs33ZqDXEmdkbnRGwl/GpQ6eiq9fTGlmUHHuWli40i0BQmsdw/YdePiz0x'
    'dKlqFW4Ahy7i3l1ndqxCqIppvnb/wS93z6EyUzf4KNLuFTA+Cz+A7tfAa6/68TUexS1W6IAWtHEvZCr7Xvoa9Yf04/gag0C7Zs5T'
    'gALxomBn1Mj7F5kdgdcTWw/SoJy1pon7Bxdme1f0m1xjnoNpYYlQA0qZO7DQb4h6F5BebElfq4WWu0rxatkEmTAWlSxm3NL+ZdwC'
    'm/e0W3/F5nGjNqxQ2LSXmFN1KwVjUHNVvB8vdho6+1IrApVs484oGlM1gGlGD6+7eQ/468mW3fffIZHtqRbRbNqb8Z7ORVvpmpqR'
    'NawuL66sgyPr71Y74MDcqNh5xYqhLdyJKD3B/ek8eCjj/FyfUN+BifP3EBw4ZMLFwDPC5Stx9UPly7ycCI1KHYsu9z2EchQc2nhJ'
    'GPXf42fRe0UuNOr9TpWuiQGjdwsjo40sWse3gRZDJbWiLWGSAPmmebSEUt9lp6NWgfVAoyOuNjyg7IfYJXj1OYYDl3GOATzDByr3'
    'Br0VvqHQg63kMfFsG8cuzZYlQZotAB91jy1tdGYFDdKSky5oFZDq3v7g5t34gP/APxvjpPHN7yv/+Pv/ebQ/3TzAeO0vxrXWfj5V'
    'bUwBbr1U502aZM8dgJ43NndXbnfXdt+t3O6831rZvl1a3F6m8NIUZ9rGlbZ+F7iBPSdnUeovzpuM2Z5J8V7Dlura1Rgq9IrRMS4r'
    'eqjU7sa85pRg5Y/f15OiS7Ek8CmWFJyKbSyur7RcaOccXggn6HK5AU8arRoycYqFQK0yw2dfNEPPTu7fbIJFn+J4e4lnG2PlpYLk'
    '4MlWV6M4CGVz5io7NiDDrA+d0Xm1Uq3UjPOYBjwmJbVWQSgyffg+RgPHL2F/Dgxq9g5U2fkATh5muuZdjTua5rXSVe2O3FFTeUKl'
    'UaHHCfgPD9VbOF0J/vjz+/WtxEZxp18UyZ1+rb4zabtr6yv048PaljuNUtQezmR3s4VnNnmzuPQX+rA/8BQn0Pnaxu3m+93aXqtx'
    'sMCJu5uY/uYdlLz98HZtd6XWWrhd217bUcVbCzb0MWF/tRhqkncsB7twcQEd4zsVRH1UPYVZQXfNnxaXdhHXLbT21v7648HU7eYG'
    'oLQPm7e7b7dXVm5XN99v366uwartt6dq+8cl80EnQndNhHzqxoffvTyzhrm45T/RIu7uNxZuV36kP/y135RP/rPf5OTafu6NS7e0'
    's7SysQIThOGXjp6HFnpJossUQ7PRzW0OnhH45VPNmqIpv7cFXNp3MzIQyLLXs/5NEd7kw6cJ3BWz+3YlWdlYvoX/J5urt0ubG7tr'
    'G+9Xlmslcyk9oXse1g8QxYHbDUbS6ag6PYs0OjRbfogV0bLyyeo44YmV5m9tn7eCTW65iVt3Am4DEL8NQPaWtucWgaRmI4lfdzNP'
    '2ulfKv6InCWnimbnWVzd50rhuvoyefmQy+QIKVxlj8xU3T/+/q9PbxyVN/7H3/9n48jIPNBJghqyuWg80/M7Iml3JY42TagWlYvy'
    'CuCj+R2bAsCrgqy/kHviooAScXuY9XK49rDwCok32UHe4zYkLDT+vPNfOoM7JKS0CmKxFxeNMkz90hlYXiW2zo03UPFwESfAg1QV'
    'nMswCcPI4Rer0BBzotiI3UpfjVMoOa6vkxczUQEsDp4GbXjmxudinoz6/eQi7V0n3P6obwQseXqada+9+VihhGjEmGFVaWualiHv'
    '+ch87NUqc29JfLfAxyWNeHlz6ce4h8s965dFtOUA9nL+jcJM/DVJedobVoMAqmo1oPhkBfPjHnh2C2EN/RBw9aATdMGdk3j1zpoH'
    '2rGonZpTjnBTdGlmqhoGkm+T2Zln38kfQ53fAyo6DA9d5GqWgcJYu8rNrYq08qRaBJgfyZiPyxf8rPrbONHZqmlsotPVe8E/BkGH'
    '2bbTC0DTbQ+uaJWRQ1fQelP5HDe5UMLSDLnzOevVyycuhYbh+EIkRT6rbbeOhBLF/HVhIGgunt8YbzhraGricU1tDdPaWjsUqSI+'
    'NT7oo4OR6lhO+UZVq7PWrqllJvUsSa8HPFzpCloDnKAIL7FeDKaztTW8a1CDraE3Jr0YJhZsvAFoHOp3MHhxvD4yGLbTq+iKctu0'
    'pulQnCpOKIU8iEpshovOI6Fff9KYfz6hIZtFjPFfYpsjMO5vj9LvJ35K86fpBSBLn2qiRhZCaeP6yT5zRbujDCZZD+JojS0Gwiep'
    'RRzC2HRG9gYp+gcQUyceP1Ot/PCFXUqTJeKLqpKn1I371Zrls4r7zwXlpZenMH4Ud0e+Z31/i2bCrP2Gp3QHdX6kNPGgnBWZZ87k'
    'yLf+aRHUFZbF01IJlAgH8ROmXSP7J2wisim2Q/A6kNDlCmY9xh8R1eWndRA5qLpmyTnVzU44qEExfVIL94PhtpuTdOZOUs35I9IK'
    'wCQz8U6UN2Z1pIL0lpxe7soaSJBvFM+qTiGQ6n02I0AeFgNLRwEnNIpcSM+nZKsBkBXDtFJTYg/F0zYyZ4L7KeV4nhVcshPFUucT'
    'cZ7mW6ZtfRA4F9mtS2hxblzlC5OrP0q7Qbqo8aVdFo0HWie7wyz7QHn6DOBds0oSs8bO280PhyvvVtZXNnZrrif25SbNNk5YDwmr'
    'iU7yOdLD7GctuLcpdtN84N9aI/Ge9Xc9qhT16IyoOh6pwunD8aLyk5S1mJUJl1umqXlu0eh8Bb2RByXuix/TEQ/4rCaIvqWK5fCq'
    'YIdy/RwOw0KjWlEaXuKRFvrAsDUhgEE6ANixBama2vWSYY+VHzu3iim04a2HZ6kQqXE89BZeg7+STFdG7C+Sqgw4pEkAtail4iZL'
    'PXnjSNwwokNHS7ZtsZ637U7uxgdMZOwgVFY9Z3++mEcRciF+M2i/ILsxAUB5MtZLtTMZu5yZSWes1di9TMlG6sL3BGKeaZUzrqII'
    '4EYIU1UwDcDkIOX1vAb3b5PG9zVW+ql7hFDdIdZ6cqwlQNGruV4IEHrnDe7FYJxUw+2miwiqNzzAolbHJ4JuCw+pjb5T6aE9vEpz'
    'Uc/piKq0987yHlaeTJmktsybUdvb2PupcQBXH8W79j3XUrviV9W1eYeg1tzxd6hT+GRdKP6ORJ8oE/mGI3BckK4XpjC2sNZFhR0+'
    'XKPZPVbX8ynY/9hKWM1N2GZqfWzTFMulVbxgVTCltx0sEWoPcDyTCWtFzEWog9HlksqbS7gEp2HsxMVhjlnFBeiJc/Fwirvs/HY5'
    'yz+O+oOdbPgJlaMUT69o7HC4s3qIvk9Knv/sLDFpc4voNRebNCwnGHSPna1VrAfs404vJTYXoy6ioDFdPJmQMrT8fpXQ0KzisyTD'
    'EZv5/JJYcrw50uSUkY2TBhRiFrRNR51Dbia/PE7JDpHbqdv2THMBI2YoBvKW25WfLg46q2T6X2mmg06TV3ZaWMI8mItsdN5HLzlb'
    'mzu7lTpFDsyGOfJrTaSMaXJp3PKfQz/n6P5RXCsf99vXrdBF3I092i12QdYjF9ji76WVHI/6aZXXoiaefi4yICbXofM/wvxm6iGH'
    '2MywgZ1XozxgVupD4Pm3891GiYC1iHVs5eN2yvbtpD21nfeBlEnSZL1zMuznfSDT6UxjG+iZhtoSx2115udqP3lm450lgGp7myMt'
    '+kiCvWu8DL1rEKQJ++o9nPWXbPnK8EPdEwi+uUSnU1VfXwdhFP99Z1iOzwosx/sxG4nROITCKWuEQjvrbwzXkUyEGhVFNLNCpxuJ'
    'rPyEhQ/9bIjHOnNOJssNuKnAx0HCGnwr2n7fecqIoyJXY+6OkdwP9wVmJT5Z8OsbVoHEubGoyw/JYpeEeFPHhAxGNnKcOfeXlYLh'
    'IMdImSgD8u2zpW+OWAAPB/1NBtpKWuS6+oJICNqfsA1lqJTqWqZrp/JHz/q6vkSliE1hrTuBrzLix1nfe4O27v4TI9/TvviTircB'
    'FSPIo6sZclnIx7vES6z8adtr205JUrRoQxgWRneZG/zQ+SUdto2cDtdKFk85G0TcZFW4Gz4lYvxdO61uX86YNxIZ+TER1QJLeIEe'
    'KRwZd66h8CO1KtjlNIUdEB9xntPDOl1BNetuI7hmQsXsyzxb7wPiWFzjDid6c3ILZ+3M1P2omqKi8IBdK+8tSkFNrkIDJHZh+1Rp'
    '+Ydec8kbybvOscMhynPU3CNt0lER/ylYACa6f/nsD7PP/VOnrhHbYPF+8Zs9Qg+oaOhpV2ecVJ/eVFUVdQE16cppjPqrnc9ZuzpT'
    'Gyd/eVMzBiQ8V2vDRTPDh6p1KXlDvgxa3kBDIxZhvRhD1/lEm6sEY6c0HLw1ZzlS09M2hi/ZQ4M2NxOtYc3JgmvJtwJUtOiAozDi'
    '31fzdnz4re3s7rJm6wWShk+DSbZryWzRJsvGa1NGRVB31/GXoLpoZ6ynw49Ze8kQg3Q0Ci1iC+GsE9NPg+3gjZDLqMkGl7FoJBD6'
    'sh8lriHsFZF3fsmMzRd6MGadW1TzQES89/yAXqVl2TOcPfssbNfwSswEWGYHdCc1gB5WkIFyoHnC+t4iByy4El5xYWLQ92p60ele'
    '65QPZFZ0EBrtC7PltlLwv4U8D1F8wZ+3x3AtfbyFV8Gn69t2dtG5zeGfvenkYAGzbZAkGZ1qzu6dcF6MKqRsATu2UZ+f5cOt43cH'
    '6OUG4NAYR02HJV4ciP8Lqeuc89SdfxvezrpZQOb2KK81YaOzB+LGBs5PXXmuwYEUndao4WkfX+a48uTtWuy5VbHusGedQw7FCBIs'
    'ENSvaWs6D4kYh9tsrAynOWlaTICGyOhhoGCKtyVmeL2xsaf3zarohB1FuH64l2+uxcIk8Aljpx6eTFeJhInWesQQH1VV4EwXqLGr'
    'JJjiZB146zDDE8SwfZlB2crm6Ea84VsMXU+qh1pV3uqdGzU8c4y0OfHrwriVXbAM/BW8adQLhqmHHSLZSNO1fapVadWALasokNpz'
    'kR1iQODy7yDLVdUL8KixYXR3ecGFRLS2unTcrvo2QI/dWCg0ltu0GtKOQItVTe+Bb3A3f3QpFT46/lkW4XQp2Mn8GhYnEj2VkGTZ'
    'RS4xnxs8UkFHpTTAixc+EWDU9T5cuPfJBzRTuYBrs2parbsT7oCLbEUXixunoujZxh1c2QnYXuwYWsmTpzeuzvgJEngzs98hAu8M'
    'BnAeQyvdq4v3YiLiqsUMRZLSwVoooxvdIB0UVnbwtri97dDxv71Vh9/vwPCMWDXVjOj3v1e3dsNcAbe3eEbnk5nG7Is5hYTtoiye'
    '4gPoyi4NzRz31xt/GdoMiLsPYvvr1SV1AJcLaON7Qz80m8liL+1eA32E3BFmwRIZ9/+z927LbSRZguC7viLEUjUQKQC8iJIoUCQX'
    'IqEUJymCA4BSZpMsKgAESZRAAI0ARLEFjpWtrbXt7JqtjU1379qarVm/7PTz7tM87No+9KfkD+x8wpyLX457BEAoK6s7s3rqIiIi'
    '3I+7Hz9+/Pjxc4ncbi2PgPg4kD77C5eC9yPoy94kNvlhTOEkGAC00Q3GGuz2L9AHCvqdsBMN54PA8MpX3U4cLFnfvaWSNKXAZl4L'
    'X0MXHQu4GzqRx+taZ6EI3mQGzrsNiU3ZAQLspylyEguYpa794i9Yg06cTwli5mJ9tuYuVlbZaxJ2erEzAyWED+s6GZTdcs699ijG'
    'y9COhn8OL3axMDoN47u8aH8WamDGL7sUaU3h9i2/2AdBtJd3mkiDMLhSlfT6J9OfR18UbDI24BLOIQzNpkUpY0X9vVOq07sUhbRt'
    'tlNm1nQ8X3GnAxnDgdYnYViCocGUM1BXSrg48C91oBa9yxuABY3HNI4M5zVgiEcADKW8MqnlNG+Zr+myEWmYZN6QWv71YIDkozpb'
    '8GnNnEyLlI7FbA72klLuvE4qMH+qdUcMkzuQmpmZR1mzMggfjgOsUIapW7+5mi+RaqB4fqavezflXWbTpjVMqeRwBlTMelOMMh/c'
    'x0q06Zhz4xU6ffc+Zl7LCj9szRcZg+Rx3KOkbCKxlk6nhSow8Vo5msieEcjQwyW8UsljJy2+gMEIIM9W3Ovxu5+iBbVdT2lnOFsn'
    '6mcy03q6GzKpbmbn8bz7rfBHMFqb+WpXQVEFIWkUUtpSnZeFdaZyDbifWH3qSqdbSj7FkGEyglleBEgLKZYYvLWpNduj2XC+6EDD'
    'OZmgIHheWimtqLBdE9yPciq6WE4FIaj1TVQYx3jyLnsxvjB8EenGVwA6+rsGGxGgsTcVCir7yOPXnuVmHjhfPAnnBTHXriP2xHFN'
    'rbMgY1irpa45vFUPwdf+cwtOlLDAZcK6zKYoYAbNI42oRyq4G2UcctWXduHYANc0FDgoyJY9sJV9nU0HVcu6gokk/Rheq110gnE4'
    'VLo/o5jOpcJYG1Fwv4jbU6Jznqir7KK5yqb6CSp8ObwKmgGRcoNNqjQcu9qWGUsctw6zAI7JyUXd2avdsIupMFL4vWcTk7MrV4Om'
    'S5+mVs3tZBID26bbYJ26FfflAVGOVZqraCiZ1xAOZdFdBEZgXHvqXBLgHUEoMqnC407JGk6J0yMZgGYdSVNraT91Ds1IDDXzxPrk'
    'qUja5OwopoFqvV6rmysLTVL3NOJddNhrDnElnBVICCilHgMq0eYsHhXNpR4q05a76DbBmQQSZaz4MY6HxEmQ9K5Q1lLxhzS0qNf9'
    'FJPqGov0KRAQd1Gfq4WVAdBBktiMlCKoESBjZ15YJLq0UZccTBeNMUcJ4PsOEbdh3u2fsBvQ0RnSqddn5becEzA1HUghyQi4KvdP'
    '6XpC4VMavckl9oeA6DZ0/Z/udspxOYRFpBq98XGc3yZ5FO8flpVvce2YGkOXZHRC1o7K9GAcnvHJuBfPav8ToO8juorPbb5ZrTSq'
    'deVhGqin3doBPB5VD+m9fWpWvqU3+i/UQDvd+7tSaY/nd6Oy20Tn6Vn+x43976eN6jvoAnoi67ahEtRhB+bFaoY79/V1NLiGU+Xc'
    '7rLTNHtMU/vfnJRLxbMd+KEdjq1HNbTqelVDH+7pArnAvgP5pTXpsSXVbLxVD5s4e9/vN+Gf6vFhMzxtTU9b8OX4qAHTVJ3u1d4f'
    '8i/6Nziovm6qn/X9b980rV/3vO68HgH7eksxaeb2Z69eeVtp7jeCo2q9UTusVKe7byp1wBg8TncrjSbOm3jVqDab+4ffsrd+Bab1'
    '6KCyW71vktoT2j7pRmw0n7B2j+vNyv7hVP2FtfVoSp77xR1YatMDRAH57R8fEarC+9q+xMzA3XYDDxpzml6AEiyV3jsH7UFv0N/T'
    'ISg0/0s1elIp/uUZ/rNSfBGUMKxJUcU0wVVy2rhnok2QKd3SUdQdWQ6umiO2LZX+Xspj62n+QPm/n8iIHPc4n4vQNdoBPdVR2DAT'
    'EL3o8DF/9oGZ7VcbAUdpqR7tN2oYvkE+cXSAKbIx/hBmI0law1030H8JTbjFvvJN8AzT5gmu/02wpu+YMNL7emEWhmVCwU8atuDf'
    '3wR4WaW4KLfjogDeEa4fB/m8qAe7qqoEv5waaPzjdv4JZaNVUEyfn8zvM4kL8EX32TJP7rLPyb4Jnuq3kqF8E7xQDXsLm8fqrjgP'
    'qxsFb3HAd+obpvamKyUQqBKuiknx4NByjeYofRT7BmM6SZAUk5SCXbTc6ePkRb0AQw4w4TOwZAw9vsRUqJPxDV5fojh2HUz6PYxm'
    'DH2coHDD4QsoUFusQxCghNZLBhxeuD8uaX9Xgf/tLRgVhn2wGMQnH3/mncQeJcd08BY6k0L+OOwDId7K2M/2fdGjijUzzawhwLsn'
    'XAA5vEXuY+pU1kzxitCmnZqIt00hjI+hX27Z9jBiowU8/pTbFGBVhU1jaW+7aQC7ALCAA8LUkLlLyS3BibZfMJ17LHDx2A5MLFBY'
    '3x/pkH5ivprqApNnpQRtP/JRoUU8slWMJJBJH0j6GM1FGN4JB+pakS7gGHuUY2roAe0Eef2zaGBgkG79tiwhOKmHVAlaZjt29bx4'
    'UZCX4OvO0nqyYWcZGETpKd4n2359E6y+CJljOO1O9OlW9PwlLHwYX7r38OUJJycxnX0ZPF9LmefzJMsQHAXbkE7kDngnM2ycmXLg'
    'zE/ZnaOymGdlka2XK4UCsYugIFl6QXDlguKtBcv1Cj7DK6R4XcFjcT73ujNG/oxMzkuqHeHO69V3+9X35yg+wI4FYvkWIUuczUYU'
    'n9xTLKA5uokHkji36PLAxnUpy7WrOTIGo9ZSNHQOdMpNyAkfJ6OrkIhgX5BKTxWWr1FLB3TI3WBjdrFqmvXKYWO/uV87BDzoIJl/'
    '0uhQIBwsHh+qVP7q+FAidCfJi2JcmUfR5JvTZfjHPZCql6rC/unyTpXPp48l/N3j6jlUqAIGDf748HKah7/voEoN6+M/Df1jl46i'
    'tcPmCYXIO9vZm9ZevwYpNjh6g6IstFlTP1/vH4BAX92bHtWrxZ2DyhGOvAGnAJDuw9MwfAwtOQOGAwD25KDyqnogxn1UORRYmh4d'
    'w4SJZ6CB3e8AJJ47m9Pdg1qjCl+L0yDcAQG+cvjtARyhD6dHtXfQOZD+YPah+3T6YVGQj6zNBp0h9bcqnIdeHew33hjI7/dhHulX'
    'BepVDtTv+u4bENehxeB1rYZVwx04S9WAItTzdP8t/MunUjxw7hClAfi3R/pl6Rt4e9oBuXwNxPLOl7U7+MI/Qvtrx0Z7AuJ5W6vD'
    'wYGjQeHkOpg8BDRikDqBRTyitqZ8BmlN+VQPP8xJHl9WvoV/+SQNP/YqPzyaHuJp6BG2dgiYeDTFczP9OKjA5D7SXaodNx6pk9MO'
    'QlVHK4TWpHbwPEp/8ER62godQm/Wj3ebx/XKwXnzh6NqQ9jjnKjrm4IMkVag+GL0b5EcBOE38MxOEUM1Y9HoEv5NKAh8G+uCXDfO'
    'nQm+MRwkOv655ld+NEt8v1My4S41q7Nv1DaXn1Hxs63xWd00ZHSgeQUb1BWbC35FT1bXVgDmqthigS/3ervRMAm2tGNyZphSpWfj'
    'Io6OzfWfx50p8YJlUojM5cuJihgtnWl0DRs7Z0VHQKMjYHaY0zt5fo9fcV4S0/vZXTX3mj4LK3jj0bgxkRt9LOe9/WZH5n1DwfTF'
    'U31kVWHMZLyuaazgTl+jwjfYG0UX8BsNP2A/N3adUrcpm+JQYGpoTn8rtHXTwUxixGOQDvQMNDkgdydx4yoa0l6eSSAqLYyaCMdT'
    'nXyV4KXNH0fp4+Sr7WB9A9/pTYv7hiVE+D1nuxYl8Fvm2MxXwdDEF5NIWbj2siPZ74hWZwV1hW1n4jWwfFIubD7cOdOqnrnwaeBZ'
    'kf+2g+dZdXQyKr1GbbNpSPGneHSbxzzDnXTEYTtXdGLDQvaO/3cnPOqzx1P1iywBLie0KtyYpMFDAoFxRVm7ohYsbRWdeNqJe9NO'
    'd9qJpp3JtBdNgdY/Rf3pp0F/2ur2p1HPxrBFQCHjkFqd3FnkjmI33IwkyMYwjttXu1G/0+3wrYJSI0W93uBGsTK+nprPy5g/pi8N'
    'vCjMaepkN/dsujTfnMWoVEAzyALGf1L65vTMURdSs94GR0aeqtscUHEmzVhkkO29oSADe+xELHu+4uE5tnEYFXr9wIU6JKHAslDf'
    'UXEbWVGK5taaAOR2n7up8Hr6bKHv9J0Qiumu6MgJIoyiew685/BTMESugi4GTtRFcdV/R/q75eWg+hnECBPCF5j48GoEizKxSp0u'
    'Baihu7RSQCH2SHeDZlCoC8UJKA76vVuGh/fJlJlN3SHfXKHrOa1qES8oGo26n1D/NLYXzBRohi/wS3TYpTNPKp3i/IWw2DqwOyJV'
    '8pw4sOisJWEvazVlKbJyBLQAtQi5Oqd4SUjdZrIV2HIK1eZyVwTeyFqowJ4sYT4Upj0zu6Rkx1Rv4JBSwju8EqsBi1fK21cEck53'
    'KYMRsCZbxFG1Wm1Pia3X+ayeKtsl6Opzt6ttoIwRBhwYDToTPtAPRuT80u1P+H7XREa1vVZO31K6UkmR2re+s8F8OmP/Hys9WCIL'
    's8Laq5SwSoawZTND3ItO2byieee1zBFLzgurJuYpL7cKgkF9KitjY7Scvoox8SO+vBgg+wQ0tm6DKHCuGRCNCW1BuGQZGNS4JqdI'
    'WvGYY4fdqWGVclH0nhxisKIOBQ9KaLVjB2CMcT8hHT80wtAmSXwx6ZmgDgld2KORMBRVUTiWkVNoe4CkJGMjdG2euK5KDKdnSsdG'
    '6LpZ4KwXMFntUNlUQgJ/5dO2cmLoT1zLCLrOJGa1IWVThiLQ2E9J4PeMbnUcH0c0xz7MLrl25oNrTIbEZVmWCDh8MmXz6NOBw9xA'
    'mWFZYdQr4d5B2WI+JG1lCI2kZBgq66U0d+Bm9nfnvl5AUxYtxHLS0yWmyJRV85TZU1OoQDFO5CaRgVi8UJgzkOz5ppwlA3LxVKdd'
    'JrkCjdr7QphzalNQtDfmzIblH7LliQ6a7b3SpbbNx8fpczZ3QTY00it6K4P33MfJNGPaduOoGXYAQP0zavpMKLZs16D/djggceGW'
    '0WClv3S3eDk+ZIUD+R/aZ3wU85u3qIUyZvh4IWi6jYKl07ryK8+81J2x3p3bBtvmTvDiGepNnMZML+Arml1vPFOY8DfK7FQVJoO0'
    'aCWHjp3FhM+8apOQ+wFe0hUNp9cLqZQz1ojlTBAJUz7DYHgoOphkELgjSGnHYLEkLa/9dX8vV1HLNOXExkVnYnodcbm+6UsdDFHe'
    'wfuA4CvFpGfhoqeHCtubkeEDMxeImyyRaT53c/jawsjwGVeGTCWKyCFmIEaP8r7B0aw6vXdlLSWM7KpVEFxPeuNuUWiLaBB4qIBz'
    'grLyE8cKDZ5Lq8vlYdQmmZTpjY4JhsgoCWMpeG2ECSND0I32NfmFoyzBsEY65EM7ckxahyq7WDvq85mmhSMNGP+2QyV14cvZDRsc'
    'uF9EPcBvGB9PWKPoTyJYKgkmgwu9q0uT0dmcxUyu3zZW2cxs1eNFd7NaySBG2YbP0zIgGNpy8/B6YLw+UseFE/4CPRXrwUVD5gJR'
    'p/wZ3ALreVuv21+6jqRUvhlbt+uiiCPzS4nBpkrbDV00ITZw67CTFz0VBcTbbQkja593RxUa0CjS6Y4L0MajUX8rigbIsXGGKKEh'
    'e6PtXl/HQB/juHdLjo+7PPkOLdhlInxK9JLelUe8reChvXwQQV5J7JEw1YjMaOG7nE473hmz73eKE+kJcSFrXBiEJ6vb6ZCps0UC'
    'NDbKZwHfCTbW4NvzFeFL4AsFmdmdCsJfwZELTExBYEXXlLlBZVE1vN/wWan6yQl4JBxYOHodOxsI8/xC0JooHQ9fsl9FCcfjgiLc'
    'LTOckvSXmMM2fMZhHRz0lM1UONqj2wwek/6SSiY0kycz+52xE+idUgSio33ASwC4UP6S2fYK8xQdymRxpprDUy7JXSit6FCxg+dr'
    '3hbSenDEovTRo69zs3p6D3vlZozoU/aX3qCy77c0swhtqkZtreHlwcm0y7jb/GmKyK/JfzhEyWUwSZqsi5bmoEVjDpqOiUtJlNJV'
    'HmdWYS9LwZc21mScPLqiA3JQYchJvAeOisZRKJ7pLL5CTkM/KOXw01asY6YI4Wsw+Rrhj0t3FbrDefEiFV95+TQ5Kf74h7/98Q9/'
    'd3aafING2pUf+Kp/uld5fzjdO258J672+bI/lb3MxdqG08wX9+uz9U2BS1Kia6VrZxBz5NAJBXNsOxaX9iCFxpeASDdS34LCI+e7'
    'WsjiWJNOCovrKSymlywjxqoEfBStz0XRikTR4cDuQuiiMxJHMCIx2MCTLkbW8E5h92Nohtg6NyGY3GQFtuT6TGFsbd5on26kCMKM'
    'F7fI/sAMW+6ouNMsMka3944cbPuw/LvTfOmbU9e8H4WRDdjen625vsyLX0KFzsBU6BOeMRK5cOPvfoxTCmkUFFQQXWgIHfUoTkoL'
    '5uRjPE40F5k9aCdVYvaI2TbOGKst4kykiFqjZePnQQsMdIQBn4oU7Funs7/GbNaxPoCOIoyuwUr4SNwb3Y8JcWJSG42yQclIy/ds'
    'JYP9os3Z/mHadEuZe3kWXsagyzXiUnZbc5nzfJawKhdJ4wr3l6jXK7ajYRctlh2caYZasByhgJgs0E2Hm1NPLCGzM/lmR9JABkMd'
    'Wd1QmDpYOp89U3JjPLy6suKYFs9tQB6nfLgAS15fu43DJr8ijB0IeY+3gg9BzfqaM+JE7r7g0RcHyt1vSx/kodwxPE7lRHaEJSOj'
    'uxff/tW3IdiCFOpTR5c/+iY8fRcuPtg7cXOE0FKmI5SjNymG8mC3TusTYQRytsVmqkhJp1kX1+ouyIiWrjQ5ANaABlVKhjM3MFkC'
    'pBI5ucxCEjhFgFAeAlvsZJDBAXy/x5T0I+6FAmF+mBa2CJp1k5wPCG0Xs0EoD0fbNXY6PL1R3o/WJ9OkcJ3nAUm+j3O7Ys0rU+xW'
    'oo9cLHwESofI+xrJGq+sDz9E1lYfmq9iIFtF4wFm0nxLgGgInRcgAQ3i4J3uXmCJCxgJRtgBoCerZ3eB/r12dvchI32Ik252HhZk'
    'xtnA1Z9n72r5ma6e7q6N2i67A9px6I3RWg49CVOdykwVfOfcYdjzslyz/vagzSQt50DTLncJSgWdMVjWMzYVeJzeO2qTgAU7mGmw'
    'xCZL/ndlsjSDY5vhZnHsctYYQWR6jmotrx3nDI5Byp6GMxh+JkyO8qpSUyzK5bNgCX3WTvBB2JxEqMfSgWbMBKHqbAzH3U/dhKiw'
    'rCmEGMCdNKGi+4dR6cMDR1+mTKes+CI842gPQEkGx49atC4GD8YgCeqATbZiJRMb5i5jd0Y0Z25f90XYFvojFH3gGPJaO5Dh95IX'
    'CmenZP2ZACeIiXx2OYVB3JHIRU76e7H2ywQBud9Jh5pQmi+ESKovCzBKMM6DgDhfkybbvxe2DvmlYbtY2pknIDjdKrg1MWSb812Y'
    'g2sRlqIWw2LVDgFOV7SDr5YwZqsCHEHEqKdmRZcIz6QLtPLqdlvOVLvlvwTiFboqZcbvy9YBZbjL6dn6+VuX3EiwHOpEKtqHiv4+'
    'joflYFVlw1GZSijvY95LWuL0NQyZvOZVoFWomOCFiojlUIo406D6l6akkMYTQwBiHA0+xZR1iquUjSLYgiEcshZ3OzhhJewXU1dn'
    '/qECd2e6c/ozOx5bsNwjAqlxzQGmaSqyAItAzlZbahvS7NyGkNNNpQY9r1UksrJLc6rpjJZdw2GtnhN5+mxqzle3+518TqXC4b5q'
    'I0qbZVi9CDUoJ0eeYq0iqQIxHpWcAIPuqKwKCG1mD4BUdfM3xNcxKTQpXw+6ybgUdaAMSeVKb4752/ydwNstZhQSe0SiloW7TkwS'
    'G/osrwx0TPDO7TxkiqFgUTeNcjyk7HAAuIQP4tOkRfHbiE3m9oymjBNgqf0HddY24inq8uikO7oWukMyZ5SfiKT11NEXNTd289O6'
    '79zZopOku4vnM4cYzDhOaLBFZRW4CMyhCmWVgvmhgaAefUGId2h5sP5hUZhorwnwOAQ8Cjytbq87vqVJwLnA2Ku49191OyDGkSxE'
    'pXrxwvSK0koaDRr6OkJXUbBUpjayR8JKNju27oqfnPcTnYyZXmiZeTlVnHO08M1++FDUmS31pDPB4AhGA/RVkqLRh5ed7if2lNpa'
    'uhx1O0U4Jk+u++XV5eLq5hBWJ5BWeXV9+HmzNRjBqiuvDj8HyQAz1n+KRvliMaIA4OprcQS0OEnKG1geJuiS1Ehl9JYeFa+7n/MY'
    'wWF02SrIusHGbwsiclu4ubStRMiXbDGs+9fpJuQGTqY1m2yGDytxPB5cl7GH1EyZQZPJ/yrCeo+2wbSVA32pVddlDf3Oy2VuwTY4'
    'jPqLNLe6ltXek3ATA4YVMRB/eRUwBc2rVGw2OxCeKsawpdKN86MvcdJ+M77u5cW0iiiNxHEx4iJGmFVHknHvthSYzFqKgSQDgqfz'
    'Dtm0RBN0lMBP7cEIj4n6Rhs5juYOJcADDNxgQdCERgLSxiYRCOxKQwyjrCglKbNhYP5JYfUCCOEyGtL0m0kEeD0aioJoiGptNlHx'
    'a5+qniPOJ6MEkD4cdGFBjqCVl93+cMITvLWEBQdLxCmhIVzJRcZPsX016LbjJfar21pCWX+JGA9incvAOuUzwA6IpXH7Y9zJlXO5'
    'u21Nhtuv4aOhmJfJNRyU5tEK0mSwAv9dW2NKMDdlAAQrb79cJsz8ojE1/pSFJzhszsJS890fgaOmOb2qpfprQhWOLgtZdPqeha4j'
    'poefTFR0a0AH9PyrV7vB8XfhDJS9XIZlzQ/88wNsVx8YjdvZYsnLBKajjSzLHTggaEApCRZcTgxGDx2Xkbg2frnMsHyYcwjPhWdp'
    'ZhaoeybGBZeJUQ13mcsa3CqVIoqDINL349Gb5tsDFGyIh5KYu7XUTghvRWSfhi1q5Y3al3XsVWc+KMa9UUQpolRj0qPJFgRc9dXK'
    '3W+XAqAmTPPQ8eni0RfMBdi4iuPxPjagRKAiS4GFXJP/knxiE6OKxp1Ubzl07kcRqEDmjXf3NBJNxlcD9Mp6b0Lv66b4k7oruA8O'
    'Oul2AAya3HcC9LtgIPS+1l8QSgedwwEKOYkHbJRLmjQFjb4vCAvtvzgGwq7+xUDUh1UHjlqRHLPVKJeN+Lhmcqr6hMbzIM7MSluM'
    'ot1QMxJPKMmSW1zxhjfwY5BT2h/NAYO9rNB4GcWYYTwYAinQhT+eHIMfBhNrpayFjcg7v6Rz2r1cHm7LxSLk7x4cEJe2NaF7egE2'
    'yprlfc2HbYWdtLbBWm95PtcfZnRlNLjxdgXi5q3B5yVKqFbEstjDIr3H5Uldu0O2Qwd53QlvH3Bg4mT48HjbseDM8teCI0GnsdxB'
    'F6UAmzXPS9sGC0roE6SHilmTn/zO7hI5iZVkcok+fKg6LIIoOL5d2j4cuCYuKpmzVs5b2rgcBHgsYJ+8q6h/yZbuSoa1XpNxiRvP'
    'zVoQT+5ZEErb8/MvBlLF0EJQdiCRewzHeHSK9Pu3RkNDFTC1DibbwdRwXAYE+YXJX+ivaMpnkr7yJPCJn/VhNuEUV/85yZ8ddTPo'
    'n4H8lBXAIO9dAqoBMg5abBEQNgIFEg0S7n7W1eBqZvzVoLQ09rwGa2OEjqgYp51y3XRhMQzjfpKxDKQaIWJXKbqDIO2SjsRjnA8z'
    'HZ8LvuVYVuQe/2rxvlg+sBZipWaauSrTitGfcYE2r2JAjzH2dHAe3HShFUTWSAhUFDuSNGmAiu6IlQQ/fYOar/adu0h9XbK/TEkn'
    '9BWqYtdhQSWWyLpacHMwLsAFHF1RShVw3e1TbMa1leHnQunZ04tRGOh3L/DdagnfbZJFWZHThwEGRuPZ6gJXARENSdMjSGRlBoks'
    'bVfFtaQ+yRBnUUpxRSpF5jxqm1Y8ZptympnFxUHL6TpoG9Djni4efcEvktMRxK0t/OOfLizTQqt/jqXTOMGSZ8qjM0Zeo84bHxwG'
    '5J09fnaE6RtIoqlZbNlHHnzxkbcAg6YD6qMvyr5MKUCdI0vopEoJ/uk/C12ZupcwoZmOOHJ/26xm2JtVB0uMudkH4j+W1ad17cx6'
    'KIkeBiMRSjkTvAKFBxQFbh0G71xywBT1OF6/vsGIhz/5jsNGrWEpSt9SZOmmNb2aC/aFFM4PtJWCUaz/1SQe3TYIGGYaJHI6ma1E'
    'OStrqSDcKREBPdBmCfN19QqOqSbcqN2hWJMXkTtC6VFRJ1EImu/IEhNVMnofUAIpbgQ5kX1bcEsREOhO3cJaLQOiz+nEpihissHP'
    'vpsXBQsO4FACyrqNFjX/tHfRwYw9TPj2LLI//jHXorIbnkrivuu8or7sItpR1gbEVAw3VJc7qUacvF8izNLsS51QpXIqZ/ZVG86w'
    '4uNesleqE7fnhUBpPO6tzhoTr7YOAYV6jnshsLbEb1+rN+6trhUkLgBh4iqPfQ7DMtqQlGJAe47ltambOCXN1AWgh5cpbz3njDXA'
    'DI724WT+wf/sA150M08j8zvH6gsZ4cKgvQMQQfbpVY9A7WbhfBQ+cVGoDpcGfd4BM/MkmTgi6k9DXPaRcT7m2CxjUdiLoM7lKBkI'
    '/DKP16byP88Q6WfhizjdPeNZQGK1I/OGJMwhF0HdAvLdAkgsOFi0JueoFHaNOYz4ghfnSsChzTtbAJJWGxRe3pF+mMBfBusYYj7r'
    '02MQdzZnWplo2CLu/Gwpy4ZMmL3d+jqa+Zb1GfbEWa5yc9U8vo5TmxPLeKO6LQaBqJJGxZ62Bq0cbC9QJlbKBdfmWtXC5Zb2W5kV'
    '6YmiI8jYlgKLwof0Z8THrAbmYohzPLhoSdvIz7e/znQlXVhh5+jqvmrquMn7pg2f3GlTVuHMBeqLaCtEHynHnKxqhyy76xQR3iOB'
    '00WvlLIg/jmMx61Btmuo7Rh4p2y1uQ4bnKdHkC5ZGbNl4B5G/kBvl/1GTXnEhIvaSrumPBwJ636Xn9R54aca6Y3ia6Anaac3I90c'
    '5fEFIaRLGQxZgs6bTheE2JvqXeae8CpqfzSH3qztIHsb2GFmT+692ftAcf4+4B3FKXOhKeacwnsqALTfgWs6K2VZ8sxF3883Q/aM'
    '++HRF+rlXToT4wffDj89e8K0veDnk5GI+HJvwlqQptikVIQYVmcsti7dCpyrZANvx147Z57KGEozar0eDa4p+zHzAaiOt7floPFd'
    'ff+oeX5Ur/2b6m7z/F21joHeVAISzpabaV9fMBlM1LHN6W/hgUnTqyIw+BjwKmBmTlKTYyoOZaQts24cjQaYL9p6KJoBrHq5fbN7'
    'm5HkN8gyKMvL2rQxYcwa8h7BiJeGCE2639CPDaxzIt/rU2E75WhByhqxD9JeOlIneJ9dQ+j6dy7CbO8MS8XssCMMaScohxzbMUVu'
    'NNYGpTejCF2WODaoiPFq4nkpWHEfCrT5QtOkBdbmvXSrQ7eAIMF0+9QMX/gwt4e1qNMwwSaChoo33XH76rXw79GLFFad/Jg3JKpj'
    'RCIUu+pc5d7NNQZTq/bm6UVurknqzzlhPm6uq30yH7m3bszl/OqN7l/H99ZFDbVfsTaM2vdWHGAotvGtjN+nhxqaQavj0ZbgSbK4'
    'GWAoR2sOolvq8GIr8JBCMzgDP7exkpMFeQihGYwtuKYLToYYGew9/H+ErlnaEVZw8dPJ3saTPfh3t/I8MAUDOJvZ4dwt2SsvvGOn'
    'HLNx54PQXCL9z0pIbHKe7w36OkE0WrjwsYbv6u6MnvuDv8/YHlafBoZRz6oeXMCaQ/fMWSavd6oBP0fyrAzJheAJjQM2tCi57bcD'
    'u61lJuXuzczHDdxcukijPJDOpEss/Qjq5LHi6j5eZrlA9EnWfldIEOF8uomBo2RN6eHBp0sU9tCSeoi7MoIRLcoshJS5103dS75U'
    'cx2pPDeqXcyMkcpVqVIz7h82T05Lp8kZhrdRvyjADYW9Mck03DSVnDXPgN7GwCsLDh+45KtbnKzA9CgZXMemPzfGaGwK/xORaPBp'
    'PBjhD/Q8tf1yYL+/jGjzyID9/tvKtD0Y3lIAjOkovsRM5KO4Mz2drKxEL2ZBZMOxTIinLdKXUqJXbVdGD3ZLmdFTnE7GnYGbTgLK'
    '+QHzFmM7KjkkppdUY90J1uQr7uxOsGqTSNr/POaAHdzuy2D1qaotX649NbVl6jd3UhOdP3BNpUiz6wiGgmdzU5hEtzmLaeE18fW0'
    'z6YBmWtncIDfUtmp2YUDz5yCYJOP3WGd49Z4xHlzGQmCYiqaoq0vvUgkiRGdTDWNTFvKpHGqFOaUl8kJQ65CkMOMmOAbkuUWgmdw'
    'pOnaKOR8N0ZdZXJT+pAzE8AfH6zf+WrW65fBxorUZFjrUBPR62wzIHsRLwqrcraCrRuDpxPmYWL6nX3UIDDaXfRlL2zAqgmO0AuN'
    '5MNwgd5IocRPj2EILwOJEysVCVNT3XFT6WyG3U2Ll5hNsdvv3N9v6G5QeqxXeC+UiXsIXuj3hl+L7DHzgS93/dxKEt1IRXMxruks'
    'A6W6LmLVxZy2rzWoU0XP3Ew8nexZ4NSoKUKUNc5M9E63wccgPMF/HwcZVbyh03qaNWHZbNmbJZKoNRQ9TWwMvGXBy2QOvFS1M7aX'
    'ibkQdFGQYQwF2y5KisFGGi24MDngHd2HyNWGS1O8VMSDb+0CXnuggp+e5PT1HNlw0c81+/OJ/bmeO7PXQR8LXS9moRwgMQ5q/eTj'
    'GUaOdb+JZBBqh6Cy3l4wHMW7yJMNO+9mbgFwzqqTqiMYDVB10lnudKNLCkRHFUDa1pIxVG51OQIg2Z3YycF2lD1U4t95myCzdJ+R'
    'dPuV/mVPHTYxFNVKadVkKuZzadCZRL2i1mmXg/GNsIal+6fgc7HdmyTkKo+OLRzX+ZJyFOsMBJfx97u6jNlTsKOp6yUnuQzu+dzT'
    '8cjcwszLLzP2EoSNZXawdI6Zh1568lwpH54WMTuXEVRSdagPmAzDzF3wDeBt7anpIOr73Y8bT104DkLYNABfIXnN/CQy3s0qUxpO'
    'kivVwdBXruI8ohiSiOSG9LnW+j3McwkOLaNuzIKGAR7aVXIyvCwEn5Mzb6l8TizK17PilF53O2pYjI/lYM1N9HcxNuLfZ0Own7EV'
    'xDJWRxS+kEK3uVtA6ULL9KnK26ryamnVrUzx2ky7Os+1ALZNt/AGY+TG/Xh4KXBKPNN8x4M9i/6KfLNJ26uFIXHN5AGl0e9z/L5L'
    'nqx0INeJywR/QeDIXyx7cUVFWvmOLRUfVTmOBX21qaCDlmHWEXWEuG2Lf+7od0X9pkwlDRuJSrf0Dfbnl+QyHJU+0wvMOGk+av7s'
    '3ikyNVPw08koO2I7YQ7VRTSAMMUcDG/APpskvdAN86FseYYkHGRS6EyjctVgB/CyTk8GqaTgJT/I4NxU5JZjc6tRS7iXEfnJS+g7'
    'mikUMcTuqPSZU8qXbpjtqzTV1jwNg96P4RCCJqc+LOgJtrAdWLrhRYX6ZNVd8+IZsHJaOqtr0mhMwkNPJ6dBIfLSnHxRl+pjWPoK'
    'lZ8Lwa36ecsbWNkiruCds0yHRBl65ppvML3ZWHzjFz4UNO9EHZQqqB+x+6trmA/cNnCjR7+SBeS7+FbAgCelxQ0wQUk5ePiQvlHy'
    'EmM1zOILcVbAiZtiQiCLtyWQ2/I8Q3h4RBGujPsUTLm51jNzbzY3pIi813tgB0xjn2W9FudpNT9RkrJ9duJiQhE9Rlwc+fSoMRKk'
    'KLVl4hF7YbJZSYTyDAgFP/7dH/41/A+HGuwf7h03mvUfio1m5XAPk3k3duvV6uHRQeWH4G2l/u3+YVCvvq7Wq4e71SCPMc7ef1tB'
    'n7F2CAAIRgXOwNdxlExGSi0YJcnkGj3bYXkOx0F+o/R0KUQSZqEJ8/E9X+sMuyWq3mhHPWBow9GA7PVREqQwvKNgQJFJqQpRTVLS'
    'TaKyn1P5xZ1LCgtAi5S+BZxBDjZhdhF5ozx4QNrTrhCY1rf0dGUJ9+PVlY1gOOaaJqL67P+UgzVTc2PF1DxygszOqPlE11x7umZq'
    'GvOGYHdWw+VgvbSiam7Y3jZtjr/ZvX2GNR9DzfUn2GYQ5J2IsCGDquM7HekUlalZoJ7r7j9dVwPn+VMXWkQX46jfiUbm1uQxhuDC'
    'EGNttKEmySyv/qKBA1AE9+Bfy5KT8kw8bow7b1l1nU8fkmhZ0FUUItai0VlpY44ZAfQzwaSaZqUItWJE+hwpmz7jzdIJt5qMKe21'
    'nmoRQBbXxzcMJyxQz2DpLAU//uFv/YUmFpiGaReUCxNWjgtzTcPUNTQEWljpXuEKciE80RCcpajB4CrLGBwuJxcMrDQG46xLDcYu'
    'OQcMri0XzDMNRixScpPRkGjFVZF5OZBwabmQnutxpdYoh5JyzuDdBCTkw0HfdB76rpJMC1n53izlbkBX6rLVYZ2omPbLcFbKFXP+'
    'Z0ywjF8CG6PqIcf8dgwImcjxWqg96OAlThtDJCCOrofwRO6lg+trvKVF+wp+T67Lcac7Hoy6GAExHkdo8agvXuGke3qSP9tR8aHz'
    'O2UVHBoen+DjSal8Rh+f3IU7J6dn4dkOxZ3G4PyVt9Ojt2G4Y1Iuu1mI9c1hRjsnp8slOFGnntYK63c6rLUIWJ1qUXdloZYxMu3+'
    '2+puba/a2KGY2ABMPFGEbPtFP+5VmuIxPG2VvpnbnEq1RXlRA2BQ5PbCmTcx6oyZguRqoCxoEnIPHrTbk+GtTX4F5Kju6VnYp6iX'
    'jqexyd2CYSlRIW+i60QmFr0c/W7lbbVemR5VDuHhcP/w23Bn+v7N/lEAb6ZHx403GLK1Ee5gZPGj44MDeMQn+POqsvvdtHbcDKd/'
    'Wau95feAp4Om/lmHAvh7ylD3agcHP0x365XD6vQNSEdvqgd700azWtnbh05MsXTwurZ73JjuHtQaGMG8uHN8FCJJBbVD7Nb+Hr4N'
    'Gm9qzSm/qhx+e1CFn9Oj2jtoplGtN6e7x83K+8oPU5y7Vwf7jTfQPNepVOv7lQP+XXtXrb+BtvnpNQhpf1kNXtcBG9PGQe198LaG'
    'eYRp3k+C4tnOQeWoUQ2R2FpTmPmTcql4Ft4/5bybFylFkJ7YiQqSr6/vo9Etppe8UesUaGAwpixqZNCTONOFdK7CufPfygHHdZ++'
    '3j+oTg+r7xvTg/1X9Ur9h2mjuntc32/Cj+P6u+r+wUEFhM7p7m7z3fRVbe8HRPpepfEG/76pwbiP3mDs5be1VwAp5JUG/+p48e8A'
    '+zUOLs//NrDJtzBZ+0f0TwPW3nROaQDfrPG/39YrR2+g39An/rcxpVf7u/pvY/q2ciRhm4D2pH3bCRWnoXkofRMuvNprhzSdLJZP'
    'dytHNM27b36owx+Y+Go9aL7ZrwNlHr9q7jcBp6+KO3Ug3fBrGnzgO0OltxWdFvPrtxOhF4nHSj9Kl3oqcDQmtL9bvpyEVgGoz2Vc'
    '3mo4Vx6ohFvc6FZWbhtdBNk0QoZ/Du+C3GnxtPRwp7BZ/u9+s/wX+fAUmO6Pf/jfP2Do7IlATOaOCqxM5d/9aaMnva3MiKBUt05a'
    '+fUNfJe9h7tz5vgCPlz+HQ1TDrb0m7+A8eLwlvMh6nonWVPvgFk+KRc2H+6cuXk6dCeTYa875s09tD1+ng3KpZfZvOZt93PcKbbJ'
    '8RNDTuDmMUJGg5fuGEuZdXoq2XuRr9nhBQBPSiB9tmM40Nik8KioL1LSD75XIcCYGH4zINmEXIkRWFZC0RHKGF1K6ka5HP9qArIs'
    'pR+lyGsq1RBsT8qrkDMQwY7XAgGGDrt2V9OOq8JpIoVDylWfz6PZXjqnlL7wI4sALCJuEE94ts8eT9WvElLw5YRuDoUSDGunuIpS'
    '70uDfWIynXjaiXvTTnfaiaadybQXTXvx9FPUn37C++tufxr1QsNACHQGbPWC6XFyp4mOimfGjGYzHHUG2u+P496MSyPtyUFW07NO'
    'Tpqs+KwFx5SAjjTqQPurOSPy0hjQHSQJwJ916jxUeFzjh7W136LOA9+RRjJI+mjh2MHzICIJJpksrEoP5BXEm24yNjdT6uos82Zq'
    '3hXQmu/70NIZQ/gAo+oto3/aN8ETo2FU7Z+08AIoLx9N8rVNz7rT9rzK9zZQ07vI0XBCo+snVX/QOlk9K0bwT2hSp0JJJhm8zbUw'
    'bfyKx+LtycoZ/C9AL89OSZ2N1ZVhA1CNeIZFNAGx+NbqPABtGKQCWlhbGY4VL7QpL20HihIs6tfXAAFOB51mHapeK4mT6fe/Mqre'
    '71+QES3xe30kICNCNNiFaYqVKjqoMDdXWaFJkS/SSit+H0ejFkiiiLl0jmlKI00x+ZAjq+SPnOZIhcbv/jUnjnPioTuLRF144M2T'
    'iPmedROFpWU5zxFzBoe3l7/zLnxnLcWNebex6+lb3a+8OJ4hiGRcFz/0NnwyQnqYtxcN8JgSpMahgJR2rZPIFJkF5T0S7KCk4/mW'
    'LqQ4Dba52bL3XDvsZYQXWupmq4yEiKHPb90gu0xfr2452a+C+cDkeCUw6QZsAdkhNtnI+PBSJG56slIQtxb2vgdZ51rpaei1TeY7'
    'HhGspMq8tJdxpqGNgldvZVVCf5g918aHSxbViRNPSqfJMpuR8i9rRsqpEylzojlxznBjnL+HrCMi9OWjWpxqB5GPegfJp6ZwJ8AU'
    '5KspQwGsPXNT0aDv31Sw5Pd4WWXBif1EvPX3E0Tzpr9DMLSiLEObA2BBN+RUd/aFJyV7e/H9r0mfniXvtOLxTRz3xZ74eG1Fh5wb'
    'fV98sgLcTKZqZ+4f/PWgH4eWn3d6lz9F5tmWe/Fj2JzNvTkuLj1LT1YWlYQkFQe6U4qMxdM9chCUnEmxCsr9BAsFkYwsLEGu9qVP'
    'rZqwUhRL4Ip+MS3RqMZSQBy6XS95d2e/bOLVcown+5WDq6h3cUNBZ5h07clSUa3KFfjv6J7iQt9flpQeHGCBTMnnIYwdRwXYHo69'
    'l0gBp4O+JXFSEpZn8HJhOv+pVmepNJ6hWBXbPNfpZfKYCOGnLBMzKrVQnOd7lgqVnblYDKT7lwsV/Z6uzyxEsWTka3/REFWnVoyC'
    'WHRKaS5vmnNBOOvlaUleKf1KOP3MVfNMLAW+yse7NNLqKOMBshuzxG7DHAo8WYSI1E/mfi2wBc2lm1R4fnmgD6jM8tmoRq/f71UA'
    'K6DvwgNDmJpbfV9Wk1YwMgqt8++pEq0B/iL6rXLP6K7wI6Cn+nmIcazw/K4cmjAlgNA8obapM5i0eireClU8h/JEc4WM60BV+XYh'
    'hynrB+wjRIyrYBFT8FCRHqgYJPWTuogexNy8sLZWmh38gyrQBTU8zUEvHqEndPKrNCBQJsgmCRtKLwnnZrOZ2cZ2jK24HWH6bpJ8'
    'YsTyLWmBkGt/iog12XUy6PF9/pZzCEidAjbCTerFv1tdhcWG18xjNlfrCdUZZpRrJXBaH8eygb3eZeA0sLqeOmaAlKQb2FANXA86'
    'MVrjlX3xTcLma38Jey0Fe+2pgf00BXvoWQEYyGwJICGnD0frptdr6woyWi+NeEmT8oIRbrZ7VEnLVoglOa08S+PG9H/NIN+ydlo7'
    'QQLNukT/l+jYORzFHcx7/2uhfB4BiiNoyYJ+5Inysnatg3JB/BkYjVYN6WTeQNgPlOmJo9MlKyyUp/7p/7YUHwQ//s1/XMAIzCb1'
    'G1vTF7LQVnbZW+45QDWgedCaOHDhykXjLNsVXhvUE1OKmK9oVVqbmVbhhG+3nqIGBZIVdch+eqw+6e488eXoLbaI4e4oKxrsjlsq'
    '34ojjJOvkoGbYMGh6KcP1/bU3QC4u9yU7rBX4rEtgSmkdefXpVITkbnFdjjceWW7g53fdUPRtyex6Ke18XHxKXblooGnOyg+PtYf'
    'H8yx/6N621kTobbx6wnKuLFav8CfdVE1VleAo66isdBjDFt5AR0z9czmKYYoa8ohSrGoaPkP7KX02QpD9qO3l76JexQi4ddtX2ei'
    'kiRKGYmyH3mcOxrKxEgSlWDpUF8bLum8qaQ4xlw0aNowGgf5H//9/7m+QaSShAW240pUQGq6oFanuLdw/ov7KlR1/l2pVoLS+Vqp'
    'QX93a4fN3F4Y/NUk6pFAJ7brf3tcOdh/vV+tn9erRBLLfHl/moe/705LOzX4/xT/aegfu/gDYZ7kTidrK6svPpzt7CmTiNf7B81q'
    'vbo33dtvNGv1Jvw6qleLB5Wj8DQMHwPgR8oFlZunxL/cNFOk8BQ/Xba+4qez1HzTfXhzAgVKqki1vl+rnyZYRP0kp1dpVWR4jfKW'
    'sAn02nA2SIJ81Olw/A0+GfB1LpTqYb5D03e2Bzrf22fcUd/JHieoHZ6U0b+dnorHR/ykLXD46aj2jn+grY55y4Y5/ButhoJmjXE0'
    'hff71QamCEcznMZU5Qvn1zzw3eNm8H6/+YarN95WGm8CfNes0RuFB+48GWyc71bqe7bz9C7AdwrC8VG1zj9rh8o8mx+bgN3AfedC'
    'r1cOG/toL2Khv67sYYrnfO24iQS0f4g2cTvTZg1evjqAseLbZq28E6JdEryE3zwI+A1vpm8rzV39G8irUTt4V1XF3u8f6Z8aE3l4'
    'RmSEO4RI9ZWGiDBgkOqpzOMsT+ldqElUD+Ww1hQEykOBFXJyelL65vTs9Gx6ugz/Tb4pPZ5iUTa+oUHBz3oVBl2HuTt4Deugtne8'
    'izgJQ1piJcxMrkkT7RGLg4tiB1Zy0ptc4nKm+P/GKG3SJ6OoHiVakikCxJy+rZ4DXajuQldPk5MiSHdnaPa3V/lherj/7Zsmrd39'
    'w+PacWN6UMFk229rdbRnm1bfVenv3nHju+le5f3htPIavh/WaodQ5m31sNnYgYFxpUNciA1YAwJleEs5aamOaSZWOTgo7laOGhzD'
    'pjOIk35uzLwsgNnCBU2WeDBixdvGAhmwCOEUgDYLDM6yju/2j/yJab7ByQUUIC0pglP0RpQ0pU+hN8GH54cwDIs1MvZjHFX3yjuI'
    'nurUos/HlsYh4SfgJ8QLzYdENvQuUH0TXQy4g6HLGEHAQEci6I6K97IdyKiZxixD8m/fhdscx2ELGmAKSpAHZtnnSl9vcoKh5lWJ'
    '1IWbuE3DChmGPVxcs3dtjgFFUTRwOKf3zWFM4tusJhxW48FSJOK9FRO+AHzfOmlmYc8o5c6dgAPY5nu3s7Gvat8zU6jn1AJG3p0j'
    '67RPCi91cc0Bs5Z231TqlV0gzAAHLs6/HJwfeojnCKxjCHD/8GBfbM20LNjQ68y390Jrr9Pi8tmXlcKTp3chWUOWvjwp3AFNTzxC'
    'fAciSIe7h0TEiZQUDjhdM/1JaYHppXuLLF9tB+srs2bwoW8WRG1mlVZhowYoBKh+SNMpEZYJi4i2s4AJT8sblKqpjq+StmaJN8LO'
    'XRlaoW2VMa3SjrW+WaK6GnVHqIplDvJOaNbzuGURi9rT3IlZk2KXbNZJ+yNtj9YSayYOU8vAEfZ3lVKxHXGwRngKfvlCfXJx4LjV'
    'qgCn1126zbDx5Qsqfh4HvuZK7NzIs26DfNo4x+efy6rWTumzesV+n/qtdf08v7Vvb9Ur676pv3genLYYOWjKUtZHkwtpR01dBp9F'
    'l7RDqewYvxM+oeeD9mhXhOTThd33BRlJbzdqK6v9Ihk59AaDjxEKESSZc4pYkHpQ+UV5rDEzBsgEH+MYDky9aHQprP05mF9CvAzO'
    'tAjgsvspRlNya4tzcxX3g4jSkFMwvR6GGO3TTRdKW55xDhoQ1PpHZH5Bzv2V0Si6dcLkUHSgXr64Ks3HomTciOP+q1tRFTMahJt+'
    'BB4viMcqBuTZ5sA8xaLhjqYbJ128mHLhk7+7ibNDdxfBjl8GY+16ZcpBcVX47euP0l7Ch5L4UDAmid7yjPTyGi1ZAdu3/sh7jpUS'
    '+4jLu/CHs/ZAEyA8zIqE8JG8bPWeaMu6FtqqhugeDQcqF9CtV7y+5NehvfJL23JAeVhFC440lURDDJm6K1bkQ9Yp8TA4hdPDTBli'
    'Pk6MuTEF61FmRZqG8NVZZmko6NWkkEg7Kl6O+w0vHnVwATUaCwj6zTrOvHmnhuNKhvarJDxvSB62DR1qxKkZdMpcemXmTWdncN3t'
    'R/3xLgNRER1SIPVtbuiHeaBrXFi+dJF7snK2U8JrWeKv+lq3239FzmYqLQEr4XGrxHALfVS5S3PuH//mPxpBjfL4zgrdJfmHE63L'
    'xoRQQlxPBNZx/AjsZzkFYlLZKl/nWJT1P9sjGNPrpmdUh7GVPOI788uoGEu6uENw6qWlNHFx2eu2u2OREZiD5PruehjXp4sZOijr'
    'IsuigEeN3ZIZpjrtOz4LWmLD/T6vctXxfi+M41EhMEV9wCPyQTTnMA7Va2U4nwBchN6ZoSl5qX58UA1Wy95dwi9HPmLtIyuey+he'
    'L2/vKod7jsoSDvslRDsc+EuwVoEhF4Ho6T4RtuhQg6vVy1YfmtIHsF7EbyovtSO9ySUh3cyq4kGf6QDlcp7MOVapEL05/s3J735z'
    '9s1vSNvxs09xqxxwnOddNOhGNQpGPPgTzBedmdNn7Pvx8DMOtl3WqlgZGsGkvPz5KFOrY8vQkFa/4u+j2jv8w9pW/OVpV8tBPG6X'
    'suknQ3mRiTydR/PnwN6RCB2t8ZXo04ZyliwoPbbyayYWqFiddlc2Fh+j+BLIrBfD6QtPpuiqpORhFVeT5gOtv/rk6q+vQ/Hq9Lp0'
    'n6H2nxobkpbWyvJS6xd4guT5G2jf/WdLj4XhUa0eOEEx8EAsLIhKun6T4gSR0yLMrLyrjy9BPMuzlr9cCLRCsRBoDTm/R3IO/dhe'
    'FW5U4G/LuekDgrfm11bv5Nll44WRVMmTMp40m6R4V5oEUt4b5XxYQjd0VMib24DyzlTfAoSuw+hcXZ9xFswekU+GMllthgPnz0GR'
    'T8reTfcvjBaNMdzQEKVnGUrkJq0/80FoSHFPxwiPuxQkp2UBgVTdAjbwMR4nlAuxhUapuFkb0bYjY2wAMJJqiW9dRZ+wpKqv8oiW'
    'BMUCq0GsNtlJI2UU6hKKLAwkmvdMCfJ8Bsnr+UUVmuHxYYp3eRmPlarHoZRFCGO97Opl+QLYKmOXgj/ZtCsUUutvAX1GuVuKP8ft'
    'FPZUOURLhrRE72ctRV/B2TWqXjriEOATzJokzhduWTJgsWXX/LI8v74e2bYjuqAnUGSyFh2au/R1VZv42nYvVdTyCY4q6FJDYJIj'
    'ZVHF07IXiOmXzy7WU8yijJd8AV7yFbIsFwzzQF/1Ie5fXbxKt5YJy8poAX+Q1YKwVTB+z5g/t38peQJqA3dVRFat+RG0zIUmOMd4'
    '2NBEmKVHSdXqmxsuqpKtkVK19OgOtN6yzL5ktNa7iVng1lUwj+dQRF+ojqTquOMdihWzM+fjHfNTHtIpCl7qzJ34xlM+y9QNOMOm'
    'ZCOH6hCeOo6LE7w4k2sFogcBhQkJzTnSyy+uBkkY0uvOv4kSY7G2lTk64EgGovAYszKL+eoomERRl8/dWzyD/WXXSc+LN5QDvnTL'
    '7oeZo/lNZxTLZ6DJ8Kudmfh9YIOu5QX6TAMEWu+Vhhh5O7WPARqHGbvFMBRr5DWQegv2+LKVGnABgHgA04hWAObk/9hdRBiYddS7'
    'dUUIdWc9GkQdWI9/ycaQRGqOAeU8W94NgTRlOOi4szrxdPVdxC5NX1phbBiSu7doreN2sOoqXPvQR5Lpdyd0vfTwoa+EVNHzbSDJ'
    'rS1fUSlBkhGr5VE6zqnxAkHfTGt4SFGptV0ijvaZoxe8HQ4uQQi8um0AD8VbFcVBH7K+mhxsYWD+MOBVVjecuMTAKYkNK4guj0bR'
    'TPBfjLmS2RVnceGeC/QC28Y+u+QJvqlcVLOI0+8V8e83dLHndlLB2PeXCi4IhwDxLCLIhJKRuV0Ty6Eiwn0r0+Mr1GdiQBDOJWgI'
    'fhmhjnnJ6JssvgnTwIaj+BMF5+smgx5dmRmVCorYWgvAmzdFD6HYSRzqKpEbK1rCMhLURQSrPlIYyXsszR27GGc9TmKVXku1F9xc'
    'dXtwJuhRLns8ZdjjgdJ2y3UH1blDQma/Z4JU6ygv6vFA/5xJpv4yaF/olzLjVxwUswTAbMHvWdkaaP8yL79nyX9rKUdCqQZe5CKD'
    'jofROMhwpS2JY0jW6cybJiGfy2NZagbs7aKFag3hFX0/9JQcs05AthMw7ON+MRrDbg+blwwC8eMf/i4YoQ4ONzWtStMRhljTRozs'
    'J40mi56el63rgVWq/gLJZ9XTNlAwJiQI2gXI2lYRgad+MUxTiwjeJcCsu4KtmbaT2RreDCpwQ2itrpDZjbC3/NNcJtzdM2I8PMgB'
    'o5dQDAiDEXXHOQx4mBhrTAJlUrp/3XifrTgU36ATXiT6pPXMdh4GE2vciUuhR2cup0cw5RamsMmmRG75uHRZCpYcq8qlQrBkbZTL'
    '+KhspMtL6oypfJrRtSRK3LlmrHCGEXRxjGArYDMkDt3FAbEIQzyckqOcgH7Xq2RT28o7Fp/GIBZtPtH217f6dEyOhS0yGtDCz73K'
    'D5RnbFNSDbUmdS5Z6ZgzNFF3dprn6N9TVe6EV+r5dTy6xEx3DXOpqpM158+BfqMuZr1VrzCVcZJXpk6hH2Vrfmnh+MkF6aytzaYw'
    'jZZ2IM9ThlR6ugtdAwzc/qWRbIYtK9vNijCx35zmT34Xnj0+DVPLz7Fhy7Z1zYhIQha939MfpYln/bdRic+2JpaxzRIVrMxLq+cP'
    '8evioLCDBBUwIVGsVa/v25zZlhxTQG3DMJTivlkLSG0fTuWFg+N8UGblv36yI9bdmGHVoIlitmED04cpmGFW4HwVcXxM0A2bYF2t'
    'EEolr9FuQyTpDCI6aTsvxkWAucidDVFcTQjJdTZcRfwCoBaBfR0svtuN+q9iJ7yQgGrEDn2MF99c5bfRD9AZzS0p+uan/jFRIW32'
    'n1RYHk8ZDMPbT/a1wmxLpfYtdZPXGD9JDfucNzD/G8E+/2zzEur4EOd4+lNfkRo2pFLZRxPj2HZC6pWdmbNHBaESvpiFn9DJY29x'
    '7yuLnTQRmog9BjuHVWdwWSrdMVasWalgZCWji8PcZoNJQhm4EcIJ/xEGi866a6kEKBwdy9Q2c2ACWelP/OqB1k1xKYyaZQvcPtBq'
    'qawAWt3kPV9WNRmpMxaNiTaSTfjeNzb0yWxGGSvJoZmuGgAWHIlYood2B5GocuJ2yQ8ybtfqCx236zwduGu19PxpKHmH7K+lXttV'
    'ZpAfHn1xXt0Fj74YpnL3ITPAuncnIyZKo//8Vq4tf4WqRN1c0rEMDp37G02BXUpqOAOKbd2DBMR0TxGM0bWyYpftjHLGn77bz1Nn'
    'CsG8EXhL2ZXH1OJhs3Ah12Smh+HC3qpHH9GhlareKr2Ou+QVAClOKSv0c7bZPb+F/38uWAvygrESL7ApeEGafRc8y+4Cdl3FmyVD'
    'ShQX1LMvB3LmMLRei0evBwPMIqb6BSeYyTUl7DLpJyq9m+iWHWGHpIwtUiJQfQZmx4FoNO5ewLq2zm+VenP/dWW3ec5S+u/yp3mU'
    'tE5DFrisBGZ/Tn9XRGGwg26pxUfaK4w4t+oUapKfuNwQPUJR6WtiHskL6suYfJ3ZENKKo0r14JMvaVHPbzPdKGR2P2Vjr8wrz12z'
    '++cv1twaMffAsIyn6zIdlFJ6PzU0KvIQ4eoFZkMAUFOmXqnQf6p+kb4rYnUUsLh11pX27zXA7AJggQuNCYMmGj/fKLDdaRbD9r4w'
    'U9ZMThO3MSaXKFdm4diBtEkrz8hHecSl/T5zDJjKU94pKwrgjJV5+eiFhzIcwNFUj69GcXLFyaZsQEa7EmiKnjx1zyJmqJyE72tH'
    'KlYHi18fZ1CdirjFqSpAwNfi2qzy6t3DmZgjSTGNI7x40HjYFEi6ezB3yA9TA+n5QuSdTeujs2yavJ5s6xzDMiQP7y6FT/nn1pGl'
    'wlC/193LR72eSl/tskWHJ73E9IkKR8Ye2o65McY4NJe3aDasEp3q/KYm36lNdBoGf0xcld1BD0OqoC5Ix4xDHVx/0C/ChHxC22vq'
    'Ag42P9UZUafot1ZafRr8+O//x+DFP/1f1qUeCht3GeauGiNzg8olXeeSKyP9qj2oYVlu3j8mDQMRW1Wuh4emWyfDszCQT0aYprUg'
    'PthsoaEbKs7J25q8B3TVB2MbK+5jfJvkDSCZWRN74tTZFuxjzWMf64Zj0eULtYiJVLylUA7G0UeVG201yGMgkO5I9Y2nUk9faGxH'
    '0enBI6zWbfAZdfmYnrePwYH6mDkHXnRHKTsuakBNsUXYjNG7YfIeR7D7PG6hb4XCuQHmu2KYTJniDupbDOyrYjebjL8cNvvJynAc'
    'XA1G3b9G7WCvdwtn8/54wD6bKigZ4O5aGWRocwsK7x0l4+/J+aH44sWLlOunPlmZnvpU1776qoiIiiLbV2HKykh177HNfFhUvduG'
    'AeL2pkq4uRPbVyZUOhXeCmblTWxf6f3ym+C5o3A0mOEfKe8R9d10wfivUirYL+5eomGk/bbu0g6lhtutldXVo07aHETt0SBJeJ0F'
    'fzrnUGwLJ7YRj7+Oa319KMyHYyd6ttgIHE84vIbMQp/x41Hdhd04DNxnP31x4H2nZL02re6mz9Tevz1/X6vvNVgE36tXXlO4idf7'
    'e1UQuisH8HD0A2rKjw6qGBHjqFpv/hDUXk/3ahhpI6DP+ON1rY4mzM36/qtjyjvTeFOrNSk/0W59/6g5rVff7TcovIwOq8GV36Mu'
    '/m2l/p0b5SFT6EpzTaFbjvqdbocCnTGPdzUmJ6xHJ+I6wwXuxfoUaDOs2HBwldJYiEAps8nk/fV7YD7QtkZpytDVHPKpZCh6rA+X'
    'oo/lQLR8568n5im2vvJqdaWMQLbgu76VeJkVVU5jjkuvcyqbasC5VbZgaFbIaSiFDUeDyxF6JFwPOiA3XDlhoR4gqz0fdi6OVCnM'
    '2TH6RIZtSgYS5+OrwQ1A1EXzIEDGaE9SwHxSb0Fkua3sM8IRKje3ZXJMoSGPOlm/ut3v5HPQalF3rkilRYI5etazlwLVxpuoWEHD'
    '691P2p2fipYoe3dWA7IQxdJUhjI5elUcfIpHvejWKdbt9+GM3Xx7gCodRSAvoUUO5Lm1xDVbg89LcLa+7cVbS5zad319Zfh5cwgL'
    'G2O2rG3Aw9K2OewQBFW+001QxVi+6MWfN8ljoUjbaLmN+tHR5mU0LK8iML4HhLbG48F1+RlBfHm1puHw5/LKJqobikiR5VUu9F/+'
    '4W//U7BPLtzIxmESXy5frW2/TIZRP+h2tpY0qgBNMI3FVgQHiyW/fyB+xptoZHZJgX7Lv3nWXn9+cbHZHvQGo/JvLuCnaNkZ/fBz'
    'gAhowYKKR8VR1OlOEi5CNW7YA/7Zygp09sf/4x8Doqagsv9yGbu4/XIZ0OUhz+m2JkXTZ9GRVWiFu/gpGuWLRVwoxSehh03CFNW6'
    'iK67vdtybncwGWGU1iPYLeJc4XrQH0Bn2vHmzRVMT5F+A07Qnn8TCeeiN7gpX3XhBNTfpDbMy7jX6w6TboLTlTESRUiD9siSK0KF'
    '0rM+t6LRkosBeuMQ4MpvdXNZjabxtDIDT/SXyLJMziBZZOj2ZdgeL22v/PaesfYGl149fDOvs6rh8QDWA5JTqmdigUHN1gQ62NdN'
    'Qq1ia9zHqCztXrf9cWvpvI1hWHuY+IOWRj6cRT6ajteBjlfXaUntUl21qF4uc1ui23IU/PCBuYphYq1B57ZEBiyd3atur5NnnqdP'
    '6/fyTUP0KNHgHQuaw5GBnv6wuRAYoByAQAM3Ob5zK7/NLVYb5jrV/uK1YcahtmSxfAYACgzOiQstsoNIrmX3EK4fKjhqgIqXoe2K'
    '2bNQcGcnhCJZUZEMj8yOusK7gF87h8w6R/ttlNz224GI0exTFe1iuMnyC6acHt0Y6XAuJkIOWvBtBeeoqfsU13br7+kVFvHfmR0a'
    'QzTfBl+C6Cbqahg7JTyOdvG8CAJncAeyAibmO4e+IG2dUzIpZy9H5VOYijbtleKhacMhq0Ph9+FCg/yj5AIlFsyYEzVnzhgAGsiK'
    'ZgRArvLqDmh/IQKjNSJikLQWGgEvDt33Fmb/gH+8pQZl4EiY4xVDwUJaMEL4x1tUopw/wIPBZf46uZQDg4W1UA9pARqpC57kyUfF'
    'bwAGvIDsBT+8HkOXKEDD4NJhc1Aw1O8TOEv2es3BkOyC9TOrxGmcf36pxDnF+hs4ix3AOYyegDovgDi7pEPkBLzdZFym4GGjwU2A'
    '5nv4uqCTKKFmiCwlSlSfDcHhLNLAur8pBE0KnaR8wd+CHFIIDmL0bN6LOaUrNFUIDlHp/+eIYampRsNsDCLeC3411IFTfQAEQH3f'
    'As5OU01Rpr5oqzvyBxvDlJ986XYKHAELxokz3aOZ7sBMFzhqx90ZbACkvteAAOrSKtr5rcE/P/7hH4P8ahGvxrUZJ6fninTY3JCO'
    'iX637jb59Jj02OEIQ3fDeVFFkTw4Rxo/b/5wVEWtxQks+Nz7BtksvkczZiTVXCHIVdXL6ufxCFgKfcT3r/n1a9jiVFmE8Jbfvo3h'
    'AHFtYLzdPZavd4/xpXq3i3tY8XjI9avqrW6Ni9aaDLaG2aoB6KTXIfv03FHtHX04GnT7FML5XTe+YUgc44AbomzP+LP5vlbEYeNv'
    'TvWMv44P96p10p9w1b1jNNuiuAn4+dV+fa9RrP5AD+9r9bfq4cHZpkWmio7wtvbOorPRrDT3d6mflcPgoPq6qX/X0QSOOrR/0AyO'
    'j8zPvdr7Q9UJzIUd7B/iJ/5dO+Yq9ePd7ww0flLwsN5RdQ/TWh8oqOaRIQc5nVcbf5vU2lyVEm+revxbV8L03aov9JO6glUq9V3T'
    'FfxtBvYaulx7zz2s7H63f/ith7CDKkyQQdXq+vU1Fl7d4L9rq+qver+m3j95in+xxvoKv3mq/j57yn831N/VFfVh1dZZ1YXX9Ecc'
    'DfX9sPK2Vse00txNu3/j6rlBQs7jcXHU7ZBi7MudY22g9FydMicIUQvu8eOCCX8HX0x9vtclZWd6xSnNxie3Br7gGpqolCIedxVR'
    'Dl9wOTPqgFiNUwpfBDICHrGhsijB0YRMiTt3rw9qIC0Ey5zy9FfAt+1sDqDjDcUn88b04rs4HgaUHzhAPSYa7RM/4SSwGKAPjg+9'
    'XvECJKsJmuvSPo4wSJwnTYPOwY5zC4yocRA8xIv7CXDqCzi5dHJaWTZT5ktaRWThKFoUk1gZze0oaTQhGRkEjfEtynQkUudEBuLk'
    'pgsHiHq31Rr0m1ELoClQOec+XR9e+bACcuKe6s17PY58rhdfRu3bogtAObmCbMkRr2aPAqoVaQxYWFYeDwa9e+R5W1kVFrIvtY0B'
    '4dQnKQjDHL7BJYRJTWNSoQ2jftzDK6wreN8YD0a3rUE06lQACGv4TR/+agLz3ojxPncwqvR6+VyJZbAiwYDjr77MGNJNRjB0DzZb'
    '6lgD70mTgWRRgs0LFhObn3/CM6/SPc9rtY3Lr/gJdzDbZpvbbM9os/01baawfdsfoNpLzdTOPFjz4GBGCyCXOB7/LJDM1GeB+dRN'
    'uq2egoOtiTJ4R+O0oyD5RRwY6NeB+gFY7HwHjCwCKS6+Ho5vNfHJe1opZ4XmykC/RWCvR4PrBtFQHs/W1M75CA5Y8cgyH/eYSGTq'
    'MqaFl9hPRnfGcrsX58xoKgQepS109MGR5kJvjyCskrsTFwh+6XvDjBlMUFk3dnUq1vU2At6OLA1QS1Y7u/pdnmcAePF+xzIxUyV9'
    'jCfJHmULCrNaQszlTfE5XAr1YidoB1nErWdrieAsneVC2yqDNqT6Rb2lgRHl3jQHEdBd7nCgu4EeezxttzHOre6uuYfmPfNzl4JT'
    '8KGYnGw5qBYfUzA2qQreVAhg6bEfLDUAByDYzgImsY6IOXsjji+BKmxjicY9DLrq3yhjO7wtNeg8lO+aQJe6iHaG2gpidWWUeWEv'
    '1/YJgD1zHMCO0Gl2BJKYM24Yy+8nFHAD7/ocF7tAD4hg0VnRPx+mWizRB21j6BnRQicONQ5JckSsohoCpIxo0hsHcTKOWrCkr3Tv'
    'Fu3HiRV0vyiJNes8yLJkriqaycE+c2b6a4KLesdR1QHS2Eajj8f9JIKJzwsiVeT4JYNVChr98F/+4X/5TyyAIecKULkLEhn289EX'
    'h9DvFPV8wJ3Q5U0VwFqrF/U/KkyS2ib4JTMl6DHFwsxLBsSxfxXN37dFmSWRojhJD2U8OTdLwUFtt0LGBYjYPTo9pwlFT3tqQrM3'
    'Oxf/xDLGA3SNZGr+Ze4KcJpD3ONwtXbG6tUfOrjU388kc88uwYuc7RUEPsOfhM092BaA8RBCfx1KNIld7r2DYKa1/c7Phmj0r5w3'
    'D8rUlhJXJWidgGc31YefNCW7ca+HcQD6lyqD0s8e1PTnnIJj2rlS6C+ARByjO4TI2CFklZlIdeWODEnniiw/WUGuJ6DfEejfctFv'
    'KMCf7xPq4Jn23MyYKteBRI1UxRMWAxYjTIkBgtq+zCIjK15wR7xu+PtPnajn16rXdzyd3WUgaITO61+pKDAHfTvRQtpG7S+L2rv4'
    'G6cgJWUrVQOFFMboaFhwp8TPqM467tPvTi5D8J65g0odxjjqNTRLYWljFHcm7Tif7xeCjySaYuglT5JUjGZH78VknF0gA21ljnU1'
    'vu4ZCyZpipH0itRlsiAxFgtkGWRLqLMAFVzafvQFSL2atPP0HN7RJm50VspmZwYkjJaDELJEKe8tcclVctFns9q74J/+M0hhFkl3'
    'tF7km3Qd2R1jiDHr5EKlCFWPAVcemujEvrRtDzFwdKGhkz0JjHQ8GvQvt3/8m/9HHE75lAed4I8okVxCZbSuLQm7EEcO904lJIb5'
    'bimZLPKj4o6imKQltVkBcSjDy3mjpRpFklyX6OjFb7aWHn2BZu6Wsg17TMUr8kpzDXJSRIUF+5PrpW0KBhMwZJd+qGK3P5yM0zVR'
    'cQpPaGiwxIwRe6dok0esGGd4t+TkAB30CeTWUopn57gTGNHhqpuUmHG7lZWNkLCEIx9z9uhWNm7l1eHnIBn0YLORH6VdUelphvnb'
    'YhZo8+ycDHrg6OYbPFlZUw8zXNr+///f/5kEZnx/jyFTmnNEmLycjdVkl+i9X84pgoVwcra93Kwvx6PtVLpWKCqBXTHR/Obl8vhq'
    'gcJI9UBib2rNBSvg8XRpG68uF6yASoalbb6jC/CObsF6eJ2ytI1XVQtWwOPx0vZelY218fy0HFTISntBAHTxAjys1qw2oG713x7v'
    'H2G4lYXb76GFXrosvPPmDUul5vflGK3eFAemtcTimda/sJVDtyMzuYhwZYMbdKPofA5+G6yREEecHnkAfCpilLaciNrpcsEDin9D'
    'btlI+aVHXxAQHFrvPtjilhmOR3rkj74A8DvNAwESvsK/IEneeWTfkejqMJnahgAlnbnlmVIZOvU3q8r2y4T0dKIqcsAiv13yJgYW'
    'Px0TBKsTPM4OpBDkkOw9vudP86MvzsU+uT+Pcao+vByQVQnsxTAvBBTB7cDkULdAIirDZixEhxDGxnW2P4Sl3w+6/XwuF955NMS1'
    't/850YCLeRE0yCt5QsS1i4hrjQgEOBsR179YRCB3WgQRfNVOKOi5KOhpFCCo2Sjo/fEo8CWEGTIB9gV5qC8PBAHFYkCXkXi0tUSy'
    'bMfaSv34h39M49GXIGahEeH4aPxjx0Bs/J5BkHlXIYj/atId4rHojxqESc9z7yhS0gjsGWk5RGhlTIu2wXCJj1hbS0L3hJ4Bf28E'
    'FLdt2n4MH78LM6TbZd564C/KIo5l/AfXU1rf/EmzZISTOu3TdDiGGvlkOkUPMxPb4y+WLwu5v4iuh5vy7Ut62xs7L7fp5aX7cole'
    '/tVkgK89JVCVIh2imRYU7vbZOy8/NDlNihwClKPih8HPqzDmxvGSI+/eWf2LnqKzr6OcG6gxXV3AMYwDRabunmxuL5uYsmczTlLH'
    'XC9ANMvlI7C26syFXq3ct+rM1wHxhEIw36BpIlQGUAeDdtSL8VGp2sNU9a1cib0w8xsr6a8qcAM7jmOsW7ItTsivjl020UdCRRTR'
    '89R7z7aFgMLyBlsQltfW2IiwvPqM7QjLqyvqTmZtQ1kTltdWUCsv/K3R8i8PnOaGhLa8GgSvhLAE36v9Tv4mLCWw+uP8ChbU/eXY'
    'Je5waC1CrXyOTemwqyXWziGiCX/0GUUQ9Rl7bz9bCLg5qyI4Lh8C7lzqM442C4KQtVVJ2j88QCRPq+/MmwFCap6Ki8zivMP/Qkd/'
    'AfODPFcH+gJLH4pdKr77EKbqix4/W9Hxd/JClzCdnpyFKfE9TKsremnp+7GQvE0Og6jVwlBBKo3tKL7ofiYy1lb+9HV868CGyefQ'
    'mYwSIgaRQg6DpZ0un2E0Glik8O+ysGtKU56eeerxTOLTbc4kPw3GSIAzqdAISDMJ0YFFhr2zCNEKBx4t4n/CTSdqik97nssx6dSy'
    'tJCLKiGnU62CdGmyiYDLs25TC1rBx7o9vF21fWr1Bi3lSv0KfuZPGC4LjKf9XHhWCMztMnK+ZdoZNyldRjzemowvihs5JzvlhcqO'
    'zYwdeJY2N5F5o6PiX68UX5wWz4Oz5ctuIXdunMgR/egYOz5HVXNp/Hks9qzJCBF4XD9QThO8dcFzHgci7d7mOFig6jqISlewFrYA'
    'IP7uDG76vUHU2aLO4xsSrPjqCMbZ7F7Hg8k4nw+3trF1WDODj6J1AAMz82RlZUVf2Ort0bv85i0y7qCMgSRG7aUMcaJPcbAcYIeC'
    'Kwwd/osMu82IPh+MupfYYVbLNlC0S8zj5gP7G2O0O45dcwx1QKJEN6eopS6a6EQ81hdNWYY6UDbECqVzYxXUj4bq4urfNGqHsG0C'
    'xebpJxvhdy9uXXlHuoKnxqV6i3NlbPKp0C5RF/SGxt7WT2iQxPYTqVc4Yo0D1IEofzYPGH/S48OHku6t1qtnOBDgayXQYQLzy74z'
    'RJQ4QHYFUjS2ayROutBLbFDq5lvROP+KeVERq/Xb0BbInKV2b9CPj0YD7Pw7PBB5Xf+i+SxFiikSLVlfCTRM+DSAnuzvoSwGQ8TU'
    'gyb6yXX0mRwqVhwU0bnLt77Qm6+SCvSZaPYunbDJJ91DIi62ubXQNIpv0bjzgdg0pJcHl1PRuO6IwDC9qDLuDlya1WHrxcqCsXfh'
    'KDjpxIYkNIUmvSO056oMh70usB2SUDuA5zIvOhQ884YY7X2qV6+EVeRdbtb3lGPiOS+i8UgvQTMGLOONSqyJQev3hUBtFqNCQBp6'
    'GZoCvmOEFvhTAhQllA8QyG9dv+Sjhnqgo5AftWL8lXQcECiNW666k0HEcNSStCQjz2i+onFSgiNKL4+n/0KQOWAVYfkuxF3oz9Zt'
    'j44Cwat6tfId+q7QSx2Kv5iMo34H08yuPilitKbLwYgE1ugjbtgwCZeXZDV3m2CgF6pbmYwHRY5WlmCE/jFfGu6+qdQru81qnQWn'
    'TZCNIgytzkdwlIdBiKYgSgymeTNga/LgeL+szge0gecpGRYlENTdIEPqIE8O82Hpz9z9z6RJUPPRxZBF6Ck2+NSNg7fRZbcdUMwD'
    'QNoVOoT9DDLGq73z3Uqz+m2NUt+yA9IXdN7J4QTnCoGOCgXni3JuV74zlxYYhSH3m3ijs77ega+ty3JudNmK8mtP1gprq2uF588L'
    'FGoNRP+7goGfjCf9caKgKfgN+S4F/3nnSezDX117Wni2lgWfkth68Kv0Dq+hxteDZIjWuXQOpgY2ovbzZ61cwcBffbJRWH3xorC6'
    'YgYg4A9Hg6HpqoJ/JN95/X/aetHqPJX9f7FaWH36FFD0JBM/F58tJI2fYdzGeHrViwtchPTd4me9k8Y/4F6gX8L/FF91272YgSj4'
    '79Q7xFC/C8JMYtFzsR5tPIkc+OvrhdVnG4WnG1n9bw9ghq9d+LvynYef9ovnF+0LB/4KIGjteWEtE//X0cd4MnTn9y29g96/iboj'
    '9cn0fy1aa224/Qf6AeJZ3VjPgN9DnoMWvaL/B+odXkaien/UbUsMXcRPn0eCgNZwdteAgNY0hUr8kMOz23+TEBsdoGN3fp9HrY3Y'
    '6T+Cxb7jPKf7n+Blv0efDXwXUJaebtvDzzPAfrTiwF9dJdyvPlvJgB+Nxin6rIzGwV4MUtMyRg9z+x+tPN946tAPwl1dWym8WMmi'
    'H63E99aXToF9qD+b5buxwaXF+n1W0P+HBta4/2e844vNDMGpLYo2oiTgFDS8KVpG+V31Bx3XDEUeZmDo5XjCzCxXyF0ggcDfIchb'
    'V/D3I5x0E3wPAgn+bQP7ucJ+A3sa9gYJpeOAWsiHMIR8gn8vMAAP/B1H7Y+0QHO/n1zTmx7s2fgX4w4kuTNEFrM57kV7NLjpEGxm'
    'fTlr9YF9igfDXkw/OjEKhxHemOUGfcyGBbIe/IZhYJh76ung+noy5tfRpNPFcM9YN0LTIHx5CdI9leQgHqo7xBXJ8/MESuDgPva7'
    'F1TzCr20oE/QGv0Zj6k3LdjnLto88lZ0SZ8+41jjMSXeworjAbYTR0NCV4IzhZDjW2ofcBsj0vWKAjQNx4MhYbDFn/rxDUh+Q4J3'
    'MWCP6Vzc/xT3BkNCPXKS3CVeA8m+jWj9QwsgjvP4gCuXmSRPnCmk3x2aLDWbF72IOF0uuQb0IrCoiyVbgG7sPVrZEG0Qo+lzS5Y+'
    'kqtorNCvAVwMsMg1uiEWcigqIHIoUTtmZaDuaaZeRmqIcJAY8ZPwPUFQnyLswjUgdNS+bTP+u/rXWPUQZGWaqau4120PhjwLrUE0'
    'pm51EVNXgxFNWIe61KZPEe0Y2Ah3Auk2jrF0MvmE369bk16kyGiA6vVAdTH63CU8XA94FHrrwFHArBMSOhgRJUbETYCg4KRNcLtj'
    '/YlIlqrhr95gzGhsc7d/TxmlseP0eB0lH2m+4QCTOCAjIOA+rbAWAroEIZT7xNsNrzO99fBcdqlXrdGky/1LeFQ3atlFl/QW4Cac'
    'QYPoHGTvy1hQQ6c7Gt/S+uKpgMkfKGzojQixQb+ZE1wPCfNoTo0VYEKvmOqSq57iQv2Y18ukr99cDwbmdzJEn1b+DSeBj7wW+Rkw'
    'c8MU2SMUd3u9CUfo6agporWm0DHod6F9GjqmoODR/p68s7BrcS/+1FXrZPyJBqtcdqHd5Ip8UdXqIgM1Xl3XvEfBPkb9SPAsS78Q'
    'ebScOt0BDYNSCWKjwNEGxJm6Y5qCzmhyjcjqD7pErVEvYrqBFUpLMe71NGcKcK0ToQ0GI/pAPYJdzqx3VPnQFHX7LBjkLkfRxUV3'
    'jNQLa/+j5jjMy7uEkcFFRC11FKdSLeATnI4HN0yttESvu6MRfQECGjJHm4zGvCaBK/QusEt3m7/miCH2eNrqmIghS6tLTrAQQG+V'
    '8lOp1FwFSm9Wu9iLblUgSx0xBL4nWBXPKuWTUql0VlA7kHqAfzGciPpBIUBUw8pHTgcGaXXYi5PjjVCsKqUOgzlAa0jKOktkawKP'
    'wP7zK44DkAoF8EqfunUQsDlu8eaE/pUO8abeT3GIt5W/ziFeJ/P+1FDC3tbcuAO2GRN4wKSEMDBCAS8d2yv33/zw/9X64f8yPdV/'
    'jugAKed/ZqXW7d+snJl+/60Oe/scRLd455fh9+9zoYVZyU+f3zRb+Vfn+O/vB7Nm8k/r/2+ziqgNpdc76P7kOADS6V9Dctz+Z3v9'
    '00y1VWzACxLkjeWV6iRdPaiL/hgYY0wz7V/GqCWCO9MXx2DB9+3XmdvZlb7KAcStAZmOKO6B8+u9usVR0r0Xmh28jYZ5DyTdl2gX'
    'z/xJgUWZM7KSoJ87dMUD08QlKWWUW4w9/VQx80VGTe9FIK91qjougBdOnsKzYaX9zudAXxualyiAiWih+J5vEl5NLmwQdmUO0Zsk'
    'lDlB2PBYozpyTk5HxmfZzTrhu66aMqA/iTKmcWW4QXnPBgeDGzesvqtRwpCHSqMkr0T1LApdkrBHOgFpFhFKVyVnjlkS357okjeu'
    'uwFd0WP8BnVPmeRvnFRFbGsXDeFQhJfT0kLpgVTD8uUdTtdNCW1QKuP8SpgyHrxRlnGr4aaobbFeQpmch3JmewRwoU/pAmylCB8t'
    'sDthFyv/+lQQKMM+s7Q1euJeKskCZwSMeyW8jE9itrpKTfc94TAecn5N4Ytpg1xxYirOB2pxT/Rpk3Zoon/82HV76+k1G/eTyUhd'
    'PPNChsG41fl8wjX8JGGjhCLY0g+Kj6DdxJx8ARy64wIYNcXzYucnSs+1v1fgBC7X3Us0/wzYVoEDLC5rr95R3Oa7PCffmF3rPi/C'
    '/TYveYrKHMqs7EQbYCrchGeyjMe8+EI5j+aDDkd66HGc0lWUoC1iaPK47linZJgowsdO6WTVaUyznPSoGOkLdkaZNmzZCtjUypnM'
    '1yAAhz67JMFLFsju025ErpL6cYeWlZc9lYto05XAvexLSfO0LEtd8iCXrUDv+fVOgKdq+Yk/nAVlXJFmpQZp1qpU5taIERidee5T'
    'Sryys0bsVxOLQ+UhsV9YT1BWFodI/SV+JaP5UYNKkVC2BcmQjqbdhWk0DWVT1LzywapQgpwPzswDxRP0SiJu9ZMby8ZlIDaJrKFc'
    'E2JDZguKRioVhJtPnrJavzst1U5Lp+GUnuBnw3natU+YAzG3dxqSlWBmiiHTEqbzTU0qkVwJdS+W0esazg40rybtAKZWZtJMF0d+'
    'imYHQcSn082x8Wn2e41FY/C9urFi+mF3f96pLCO1sX0Ml4ffRqslIvxQn6R+CdUUivuJ18A9XCVUxkkL2IjkVIYc+pzSVwii6Fme'
    'KYoamVhVC++LQMQWVemDmzKSs5GI/rf/PnhlDTdSkYhgUbue8/ACerm6k0vIw+qDcmhxjk9NkEeuJ5x9LPlVBdcEjFU6Hei/CKyh'
    'BLxUBJFPJkG9XYI0CZ8krWQGelHElbG8UjLYJ7Mm55YnQv+kM9T4tCFIoYHKFRsHyHxl3ywSQHbh6OQVuXP9khAYnq/vQ1TmOCUi'
    '5o0Jl8a8IavjEFuq0dLRWemzot3MGf89o88Ke+KmOPrV0DbZxcOkJXkV10b4lblihogI0hbG+OIogDJE2g7fI5MUXj9qvq/kIifJ'
    'gaMZyH8otToqzgDmKuIAgVDfhIc4C2yJNkL/YNYgwMVU3B0RBC/2sx04+HCKor+Dyoec5FJj+hd2yVMUiNF8g7ExyusRhw9+EVTm'
    '7jlfEU8n655hXjwd3GSzt9xUTBqTz8lQDKpil9gvk9rA6nOjtKiYHCbh1IrO1LNAIqjZIV10KJeZkVqoX/fEaeH7G0HD7pFC+9l4'
    'HMA7o3QTkGMIjJBngKsCvM15gVycVfroC4HZySmbYRISVGADuXaFp26rw0uegwOKqCGZEUFMa05Ql6Rd4vMIbr0c4WVmTBFLAWie'
    'RKGG1KJul/SZI1wIADEdBKC8iRTPUM9STJqdq8nmThZ+xOQ3LCnW3IgsydBCC4mncwIOAWQKOIRmxeMYsMlO/jqcoQoejva9aFCP'
    '10lBFw6nnqHvTMrVbeIMY0H0c86Lzs0a+YfNBd2jXcoxW4srkCvyBQbKm5G0XWYaDWj491ypOVQubtWk3iruiRuI8eDysmdvMwpS'
    'kfXRLi3jFae9ODgeGcdjJV0PGVMjlxfR5+BV5T5m2nEu0jZNXDhVN7RgHDw7s/VRS0Bp/s6ClLef/yw94607xYR+eofdz04QwDTb'
    'VEpRc7uRE9527Ho+1/Nc7zuZgdDMyL3QVZllFmFz6qhmGRirUkgc8ZjO7CauOpcLccFMEBxs7YGN1gH1re5lB9Y0hdr6L//w9//B'
    '6agpE+poXB84mJoA5TjtC1B/+z9YUFSmpKLEZUISY/CDs0E/WMlwNXtX43hIsusc3UPCmqGii8YpnTbsvOTwak4ypKNT4dKIaVJP'
    'sihHm7bOohr4runK7q4UTCPNlNAfLBqi5Vu4SUX6IKioRdrotnqo0XTNBDxA6jovcUDtsC0BbHhy85Yh2VQ3E7LNXMoIcwaTHiF0'
    'EKHuKJelG6gtCxgl5dzmij0V0ej+WnbvhinRDsILVbyKP40G/aXtH//X/8+LQzhnsWBNDA4yW6rBfnCYM73r0xsWh4o8PD8alOq9'
    'DZHkhrPxeg9lZ6O8dXmnc6eyACtn4smTzfTLzYxQPWqRYOSldOMU2ssR/KwWwURoyZmR0m8DUOhLT/F0dAr/kUemHLxcgldLIcmO'
    'FMfFD/JHEX6IQWRFAJov8WGou3QQOieejipF78wkwlN6Dh/MjKiDUfIEKbuXlnep+DqDPkBGUWxrqXuRx+hkJFzAjpmrYmLfXPjF'
    'qrQycSyi7Wza31uw6zndnBMNUA3bi78zv9V5skEWxmCmVR9/as0tZErQpYXyqD7wxHRlBKAkgqvMIDll9D/gPcOXkP/0eqIMGxDu'
    'FYk+iR9yfeapOfMs/BXBbb5CUHJD9GRE6OEbVSF9yYA590bMScU+8R0rg8abarXZ+BPG0Xm+FjLdzD7CzxZDs4JnZAdeSQuFJBXy'
    'F3m1psKzGPHuLkNcy2FVHLbznsSpRYO3OIKVLBxowPhJ3NysmapZQ15AtlpcutKhES59VY+P3MDjwoKydLihtfXwzmzBvJ0UgpwN'
    'cmPuwxYLhkKBRxaMPPLPGHjE8JNzZmUZ8UeCRSOQeGbG/7JRSNyLL2bTOhjJjDho5aA9GiRJUZuaaQdswCbGBvoXYO/1WOR//lfN'
    '3o/qtb1jClMrWDxl52Tm8UNQrx7V6s1/Dn6/AMsC0no16fY6AcjuZTLg+vFv/qMy0qMpPHNPjW+joTAKmacTllcZGXzQaq7Iasw3'
    'SXvIbZ3An7MwEA/GfktZXNgvjAfZqrMdhZszTMNShskM0xomOzZb9+yGM3j13C1r3ew7nqWf7kiCaysfFVrAXqKTlTPaOXvx7uAa'
    'Y23nW/AqlKaAUE8ZFXmWgP7OAgX1LvJkBXcR0mAmImJVxn5yJ/cMMg7EXcOwsJvu+EroNh9koWwe3bpfdysNISvl5sSZ01jU1kvJ'
    'WNLqbEpN0SlZlvhEyjvYtmsqoho5wY+AaOfRoVPny2J0eicUsh5ZKGhfTxfYfBZh+GSB5Vy6WCiJgbxomEdCinTmkoUNnSY2CZGG'
    '6hcvr+hN+Zw35T8bceVv/ydY8K68MVNa+VWES5sZMe3V3r94xLRWZ6FYaUqumhMl7dXe/VHSaLw/V5Q0aDAdJc1sEq4p0cwAafy5'
    'EHiVN1XdrzN3+1PFS3PmKB0pTY/hi75gVS64FKTLD7UlwoUp1GDySLQeCi5g+hI9b62OEzts0dBhbrV06LCM7xmhw1qd2p9V8DAr'
    'uujoYWJKjal5ZsQwg4r/FjMMY3O9rx7s1t5WMXZYtUoRw378+//w5/E/P+Wi9moO4J/Jr8r8jq/eYAwwhLfQ+bxahDGs2sEQY1BF'
    'lxFzDrvqaZRzrtJR8Q4fi1hO2EvhY9qXupuQs/sWQc28y0OHcuXejf7worMWNkMJfSDkeKrr39lhpwDN9w91B5Tl0WnbMECgUhWv'
    'PrAcHubzOZK7QPZlH7NUHzQv+FWvDIoWeLh/dFTFiPCv6pX6D7/+QamdNul34RDPjjBIeOP4GuPKnBXoAANybV7vQRh5z92NRhGm'
    '8KEjGXrrR5cxUtk+gMjnkouiBm3Dc9O1FzUB9bD2jpT54EUYlLnQucpRnGiz6jtUAqIVEOrRHDip8ux7QANAycIdgNvdJKu7Bd8z'
    'wDYXInTRE9uS6IBqTu2hJ2rs0Ov/St7bLceRZGli9/UUXpyazsyuzCQAklUsgD+TBJIkukCAiwSLXcOiigFkJBDDzIyciEiAaBZk'
    'cyHJJDPZrGxntSOZzdqYLrSSzEa32rU1083sm9QLaB5B5zvH3cM9IjIzwGJ3V3f3TDeRER7+c/z4+fPzQ5z0FIE8jZujYBhyNi6o'
    'a/TgcW+nrw5eHHX95Hgm+TWKjkUS1nHVrurvZK6Tjen+tl8cqaODzWIuwtr9pZMgPcPXur/Bs97gqSr1Wru/YZSm8VhK8UiPO7uD'
    'wcHeN32vw/rrjaeZCz+E6uzuvzh4MfCWrPszITHVfY0DzuBk+3p2gBpaA7XXO+oflta6vK/QpJTTfR097av+/k63/kZI5GZbW56O'
    'kkttIQ6mQ1KU9VD8/RCic8Amha46ZGRLWZQF95AvSMT9hPG+zz85zLDlu8lwHK9ETLpe29XRnXQmgiRLX0bZWbNxs9EqB6ZbdsrC'
    '/33npHplW/U6/Et3G3voP3Ynwd0WR7UBxiTVX4onnxxlicGRYPsjghivvy1zkzT/udGy4LKu29AzacKy7nZAA/eyvoGkvJJS7i/j'
    'ZCiO9+XYnx//4f9UA5mS3RgYfvQgAourN221YQwSlnoY1US0Ki8fje4xfRYPg7GmOoaGdYVyu9WH/dbLE2jotp0JGvvCwVLpo2pK'
    'HzRKWQQp15GtGMtcb3Ce5KUDs1O6I8eNObV5LsdxAQDX91GcEy18NUrbWhl+oQy3wt0iq9YwOjeMkRrK2nXUosyQnjby9+5cjPPR'
    'vZN4mBdmxDcal2zFJWA9n0H1uYJBwNIS9rML4WVn8A9+duivutYrd06ddY6D4akcMPn92fuUj9IVl7qTP5cVjeUP6Vi5E0DUYPGj'
    'QuUpfOY7NQ2l6JRsSPOz91Gp0JRfY4o7fmMOPDCZPpwOt8+i8bBJEHas0eKY6m+1f4ldRg83cKEqLsEJXdiYvdsysQ13Z+/Umg5a'
    'MJLYZZh1WQWDdeI4HNPui4dMoyJALCzFyJiI8Z8cJeMfOx/eUYHeCJDSGbsaRG0l6Q/sa5HDlpEjdyiCjRnHszNq5rfqaE/DC3MQ'
    'QFWKkYNeAot6nVHbJT3hjNXtCVUZTU8W1czCOD8XJ1HwrorZv0wdx9mZIwFAHmBeSaLFxh2wDe/22O23zLW97o90jxP4wXNTueG6'
    'CY35tKuMsLpglCJJrMflq960nNoSdnJnQb7xwViKoHEweVpeuQ5yKMyIb1uslCYCqC6RJXuHO3Ir1i3C22ugnOyu5Rl18Ut/xpgk'
    'Xy45K38UOvVhv7fT6e0dvNhRzaOjQeuPQKn+Y7IILt27o96jvT7vIPt+7Ad0AoNx5zxG3lraTKEhcNS0SRuUvJSrDy5g9ycBLceu'
    '+g0DAPHM8TRI1R+eAfxZMEvVKImILpGqhbvXlN1p2J09lPTgKh6pZxH8t+JRpvoQF6chkEPvP75CX6MkOOXAX0ilsM00z6LTs5A6'
    '+Ot5MI6ySzWKkpRINZKDw4teSeWNM3G7aHW1Bevo8Pvn/cPBwX7PFGigzvd5xA73QCpg+FYFyJCWbjpTO5hyWp+mxt2WzC9FNN7L'
    'aLq+dnN9HcFxND4xx5j+IO6DkaMTGWOGHHebaq17t7Pe3VAJ8kWo5np3DXf1XOuo1Vbwd+oN/2qT2Os4i3DtlHC4XzwDnOYp/Uxn'
    'IXKmhhkSpJj87sSSksikvwfI6Ekvf6KTqzS2xyHN7p//o3qsN8W8P2XWQS1QMkAEUsVFBI6HMFHoudNk7zhzpJ9rbQYXkiljOA2k'
    'RlsP3vhVOJ1e5k/5J/07CCbBNDtDi7+MkqDx2klVrxqnczsvvZQn+ROzlJdBMsFKSAnH7Rhb6JEv21nLxF2LLRhh9+GrDWct9PPL'
    'fC00Xj5pHrxxeElqiX2GX/TPTnAeIRXxM0n43BuH7wpr+StZsbOWX+VPzFoecaJorEYjl11s9b6Ea18e3w28fbnr78utfC0LtyBx'
    'tgu/6J+vA0nl/E2EAMuouDFDWm7qLWYnf2IWsxOGMyylN8/OqA9kGzkX62X1xtwOvgq/DNyNuXvH3xhnMTxePm09PAGQBNzY2R/9'
    'gJtMoxB5on+lE8gfncWTIC2sLJxMCqennz9xtimL0jPGuiRKZ7mZrnqbhreDu7dvedt0y1/Z3Xxlg3jqnh/+Sf9iGvlTmVTjafAb'
    'XtLX1BWwLy6foYQR1F3QYf6kYkGH4Th4Fw5L9MDbKsK6UbjmnaHCVt3JF1R5YJ6EcUJkLz9b/Jv+OBgTliBb914YFpYSTIMCOejl'
    'T8xSBiDRtI7+uxny1xuUW3KEvrrzxZq7Nyh36x6hDYe0TV3KhsEbxBfOwvHYWYp5wnSACD9jX+8cjQfzlFbvryrNwtFIdkSvapA/'
    'sRsUj4dY1U5CBDOzRUYWbtDwqzujOyPvLN31N8gh2Ho8B+fMBBrbZ4TfxHTOiN/Y185DJnkZ8VYkXD8kFELO9scJ0tn7W3de2rrz'
    '8tZNYiirtMznSTzC5pUoubd1d06O7x5veMdqbTFXOne3jndjP5ieOASRf7o0j0gETYL3LUqiwoqOUejDI4GP8idmRU8SUgTHJPLQ'
    'mgZhQKhgTlb1tgV3vxze+cLbtgJvcpCRx3MpHQ/f6CfRiUMoEs72/6sICfoPg/EM1QyekNwVF/FwCkmHSwuYBe3nT8yCSD7KIJLh'
    'gJ2HU+d+wi5o6i7IVo+p3iJByyXMdgGZt7ScGa1mu6+dMjSHId8bqcBIzVxscQpXFxIS1YBEp5OzweUU5SyiVOTr5jGESMLUaIzk'
    'jS3HMyDR/XHDpu4S5RJzK5MZ574rWIpZg3OJz4y3Tf61NeToR/aCwk9ERmIskodyWYNu6s/8IawDPCtcIOo4Gn0HBJFxvUJw1aKF'
    'J12nqvmSB0gVC7At1s6OHanaSbHLn93HvEyKp3NTc/K8OyZxFr5I8pdnQ4JNnl6Jc/E55wrM02g1imJ1g9ezoNmClyK+N1q28raB'
    'w8am6pHw05+ejsHneM15jqNpeTWrV+L1f2szVzeAaeOxE1+BPFSkYQjgtEVYPTSA3OTtbtMs8lc0I/OYurKZtB7FMcntU3HyRb7Z'
    'pnbL1SoRVAONS10cKmMYc5rOqAs041kV3cTOIlyAoIkgrgYEA9kzueUgN0MXTXJuNBd1a1Gb/nYS/QkE9+BWTsyaA3h0O/8squZM'
    'cqsKzFq51VoeaI/GcKr/IKB5To6F5Hfo8TAMhpJX5A9Gn/7EOvONQ56++F6I+57OmMl3m1wxKiAlcVh8yq6CJrnmq9dtuQF99R4G'
    'TWPiDMdXiG2ZxbahUmtcnGaebJ8FOqOo5OEU3X4zz50Jrd5SOEzOWm1QUeRKfyOchcu7a7IZofHUPMYQDkPCdtNG2ekQF8GzOSo5'
    'bdpsp3RacC7ODTV8b3CkPunUN+jHCPzh7MdN/9r7etnYF+Zjf+XlxEZasPvus5pp2Csz3NTJzVzOzrzoBj/Pgt3CNK1N3MOWUtyQ'
    'XiV9kDslWGteEaREp6bFVOb5NTbcABhn9XQMJeQVj7tVKV5NNmROumDalfO5wvXjVaPx+uHOdy168NnNqK3ybK2twnhTp14yTZgz'
    'IU+Lfgy8Fr7pnuZp7fkm3gStGP8MzmkuRyM363Gyh04SH0dTkH0adhpw8mcRrQCCgL7riQt4ATERs2H8JlxY+84V4/C5GU2VJBVe'
    'qJZVZEgB7aTh9TIKvX7q9jKyMWEobR0hQX1bjaK8vjUvIb8aPznz78YtvgSjcBsuIiSQPs0mY2roIeunDAKH7LySL167gcTYAg3g'
    'UE1ujrwIu0j9udrgSa/5+d4X9cx+HzlIXk3Qg/tEM/bXqKnt9DeJ8pTlhcxcKwf0d+HVCEP6zxYMOvIHrQiE1i5wEHearhv6p9V0'
    'NIeRc//247//HxWyvXcIz6W9Ijl+Grs8PZLzrY4TEjuJ3pGicHutcC9nZpYTAmWw3CXSW3kjYltyF7bmPNRpxHKXfdOYmaQJTtGp'
    'VrNE8pC92PU6/h4ZeJoehOJZ7iToDeN0t3CcRVzpBLX8xt7QzOjc8g3LM6FlSSeR7N4lJuElQDPeMm771gIgyJJ5HT5SOAv3y0Iw'
    '58gXb/0vC7BYCAcSCGmFxi9Tyelw/1PsTyjtwv703E13C1aYhPi+QF0vgrRnMShf77X3EbjpI6YWqezVrYDNjmeBZpDPhcX73yIS'
    'OL6weugFe86p3s3aHtx3DmopfwO/kkOzVaYY//KPf/tPrmiO8l7wHAFZuHVnLc8d7hOHT/x6D8qdwSszMb8EiUhG4rzHMpFxBDxK'
    'oL7pwnRKF0Bsq/RtNMvlF3ofSt1cpFoMx6OKghWOMOKvPt9u6zt4LbHEc4imheWk3MeSMgGl5Q2wjmjKbG+suA5wxdylPnB+WnmQ'
    '6u4N+HPVSiLmp9rAkM7ityTcsZj5e9CWjLChp+HAfKtGkRH7lfxhOaazX8e7+0ffdWmXbp7SJu0CslGcIJ63snX/107r/rsVraXv'
    'm95HZgiVohypWtHHq86Pf/N3P/7Nv33N3y4aKP2cX6sCjl1VgAix01MptgojSxlUFUj9X33X/OG71mc8Ro0hHM/mev1vLu/5U/n2'
    'A9H5aXQqRV8tUWAa8/s0AfwOeD9DORyXvHfdpoWWpJfG4zGhZ8xV296r4/AsOI/YBpyyVR8FylGPlR7QQeNSHDra3QW4TgA7S+JT'
    'XN787CwzDhuZcSrmZ0F21mXFrdm0bPCmPJ4E75rr7TJHVB21TqrjL9W65Wq6y+Ol3oAEfwOYjq3SKWg+O27R1zoh5EU0zKAgYYaf'
    'q8afNxaB+cY0vhA2R3t6Q4mL7u8JnDL48tXTdDtmuu7q+Vu/WElOUYZRMI5P5yFXNnGZsKvbOaql5dBGv/S+2Sp8MouGViEpKWry'
    'DZshc2NWqQexDq+6NIiGzti8YN+1W7ylPUfiz96j74eSDPKHHxriWBwgo0arcXXjwY9//6+187TSPtXeUq+U12c8C06i7HKze8f1'
    'SV6bvdu68aD52XsDLRkSFmNJcdsyCR1tkpmimrtqMfnAPOXcdljq2RUJc2TfPotROViciH6+tl0jrVjjqUEraxStklpqYPe1cdsq'
    'bosQ2j05peku+qi4S/nUZGfuL75lK9Gv5yGRQm04RgH4eHipfm7sQaa3E46ucyMoFSg9noB7028CSYqSd9rl52j28CHM4e4n+nZV'
    'FT+xz91PoBdwSiJdDywl2RISz/iS/sCFzpbyxL4UvuTxnMYekdpG6lAzzQKi3MMo0VWgR2E4bhX0rUOwGyaUBXlbPWQ3H7WpFomZ'
    'iieLFoVlprO3ulvDhyfRtLnRXWvn7Hete0czYC6890sLm1/aabXK6GUuSFlxmSUh2O4J3BGmp7979miF3++zRE8sSsOmPBZ/dLMC'
    'fZ0w3ZH0FLp8p3OeRWNH0bFKw0yVbHyly0EyfBCs1jm+7KBuppogiKgZrK9ftjzCFI8UHnK9nwYJRiFhfDhkAoXnXXxsBeuclNDy'
    'BuDtuGB96TbR0XdmwUwt2mb323q5q60D2oZmEiIVPABe4C0MNhqwJkYPjwV35FM9rPvWnsT79rC6r8/j8XwiyG8RGKDidbRsIyGB'
    '/K+Gt7yhtU2HhVqs6idu6SdOvTw7SpLE4AzN8Lw0Unjelde8pWxBSOYzzmtUGKgwr9aikYumzfsyj2UGtS5Lfk1uZ+x1V27GEPVi'
    '9w+o6lONOj2ugdJ1NBkHl4+y6SpNgVoh43PDiTjCbfc8XaVjSKs8xlGP5xoA7Q20h3/2oUXCT2z+bPRQCJVt/Piv/5NSz9HWCsWm'
    '5ZKK6n75wmuP+e/+HwXnIFr9Bw1ap/vn9M6xZC4Zp6qeeu4ZwZeNvBktvXWF4YrbwF8/LEMFWYMZzkSF4f8pnP7Hv/kP2iK0ycZn'
    'LzwQstiINM2z3nmQkd4Ai+ZBYhzC2mqhC9QH+z+5lweehwDCYQOeRV5h0ZmLyAzff2/F5O+/b/jWe3pz6IfU+mXM2GhiP0f8rMIT'
    'JBPsyMCusim95Ygmv7XqnSftt8KXqF9QxDc2LCr4H3EUxDY3K310+3ajUATqJOb7cumhsBIoRA1PkEfzFn+kR5Oe3WEcrHORHAks'
    'rdHbboCrT7DQD5IhbzsgHuG4gxyt/h6VswNyZkCF1IBeBrLzJbRJRnSzjp3nuxCcV+zAkg3I2zvAL7a/c6cI+2lEU4Kz2HkVDgXn'
    'HbQglSwtbAJ/19Lf19mI8mnETToSinq8wPVHWUbTGZcLoesltxRmyzntMNl+8yfFG1fX9cBr6DsgfOIk0zVaWzzj0qNF78mDWVak'
    'IPDimBn3wjf35EMpJIlaZdbuQOSldXVDffYefxFNyGdjj/bDRsr7RXQQmTgfuF/DYtFCtZ6/U+5jU0lGhn2ACPq8MkVe50t8F/wL'
    'r9yRpxzwrcPTaWe4vBfHcec3TEapVyPGY3NPLs4/EuKdxpPQaYdwJTfYW3mhrRUU9ZPFxHFRvgFNcbyEAwa1QDOLRNRJ6knPn9d1'
    'j63YN1aLnc9erUvZbz2jcoqDAowdSl5dXiWfn66csrFRLLVSanL7dl5epdL4VvrCtZvdZrvZv/zj3/07N3+BW9uiYgnRdBRX1hYy'
    'DaTQjmMgW1DuxrRP58c3nFPgzFgfh3/+j6rytVtgqc7MWa9xwCVl7FCAxcOaFJka8k/5K3kYT6WuMp6LA5RdZdMpkOLVuaqiIteh'
    'IM56o+FHoB3lkja099xpqZzJAtrR8N+5mSi0WFLKY1uqZLHKxu5uhiv3QAi1EeoVh1RUMrW+Zin+TnQe0RGyVAB4UYPO0B/VRGYo'
    '/TVMo7LJ+IEVWFLl2KQ96uxbpKuBSb3nSbwtWYab0idFPzVkKypAeKGDmnNl4PPLKheviksDR8pW9a4MioRzzfOEMMIKZ/PFqJyI'
    'g/YCl8E4MRfo8ALJsi3q2qogGy0/kfvWIuHQiIR6iGpRUCTBj5IEx+FJTh4c4wV74hvA7d4szJWzhJVo+qWl38/ey7L94lFV7CaX'
    '+CoYjfPyzp2tRWXafGnzRtXFT14E7LP3puFVzXpolRxnGc/RF0gEzmV1WV2+Y6BHfzuge+DfJFXyIX5R4kA1VuNzoZwPVXIcLogL'
    'bHF5BNYnM6/ebV3yq8ir5EKD+ZSLh05pr3ajApEa/NQDkFd1F0zOEZzdQmkuXynUs60meZLJyF4JwG1GgCMkPxiBAu4cPCOikYaJ'
    'TZFWxWhyz+5xXXVOs5iQdCT6H8tmZsZ11TAWcVF1dSMfxCYMwTFQtLXuir8IlL7FQmiSDl1wqYI84hGXkWlp9lo5Vo2tj28Oscrx'
    'EnCaRbrmvvnxMvjP3czq0KXV+0o1ukqLrq8/11GVFyvEuR1sftzCggoWsDfXIxdvirgDU91zx6d1uZvzNR2cyw7NdjlFyx3b0X2r'
    'XbPwGZ3K/jSdJ6EJ2EOqvnD4iXeLmi4MFHSDXXIUOY2de6J8Atr3e0suCRgo0r1bkyg//KcxZ1Ti2yLtmXoai73/yoX2QBymVWEs'
    'dghVV364pfHCdVoa19xCW6JVuJJpamuQ0x7XNvcVJ4l9TNDKmufO0sfH4xWiML7vULPcZkI/WviwgIXeCCQVPY7ehcPmOpe7+C9/'
    'L6bVT/6Ecvz0trf7g8Huo9293aNv1bODnRd7/T+RnD2aVOP+U4LzoPPbuLWGTvbb0HF39rciYX8cvkMaWPZBH85PwmexRMJ5sXv2'
    'VrTwfAAnmenpJsLmOIWMHUL/xAiJTu3Ao8EppsETPJmnO9Fk0w8UTObjPLYuf8xJFPmedtN9PI8GqK+j2zfSiQ0MxxToJ4ac6JFP'
    '+Z93Y4zuXQabNZkPHW/wC/fm+cx88NNzTWOnfFstZ5P2q21I9YJCxumK/NJOqEqAnLJesIibUVqm9h640XY3u+1tcdvZ2LbZpjZv'
    'TDvfh7aGfdsD5ZV2x9mqk8GagVDKXv1bnd7ihNgach6kPDkGRZq3Ch4bj2mq6mfs2GXS++/xGTeuUgCwXF/ps6/rt1glARvDS7uf'
    'f/vQttb3dhoS/SlOCzJm86nRrZ/E8Sn94k5ov96iLJz5YueSxCX42IwvSaoHwt+UC0nzMYtlXHjRWcRe/9f9/Z3vXxyyReosy2bp'
    '5s2bWArJGDxaMINTWTy5eZKmGw9HNMb48r50uXlBm/8Xt9bWtkgw2rpD//1ibe0XpoJ5ehHMGnmQ4PjdHma8hEkLIDpsV8XqXHuV'
    'AVh+RwRjDueIYqceqb0UEVyymDN0OcttKxJExeSAZKpudKGe1A8/6OmRVDIWv4j880arULNPmrbyT/jat+RMmi6xeLjLY92L9QdV'
    'BsEWvUpY83JnhKcohEWP8w3Me7OjnrFM6uiFabFWqn8Pnq8OPgAOSO4vAclCMEjijgw507wdcgpwF71nrwGy2WKQzQzI9LD8iINb'
    'ZQ0NtxdzOj8InrNWlSNkTsmE0v48Hd9zwuRyBev/7D8kOrVeIFF6ibhBpEMXj1P1M1yax+PccLL8YXFp/seaJSrlfmweslVXJLLi'
    't4aFKu1qplmE+3AxTLVPhwqi4e8bqkVUgUBgDVYGVbyHi+GZyxHOx/7DxTB5satSiB7qZ3uMtGzkw8Y8BKqQ5OwEi+ZZhbVMGWao'
    '2NmGjc6NQ+bamfAmNJ6IRZFUbHwo00cwIhKub+MVZ9SHHQP58yVKFiIIWjpRsqWKAr0T9o49jpAn6HkwDU1effb3dEoKFDtbXGSI'
    'Gl67isDCaVx7mKVlBNxFcPfQVM6o19ybIeOfSOrRGEpCSCYc9C9Ulw4ssEmQ4ncazjjRGPIzdY7H87Dx2vGsmHt+HeYPvQSsppeR'
    'uH48z2iubK/mgSU3kozMBkyeTV5VOLfULgcMf8dXN5kHHamTZb3W2kqEWJqtkwufgAKh0+56eAqY6Z5HUoaF0QN/21RK3LMDR/mt'
    'VWlSLGVe/JT2jcMEoXNyR56mUm4OKnxGqvamQUtPlym3Z8o7jCb0gZ6n1nDKTZma8UT0TFgHKrdjD1annaMllRtDX3Ln6+lP7U+0'
    'A6+T2elVNGRK8BrpnYr1kgWQLV+tWmqfj1xXKxjmET54Fp685Vj7Tz/VxMWkcAJPT4XJVe+5fmm23WGKZvcNvV7wPV6ZrzWNrDya'
    '+itYr2fbQNq2zpD0jaGSy+Inge75p3kI5XE2zc/NsefFWToPeG1I/HkwdmosYgpVtxgy8YzJSFM7xaf57wri6WW0Mtxf2OofpNvz'
    'klJxOwfPtK11j03etmqcJr67rLvqxYeCwpaEyNMaN8ncUGsIjHByqj02BdODf2uGNtZV4JDHGsXjMfLoTeI5KUrfut+X18aNwGyw'
    'qNC5RGNlM6cmfmoNmavcmiAjNNz2QU2o628RXXqbTc+zd41CPXLQG31hAQMeAlrGodj0kFw6mF5qJzO2KS6fuS3gVz3rnLb5U/dS'
    'NdDsg+SU5Tzi37hW8TNcOUm0pARVuSedw6peHSqulLHoesfte8Edip/Sw40rWRFUwhm0SiEl94shTSYMZPUVjpefb3F6wtWhJtcJ'
    'uLCIhHNIFM0Rt6Cvj9KiyHfllXT1w4esEZd5mGPq/V3npufKviRkRFPkk7e3RybtCfJgXiTIXx8SH2BDtBRQgyNFW8KnU3l8fMn/'
    'eo6714lpSnRA07ZOfeLeVKPj1Gaj0I46nL2hVc4OaS4y8Y1zZZf3XMp6gOAuWqQeBrWVaXX4I42GIefOx90/H9sihUV162gajLXj'
    'jM4JQHqZ/stxqzFaGluNdLulYWHlLu7LFNk9qXmhU4Rpi8qboosMmmpPjosIPhsRe5hcGDcYcfIxzk2q0bL+srA/XtjkZHZDebex'
    'k4V8OMV4GKIz9PUDM9liJhzHzmWgx24ZAlZrV5PFY+eq4ODCfcsm8vL2uDImTk+gnNuCcbcw+KqoPTOx6kwU+MhJQ1EsdyZ2zKLz'
    'Fn9E/KsZseBEcCQVX+kXnbOxKPu5Gc3L+XENmsxb8+oiel1FmBMb5FeHgFaG6tHMERLnoMzWwqC7lV/kGPYTAuYgVDp9+zLk1+Hl'
    'cRwkyN5zHkmd459hON0nnNBnxCWNpHblY+hlNjWafh1Mg9NwyK3sq5wsp6Pd9JuIWBdJ7eHY8fwgfEcW2XH3LBoOw6n+4evZKK/R'
    'kfeNlklaM4fSXaxpaYLuSEqTdKE4mdTHcIBHGHkrz2Mrwpy+CZELhWk8lbh+eXceWWbLr/UcTELlTz+lHrvxaER6w0vOACKzlydP'
    'Qz7qdkHbLCwe0nGFMKHpk6+TpKMnYYZK0uVKiWwyYftGt9tdpk1xww4q0tOq2t10JNaWdlcbXWxmY2dLXKjIQK/kHyd9ip/a15ky'
    'z5VRAgemyR96Ve4wY35anq7o4FL2b3MaZ81X+jJt+LrVjqa0daWn4iNXegxxLyA9o/QieIVLg9ftV5rah8OITza41Ty8QS/oJ53m'
    '8N1r+db8vH+js37jdQtX5ouA5gOiPz0DlfNsYs0kjrP7Zr9W2MYwtTjpYBkwjqXeIUhi1sUbkyDS8WYf1g8fJk6mht4GonsQYX4L'
    'a0G4omeIJpwHZ9Hsckr2oT3583uexKxp7ku/cbKiW+rlGGMvmh/uQGwin2v3Ugm7k3gyCabDVHtT24TRT2DSSHWdI6VerRitQ59Q'
    'H9RvN3/QeN1e8TE14vXgO/7gE12Y2M4glwVesZWlrd1MY2QV8dVIfu+rZfxoETDpHNkAN9O0dMbNaLlQQt+5Egn9XDyAU5G81Iy3'
    'w8aItE05TTTMTUXa9zbNQ35bheS11PwsSJ1+DQVA/UW8pf/u4neeSPLK1c5wxEvLftiFZi1ITnNkGtHB1WSYtKHad2hHO6h62O5e'
    'RL8hpJrCnNQ5IXGg3U2OX+niqa/b3eMwyPj5gvTTYizsTkSnampq2g6Efmp6aeljXgl6S6e1XAB76cYzCIBLLwQUUlqX4GQ+O110'
    'jFCcgD9FNdhWeTbeibPtcpv3Qtib6efWRKlS6yO8PFwxPd1IT1H/WjJNr32NqS5IMT4MT2LIxEJmYO31OMuKPleJATlVkOeKN7JI'
    'EIRtn5YRhDZc3lUjj4RJGuSpaskQk7m0jTjnGZkAPWR5LgsOgJheToeb6UXpH2fr7bON9tktF3X13r33zj2eIQBNmb/g3Uw9y+Sl'
    'tw4COQgwVzbl1cLF8PaTzHEMxy7beSl/QiVMXZTLp7l8KGZBb5kF+eC+Ku7f4kMr751z21mvspWnI1jBc0GvqQuo3oc8WJJSYTIp'
    'CLLGAiHv6UzJHxCqfdXB1pWt0jec4rvN3EzKVF3zRO7Rsx2TJrugqVT7MCXgiwoMT9DLwW4kXF5epdArzZu2pa6HIS/lNqv5HmY7'
    'mHUHnL9xk1MoG35SxBLWRCrhoy3t2qJxvwJeC9aVp7NeotJZx0zp/2E3QsmFKfPZlhm1zoKARR96zbBAoHajLZBdd0mOCTrLaOL4'
    'qeHnwyWWdV5ITgP5Z1evb0cch31TtBjTkVkbwAg5VB97vrxSxcPyVF0WgA7qCffGUoFJPFy0IawdOyJLRRRR6YCTPLlmrMk1biQ8'
    'uBVLgAsUi9cOWkx5BZZx/4b8Im1Mq2tuDh2xiBoEru5tJb9zgnqEplly8rBAi7Xkpa/0G3mVef8oIf+OOzP8vtl8uAkHhh94Xj8g'
    'duWHM2rxg9xi/ECSHslxrZtRN8OsZSaeQLY0kHgZdXXoa2vR0XGp1CKSrj1OZPfbfJhX4MDb8BLVXquxgP0u4kX7BkmliAD6N/Gk'
    'G68LqTPQEe2J/vPDJF5JroWp0LzFltSX3Lgw1PgvlHWhXEEIeDqMNc0iITdvq2QobcoiJQfYU5xWL0nii71wlFVNjV8esodLwcMA'
    'aqQ2E5mxJbuf8WEp24x8kC80EOXnUWQFjNTlHwcjs07XG5ibPSBdgBNlorG2Jj1Q67mQswy0Now9HGeBxaEqICBlIXF0EV+cPERy'
    'VYnBX+kJfa57+9ydUkv9ufvTZs7E95qstrxnzmbb9DH65u0Ilzr8jXuXk8WzSYz7RgGoFtm69Q6Wc+HL+MsgYIvkETTkUtxibGjD'
    'ElHsU9uo/P1SWSf/znZl21twlnrk6s73lSsbtdU4KDwsdsSGR3tsu+lZNMq+Di/dm6AF0h0QhAfFXU5Yxi8e225tORXTiq7x9aKe'
    'JTWM37XFjn56EsxC8Z5LLVYApkLefypCSP8VOFFLNC9UOMIkJe9dpRpmjBS/vH+Dm4J654+2y4+EDRq6rlOL6UFadjiPkgrg/oQi'
    '+Y52j/b66nnvSV8d9Z893+sd9dWT3t5e//DbP6mAvu2Db/qH3xsQmHrxunDqxWng1EHVtVNfPumpQRZMh7CVOYV8Sbedp4jHSvVL'
    'djBASvwkHLbVdjxPIhQdmUqh1YZfc/b4pDzSo0fbSswyhaLOYNedYBydTtGzKfF8nJB2g3QI8LsgqcUfYRJNo4ktO65HeOY9LFSR'
    'J4U8mKadNEyiURulysIkJm5zcRZl4hEY+iOAN5NiQZrIOK80u+09dEbozxMiRya5EsNKjDFErNrqGFWRtV2T/VGmheVM4yjJp60H'
    'exyNJ2rffWMKlgfJW5VHvreV562rTjEaMtw2CvWb58MoLlQ3HngPXZDFyYwtaUrsrzQe7fbY2Soi55ckcjecarZSmEb7FmThZDbm'
    'Kgn0NckJGkW/P4G+cTQDWX1/tSWX/DCmDLkmo/lqd1hw3j7SL54E4zERVO+eL5uNOY2L7fuVozhKihog/5YpBJmYSa5wsqR+i0bk'
    'E0e/WOZbeZLXM5yJZyVP0tEnF99O0Kinsspr+5ZXQ+lDh1rmX45nj/lkovbfEcJkzJ5UTgRLxjfPk3g45y6ezo+bDYIQvteJCEua'
    '3MKZz846Qhc6BmNSvnpaWOCjWN+jwY5oqO6h9TbXzRUhCGYFTdk4XtoCBNObq/Grh68RrQcRFlXiFX+lZqQHOzreue/v6YsJb7rc'
    'oHNOq3glKV74t6R0cQa/uvFa6bbo/40VTfhZS8bxcdEcF0g+OBbwW4Gzil7DJ3nUxYxECjn62j6fqqbcs8m9lZpDHhslM2Tw7cwS'
    'or7EMeAnp9NFrDhfJ9mx5P7NLxwc5+WK41UYCpu58pyZxWg8VzjQtA7UFNHdOUQ7r4znj9T6aZRCh9Xa4mwLqMPWQrpSXrjprbW1'
    'mhh5bXP3SGSNi1g39WKuP3Hj003+mXN2p3diyxeGqgsy0npSbQ16f2VEV+5m4dFRiyO/nT5L8d/caUubENxI7aWkKE+R8ubHf/i3'
    'yrThox+hHvFn7wvClLiyZvcfZDpxJ+OZ1BC5etNWG5xCRXJo/MkI3gf7/Q7E7kP1pL/fP+wdHRz+iQjcHiM8mIbPCWeTPNLqeRJ2'
    'RtF4TIQknuS1+kT+TTX5BxEocQSYVL5nLyz6vUMtSvWac990zme7usCzPsSX03hGBx6CUvguQ7bAgX7EbpSp33YvPtXu74v9US6n'
    'nbE0A/PldFgPtUt7bgi2PQ7yCSzt0kx0YZ/gxPEMZZhJNJE7RxZhhdmJ4K2kscSk5I2DeXYWs0QtjeX3gsbsBnEiuePyT/TT9eXf'
    'hJMggpLgfXNr+TezM7jSFb65veib2WUi0Xradodv+Em6zut588//F1Ex+JbuQIxpAdaP5+Pxt2FAiHpF7zwQ8ChXuQCRo0DLHdfs'
    'd9vBEfcbu8nUn9lIrwO7u221qLnZYZ3bfUUQJsEMok9SQ1iuPrWP6Yjak6CDmi6nUBN2oiRzZNf8mPudMZsp0IAPmu7SgE4BoY6e'
    'c9WfOvFxTnScyVrHkXGFEZ7wCJ4nYnNJz/p8agy1wSzisNsXGsNisJgy/+tba2vadR/VV3RmLJibA9TrsQRqmASjzJlXkVo5KcHf'
    'L0wT7lEfGWtPpwo3dv469etF+oY6ff+G9ML2/k9s6XZbtLAc1lMZ8uDHSTgTy937/bAJk8lUrW+suU6n4rNvP4IruuvGz2IlfQLx'
    'HjUUjDu6bA4b7l0uw8EjUNWb7NeoLiLqgo3wuBuJOU6TVBh4aU9bTl6zErdiXT7fGF1qh3upKLVTmofdvtIb3fOW37G3BqngrueW'
    'uzov6EW/RSGrwjGwhMc1Mmi2whHw+qjk7KelGc6LfbZF7ri4p1lM8UPNilqqyCpFsS1/oA1h+oPHIaoshQpmIufj03CaVE2Tn9tp'
    'Oh9ogl76wDL2Ck4ux7TwQc62i18cR3GeWMH5gp6XG59wjEW5sceMy0A76YPhLv5M+HF5tOfguYs/E5Zc/sxw39JnhisD0o68otPA'
    'nC6Tfeh7XIyQys+6vHOROzv1ih9oNJmw3Ad6JpjRls1/XaQ6hkb8839U2t92droiGz2mctoRU+WNBwuypksjGdum1tWz8rOulz7i'
    'Q2O/EU+z5V/Iabnx4GUSEQ2aIohNfy1vVnyuk3J7a/nsvcH9h+pN+RP98saDG3og/aB1dUMnqmWSeqX7ssfiYWVSZunTdWq98cAw'
    'tIUZgeUjuGRZWFkh6apqEjhp9cfvHcdz4c+AapismkcU22nQ31UzKH9kDlISX9iUwCR5yiGvhLv54iQe03ZJvnR5pMPh7pHyH09P'
    'bTJnToGLWDl5XJ4Vjyj0oe6I3HrBePxu9YBCWeoOyK0XDMjvlg7oYXVOnBYMrl/n6bDNk/KWFlLRhu9mcZIZUff5zuMKFlnJHUEJ'
    '6bMOf+cQ0tmpkN6PRRQvomkemAwxutmAz+f3x+PA+LPRyzwY6AKI33xz79Odg+2jb5/31Vk2GT+4p/+XTokmKJOQxAtOqR9m92/M'
    's1Hnrkbne7zEAiljY6Jd772b0kbas7XRHIW/iCaAqJonJHfWzlLHBdYlSd1tSU639SX996tikjrrf/FL9V4dx+9Q1YPTb+pk7vRo'
    'S02C5DSabqo1lNAcDvn9Wh6pyQ6h7zlBaEeG39QV3hvtxtNwfM4FMBvt/Hpty7mc2lR/NhrRE8n4rv5sfX097/ovsKPI0YtaI6p3'
    'WwEUSRBl3qRM6660tiGZXD96U22sr00m9EEEqibpOTe++pIe5anQzKrubMzeqTtf4H/oL1puLDXcNxVSjsJmkn90nfV6mdJooi73'
    'pOXlw5BIG4/nWbiFe0FeHG7U+I9Epk5/mVV8iSl6kFwP8H9bxYHk2OktElhu8Pr4wYXujpADw0GAN0lOqB2aZZwfGhXtwcs31Rx6'
    'wEmQhvk2rN8loK0plINhw5MF9Xp3/U5pQlqA9WbEJZirxze4cffuXTMiYWaWxTSX2ysmWIS5yNr+yLfcQW7fvl0ahGdR6EkLDNSV'
    'XerC/fChVOrKSBkVs5IHIAibKsoC0vTymW5sbJSA/cWd0uQxaGlIl8/7494tIcaXH4IYZpJfffVVaUZfVEzIpSIaAOvutty6dau0'
    '2C8XrJXv7Hmq1A3q3kJ13dK5dxNOGcL/cCR2eSYkIi2ZyJ07d+pDvWr7CsM58g8Nq6nzphqNQ/r+NCAqcIthrftnukBYHFtiLI9k'
    'PE225QnhGlGTaKj+LFzD/21xpwyMTSUgWTAXWmt5LvyxLY+8CYDMJ1M9x6oT4vbGCQ0qzruB6pdffrn8exZslu2Lxzi6BUnG//Ar'
    '97vj42MfuOs5SWFPhk32agkT0zvs97/8w77BECjt91+q54cHv+pvH6mXu3/ZO9xhqeQwHIapeHBksWJ/YNx6KXmqkKRlLreA9J8/'
    'aDCoX96EYPhniBUkSUeLDpPgnT3aX62dnwn3hnloNI4vNpXEq8tT/4jwowXHRK6sHeZwHiTNTiedJyMiU1oOk+PrHl1pJc83vFad'
    'JBhG85Qag5zqFyTAnQVDzHJNbRAeq7t0ylRyehw019r8f90v4M8Atqk2Su9u3Wm1S2VgUCglo0/WmcNz+407d9rmv2vdtTsmZAKc'
    'QEsyLHypte7GRqpO5sfRSec4/E0UJs3ubRqqu9Fez5OU4DhJ8obnSXyahGlqnIp+jxkagBxESIAbejLvl++h2R4rTULGUht3NaQd'
    '7EjPkmj6dtPEc1pZW3OOys23mS94RmkWzlKT/LCMg0y3OBA2tdRLoomDmR22yLA0GnljfMAQaEK9lbrqDONMd2cEc2ZZVia/m6Ox'
    'h9931v7cPx0by0/Hov251ao6s5ULUX81T7NodNnR6Q0KKyyyoLK0pJmLjM+sxIxehQDuuQnGY9XduLP00CxQPlRR46hQX9RvOuyx'
    'X7VDpPSSEFq1YWWYBpNj4KTyin4V3lnOLFJwaTjtS1M54OpuvYcV5A//RyK0266D7KStOqTYx1wRzj3sztHWYm2pQx8vrcLKKktp'
    '351CRUSG0wWb87lzNP35tZftpNYuFm9jYb2IhDULLohNHq5/UaUZEIuxC1ypH1SckIXasMjBohCDKCinZ/4TDjq/bnbone7KUwSm'
    'Mcu8JchLuSacuRooyqBZDmsBXiWaFuCM+dSXsysJVdURL5AY4bH5qNoaUCJlX1SSMu3kVdisViULsWehiBIdkgMquAtKwhVEelff'
    'd3Bjo1XSue5sFYWHwRhxQaxI/qxygjqShGi5RT65SLqsNj/lIOT1vl94aFhws0wmF0tg37q15oklZvzOpVYuP0S6ZeEil0Zj7H52'
    '6XO50mm9Re0rxEf9MR3LL5CwEMV07Pf5QwOmCIehwyFDKQ76tAJQ5iy/9ye3voiMrLWqezfgKfQevouyDmhTcYC1hXTKWfriJXgY'
    'fnSJKCfxT9UJTsWU1lK/KwzGrXrnNCHhqyAa4tkW/6/1uO4IdqTA31kYZE0SYEYgg4IpRZLAXWN1nhCwUt4raEMWpy3Cs9UNWr2o'
    '9kLR5kkKGqMB77ArX+evJ/J7jNwRXVR3/U7a9ng7P3BQeX0DDazkwg0q5dRrsQUG8N1F8N08Y1fClaLWwmP7bbOzYXHXF7u+qFYs'
    '6wnn5al2TSaimrNdIOJ4kl9JTFz3xUSrIIOWaYV3nVD3i7vtL76kxazfqZhsRKpCwcR+t2wM3yp8BV+FhWbf5RpFq9gXAnOWmNiu'
    'y02tx7OmN4ioYoeS3yGtQfTJB5KaWx6pWSseBe2O/1MoDW9vkY4s4OQ/lYLUIBiltdU95R9ywpmkVpzw0iSc87t0DsvPrd9vdjaf'
    'HPumhPU16ANBOgthSUeqPFIXbt7eqmu5qK3wf1W8j1qoaFchgrcMvjF+n7MpwPWu/Lew4Aoqsf4hVIK6gsS92BheoBGeVVxm5ZEI'
    'hHepURSOh+nPVuLm6V3zMuMLd617rM/BMK6zDLRzNbatdLoMNpCbAE59t6ZYE0yduSzQq4VMV2teZeX6y9XKdbXO1tm4hgGM4XCn'
    'QDV5/p0k/Gsb+7OACxfQq9xHPMuq+vAtZaVOlA+k2wZIRUgY6bkCfK5QvYvEJryzZhfh6UQ72UgVis4oTaPbitem008grMjZU86O'
    'sso0fOta9v1F2nYF/ykIuuuejFuUKq5hOYznGQQEF5Qupc25QtldpJZA7LOvkoSs4RAkYbZI1LvyNkB4Haea3eRtalXyvYrLi42N'
    'a4qmMp7gQk2ZtNIuuVCuvO5UNp2qgjUPlXchXeqxk04qiJQ4xBhU+wqYZhU4OU+PmdRKKUr47DsXKHj2vtJ4vmK+JTHVxfiO2AIL'
    '0zi6iLU0qHCnns+CfnU2XFawVI4k8RH/NRLkbZcnDDSFNz4gOiUNWwJcgm+8LGobVBfS/fXl7hYroFj/himHreusscTYV7rAY1c8'
    'VhpUk+3Ut1vq98f+jWugK+yvksU/7Ba2bHdgNXjDkuPrSCAl24hZx2/RlWu5wdpM4PhSKbXEf6ogQpa+x5FUC+Qx1zPFWjA8KfS2'
    'JxvbzT2LZsoYQg30QWNFsirsVG71XKF0LMIDaXRKsn1ZUqmQ5b4oCeYlUWkFPy4teEiqQzRe4g3j04Cy3B5nP/P6Wq4EL7MtbC/b'
    '80p3xgXHpwryVlv4XV9+Z7+ciOTGYWTTrOZ8C/aq0jLpDscimUXOXECreSfsePDqk6U9S3O7P89FZ0pm2oSQrASsWBMQ+7sjVRmc'
    'q5+Km7X1jbQEE2OcWEg2tEghe++U8jB5JqzYzqqXTjqh01FLugbn1iWbFtEH8osQzkVSdU0usErkXyTMl0SrCppRhQn1dnnRzbI2'
    'HnkCecmeVNgugp5vSqrHP5fJ3K3iAF2TG2SFv4ELUsevYLUMDu9vo8HcWlvg4Fchrd/Scm6FuH5r4So8cEmsFTxOsbXTME2b6921'
    'u5W6wRKj8+3SaJumHgcqYpnbpu6tOznikDpEKyQ+FbKX6yeID9GhBfducuzCPVxIlkOi4EiP4A83DMwLn5LLpwcmjGLKJc7d+j/8'
    'nMAx5eR9V/e+u6k/4bF5VJoCgijelGMuOFy6+SeXK6Psj/knlZuO0FoXyIXawNVl1Xpb8n+td7u3kHYmJpWV39yGDwYirzdNvWgI'
    'xvyq0WhrSombUTxqjBAC29a8TRQ9k+9OTMIcFbDpfHxMIvHwgEiDfcIx5zLAYw5W38ED85J7dEfXzstOBxxg6s2QY0e9J5KeIZ+I'
    'rlKdV7ey2QsH24e7z4/UTu+o93MR5MxGEu5+v9cfDA72bYJBSUzJSQZtURxZMe7N6PG//OO/+9//v//0r80myWY2jhB5WPggnR/T'
    'mxeQQDj1oGTR4lRzKqD/V6djJMQ0+0iUZjOPdzy7/eDoLAlD9SyIpqqXhEFKZOi2DWmcjx9Y/9d748gG2h2yfGHj6yR/Hyeg5co3'
    'GFjno+2iBGSq01/xbQD7Ucdj2tWn8SRsqzzBWVsdhjAq4y+kI2urXQ72aqv+O/n3aTiede/dpJlUTssW8CnPjF0RtEW6qwZnqOSa'
    'Ep8LidsjTI1wkwDYVoAgfA4JfokNsku7ajsej4MZG7yXTEBX6+lz+vTyJFBWSSFddFd9i/7BV9hWHhLMzsKEoCGnFEAK39GcxpdI'
    '9UDfXjaGivmHN/q9m/kOYTOfzcdZNCNhTyaSqiag31q6p0jTikEmeZnYFL8JAmoa0kTmqCfL8zfL/DxfGsrsOLtdBg1ye3GrM+oz'
    'oq7ji6kOfMTy23pIkrlC6ic9C8NMdiE9i5G0J12yYodFsy2dhAmUNIpmNx78yz/+m/9NCuPaWf/49/9HPm/aCMzZYozxsM5iyFPY'
    '6pBmyxM5hZsM8CENxyM1QS0EREECKHwQu44k8EaIlHfEdWHNtHjC/+7fF463wR6/vRxwHP3jeTTmetCckY9zgoTnSNGm0yQtOuIm'
    'pzDcZeqd7wFOBp02Lj/t4/Hu/lH3Zv/XR13OPoZjS0c8moSYzTC47CqvWCe25e3xjQfbWTL+fN2E6y48Pz2mA/6AL880fp0EkzAJ'
    'VBqGdB6fJ2EasmV1mobLBr21ctBtc/yL48YqSqWyIoDeJJQ5IbxoLRvt9srRdjgn9zysXiTt5XIY3lk5wHNOxH7GUZdjf5RHSRRK'
    'Hhlaj7W14SwcIxNpCEK3eOgvVg59ZNUsf9ztF0fq6GCzrR73dvrq4MXRpgqzk2VjfblyrH3ShNMCEDkov5FC0Addj6YmETqtcMTV'
    'WCUee9nIdytGLpLZAWk1GZhIkp3Ms3pHigixP9uTyxPkuz0jznh6Zqrvch7alFNCMsrrPGhcjnUxLLi4gN97MDwH209NXk2+yH+X'
    'zYm3XdKPBHsvmevNyM2we0p8zhwGzi5rkJWNIcSXgFLjy9aHU2T22Atyjst5dZnKzjjOZcmKdBmiCySJw3ROdD1c7oLZVYPoNOqj'
    'ECsZoXbMCrrMOZY6LAQUSfPf/lOBNL/UBJ/Ztsi7A+dDodHIi6U4cJ5ZG0Cfs3MehyswhzTKMF0ikIWoXY28QR5ixQXEeq4Btora'
    'SppgwJ1lGpnHmZB2ven3wskD0HX19e7R9tP+vuqQIP3tvZv0uFXGuiUDm22z4yI9F+NgT2eKdfGo3PVOCFZ2LNUMLMRmLq2/1nw8'
    'mpwDooiAH2mN1ael3DkfgguX4vvnKfaITc/B9aWUZuDubOqfEc6qmLNuLd4BGBVkZdsDTlVP+vmYRNnhJbZIoxZO6IcThxdpuGQb'
    '/9LAnCA9nw5jphqLmw9QxsH7KAnpI1CS0ZxIyFmEAlOXYPEZM7/hSnohCaQKctyP//AfCrTia9pTnWwqVUcEGF+Qg+5DGx8g8ThR'
    'qksiBuxuZYTKhYQhV5QUd1KL7TyCVD2AVO1TU9LWTzsEwc4wiWe62op4NoL35JSCJILecKjOoyCX/vnJjtaNbLfL1CKI8kjYVxBH'
    'IM/SYRRJJAbntkK/4NnHnocI2I8Q7I4iF/50joJTIjXxDBphkGZIK5lm1Df9Hjz+Nadl56l82EyKMoRRda+xl/aTZ/GwID9KJnmi'
    'alNolJyLDrZfQsGhSsxnJLW8JTg+Ztu3VoCKfefd6jsE1CZdIs3C6KNQAJukzoLQJw9VdhGrc2ROxjUFKQkOqWCFHJmp8O9SaIkB'
    'YCmUpAkOupWEdx6TyLnza9V8zMIfT7bVVjsH27/O58qIBlCYDioXTH1p4REUgzXxjlA/DWyRqJjvyz1SygRKF34wggCd7w+nj6sY'
    '3cAhdsjyzPYfUuozUs+6Rn4CMe/gbaqVxzu4DJhnISv9F+F4vJIO8lJK6uzf/t/V6uxjr7mWlKLxpK2OvmmrHuopYGcmAcNrkAGC'
    'z8fB5UI66CbyUzdh6gjDKS4xPfSYPTBlOtTLJ72bT0mpv7yI46Heia7DDT2RCDYgqxZ5kkdb11MiBq/renSRskj2/Mf/4b9XCHwT'
    'WALPU56XAP/ezZmLzUckc5vj5k15L3qL3J+0Lp0S5nieCYJtH+ztqIPn/X0C2faRenTY733NADvqPTEiPJ1tsFAQcHj+GmNOW82i'
    'cZwJPmbUFrBKi3NyNqIwKSlEAhBxgfuukeUkofIxibMkwhOFvLmze9jfPto92Ce9BQR7P4aP6Bwl5UEQtK2CuS4beybgeschF7ee'
    'T0laYtugVohSplKY8nkcnYS8NN48havJWPEiRHOIpe7JEHMvrStHqMKyCIw3B9v9/b6z8yk3tpoximtptzDXTKjFH6+4B83LIoWd'
    'KVGVIINVjzCjQ5/KfGnZkAz9ma46+6x4aKSAVSIkvDgLWfBShGicil0hd7EWwvABsTFSNwh9cCuckwLZDI0yxB0mwcyXWEsEgOuV'
    'ONZst2AOCAMwdlOXILflb0XFGk86tKMRMsk3TC4Fa85+2ld7vcGRGuw+2e/t2feclZFtXvIhEjF62TtNQ117pSfnk1MOs1WOkXUY'
    'TjBh3NnTMzrtOOzlUy62NHd3gbzOWedTYw0badeOzvhvls1Lhzy92dAapfEc2GywavWyPzh6gpuKx73t3b3do29JyRr0t18c4s+D'
    'x493t/v0ZH/3ydOjxlW72KdMljuVPh+RlsnslBYJY3PKMgutZo4aGkjxEpwkcSo+vEkcT7qqj/OXnQEawKCMYNuF9KH/rDPqTv8I'
    'J/ybvjo8GPTU095eXzVvr6XEVFOC36wTXqIm0Uk8GoWsupFAMkQZHAIfsPcC5DiL+Z+YSWdCODcfB4kml1WzsDvTaMssMHZFO7Nj'
    'qIzM7Y5gUucTQnJIrfUNAKwwYOfnERuFNbkh9pmRZEjwIvi9BdWDgg74R1lVzyUcYEZThQN9HIDtg8PD3Z2DQ/q9fbB/tLv/4uDF'
    'oM6Ej9i0M5mJSJeqcxScU7oYFcGDiLUaA9Kj6BTHR+uqhsaKiwOBTRv4R7QRo3B6EorFqc4MnvUOt18MwJ8IFW4xKvz1HGZ3sC64'
    'LJO21VVPaZpnIYzWpHepCziq1ALbNY7O9QB3GKeBzIPg8SxI4L4ci0isT1RXPY8w4fnMQYOfgJ4z1y5rcZTkyFj6roPRL2hmRPvP'
    'ifAzEceRJ72EiDqND4Z7UQ/NM5B6IDN1lEZj7PhHPXn5PImQxsKk4tnlw7oorbdAjcZcUYfO3ZM4lCiEbu3d5evQtKp9Ts7tjLWJ'
    '+vd4lDUSGvLDFrAwOSfZh0AIdBxcRLANB6ynd5GXSih9/uY0iKYEqkWEtDTkU/bRnpkaoowQPJgpHXkcErmDD/tEpNBAi2VjyKkB'
    'nQvS35E6LnNPs+R61z/L4gCLaSVZAKKtekkAPSyJAaIcrJABrM2K+o9wPngYFgmgt5/FF8z3YLuL4sRe/ZKMAJiQckiKiWTWp+VN'
    'MU4AM0R0YgWBD2X8z7a3e3t7L545xtV+73DvW/Xs4HB/d/9J3TPxFjsBvULOq5iQ2NydxVqKJpaVcWFTUAJcX7JdKcWtawZeWAsp'
    'fvWCRGI76eYdIukFtgFy+BZSJYGZ0WIG0EeYSjgaRScRze8SogUzo6+JVY41bqWw9lMnKAqoJWRUjOiAQ12GQZLWRFuUgqGZgAVv'
    '7/VI7VDNjdstfZOeGtsGMPkiuGxz7OGUhaLj4JR/8RoIK+aIEqlF+mScOsRvV5wNAhbSacPehpeWt5zBt0D2qM6g2Is6Q0LYH8bT'
    '7xoZjXDONw9D3PvAuBnjVvbjrvDZfPJRp7/7XWOicTW4hIlE7ZI6RxTfWxGuBRYtpoQj2+OAtDjFMrBY57HjdNrPwCi/jvgpHumN'
    'IWQO33bVr+aEiW9DZBPDSxJnrdz6kWF4xB4TAdc5I1kpgeZS73xiisjinMqZsp2gSAQxJubpZ7oJu462lYZGlNvsT+Oa8h0PxyQE'
    'FlPr68GFm/nwA05ZGNTTHxKWnuFYMfYnsIJpwMYwvCxxjef9w8ekkBAx3T84fFahQm7zdyuZh7RKrSXJMowRwbYDJw/icwGYB5Sb'
    'CXGFwLWBgGeI0HsyFxvfB/KKp73DJ4cHpF79QvUGg4PtXVayO2z4UaRy7+fi7k7v2zoQ70GWmsvVMo5QdAoDjjpN6FBdsho2Qjin'
    '1m3pDUfPwbZAsCIJakb6d4qbCpCUqB7K9Hd2dlFd+PBr1gjaEFFnob57TllmoT8uOINpwCn1Q6uatpDalMPG2N0iSS7Z+egi1kql'
    'tmIhMFUn9sHVNklJvB1n4XeNVPeJI89GUJp9PFR1CcdTwXaS/ueE88cxG3dlZByAroK/lKgx42DGHm5igeRzTMB7y9oOqmVistkC'
    'BbFEORhotdUGWHh51Dqk5uCMsTYkWlcPBCgpFKZv1RTu9wRMwvrnh7vf9tSz/tOjnt5UQ0kydiCUDIwB5082fklIwt/O6fg4jt9C'
    'm2KDO8sQ4eVxXJey8gTq8sI0yIwQIGiWwt4o8vFP2YwKKk6wov+fXPIQH3clg2gqR3H68KNOWvoNxhcwAyv5RcdD1WUJz5PokqSb'
    'cXyBuq3CifZocxndSVdwfokzqhwT7yH7fRz2SCDeUwdfH+x//fJAblVgSyU2o57HRHmJURSU8o8KYJI7SBw7JTGNL6XknJeZEv3v'
    'azzKziuNnNl5hw3snRMo4iUetQM6KBZOVtqf7+4dHKnm+ru19VaZX6ELZTWeo2/Uc3RdZFj0nIc0FuGqK4IDEuOJls5PwPbY3ClZ'
    'voWCnoyj0YivC82t5vVZlh2wtiVnv4frAQIEf7rdG/TVi/3dI4ZLbdPn4/E8JtrKxQLOSBIlpgWzF+t6HWJfUyJApIWE0O5m2aVg'
    'HJ3RM+xx+O4klDRhYoCM4zHolSjStUSYgXpCeEsqUv9wu38o5k9ta9COR4S9s2jKpI02DJZp0ZLO4iwmxjs7I+qJi1mpySrerqz9'
    'YCZwCK9tq5zhmlHMe9Bh8xFgrwRBPtb8CAtnDytwyRSuEXInMyUcolnMJzPiESnxCLEPkzAjFqXDcByFo1qnjqHy2zHLYv4cHECC'
    '8m9+g6ulF9O3U4ijJNoch+zQjQs8YtwBe/5lEIKDaXoRVquUtSe/xGgnla7qaEthclKtZJYWugdehbsxbZsL5PJLvFbGqFhFm3gS'
    '4S5yjkCkc9os+PMF43oK2TcHEB6b33QPuq26vHTEFp+cldKq22qH0IPzB9Za1pMEMmWukBinxIXcH2numVhZ3ra/o65FbjQFrG3P'
    'O9z9pn/4qLf/tXjH9F7u17LZRSkRmNMkvOyqR/bqJVWz+TgNrRkiAnXAFeYRMTmid49JVxkIyTDs8ILwNoHsGg5PCS4hO0YEkrAV'
    'xIqoSHSSKq6VWB/iwzkbsKfs2M5a20wbYuTi8+Cx2j7cfdbXWsUh7es2MeXB010C9OAZqRvaoh/MZknMdsl6ZmLuog6CPUIC0IsA'
    'btYxu0kSPKT2pTZt7sf0ejxGUMA0Vrs7dNSJSoEUgHrOZvQJRMkTXDH9Fk46ZFYQRL1NjDttppr05DAgSjqsJWhk34lbstZNLs5i'
    '1tFp5bB15EoLewWmbCm7qKUdk/CxQDce7IGh7vENyWrBYxBl1M8ymWMAWoMshOyFL4NqKcRoyxnb2OT6lW+LExPYw81Jbc6iCYMT'
    'Eoi9cJUL/g9UmXdwB9kj8rC/u9/7rjFQj/d6IlDs7X6zu/9EHR4cPOPf17C3cqcHg/4uHYCNlvgIiiIaqyhh+TSF5RIHdAyFcTIf'
    '03EO43lK5DiUK2ci+iExZaw10e62AffPCiIMNkE01sjFZkEoUrUVNLCDCa79sW71src3eEqTXW8pjt0lHggvx0s1BNPHnaxR13jy'
    'uOavdVrQ+W+JLbLRT+x96iJkXwWj0mPeJHjATnt8SfRqnqTQT7CJyOtTV4+FUDCBZ5Oje+wENU2vC1ZexSK/a8C2RmghWyyYcamf'
    'G7hfkIC3wMRXGhvoVxvqoCopKVgz+I7WMk9jQkBFFvW0ASa32/82gHMa68MDQ6eNpfopsCgNtU9giEZqF3z1UmlXo7p+DU9DnhnM'
    'OhOeGWnFp9OIYBJM4dQ3T8OPOlnG/RwoYW4VQ4Dkxz+ZLHSh8Dade3bHOK+JLPbswXScn06Ymvk4pnGSXLZh/kDUXBjAYeaMsYtk'
    '8bmEh9VkYyRhnIRD3LtVOgpZPXEpG3tuO1mtRDttrT7tOw1JEmrNz8SyS0olKXQTWL/Z4Yaa5G7ZzNaCFGlAOrQHnYswfJvr4B98'
    'gdg/Ojx4frC3e0QC2eB5f3u3t7eLm2aIboMcMLv727s7/f2jnOPVtBE/ik5JfJ2nlwhzxXrGyKJAGBen2mvIpP7jIM6A1wh0imqq'
    'zNu7xKGJS33T3+v/JWnMdwm9LghNL3O1lzV0OAzpWxerUmvJa0TkNZOG4s9E3POEnb2id7RrWhupJ55iLnWQ/2UoFmRcq152OBUJ'
    'GxGsns+GKZJrIA6ROnYi96xagM0u4q7qjTKWvaG6EZPDrboYrxGeBWfD+qo+sp6kvuakJHib3RHNDzZC5T7zJFcMo9EoBFWQn5m+'
    'h/2ooNoZqG+hettQ5+DkhPRG2kIalV4+ovGnwdS+/isC45Rv2LvQOZ4jvaR5N59G7C+e1TPYy7JzFCAxe8hjfsuXJ81bd1oqCSK+'
    '74MVCIcUQx0TpRzXY3fcUz2MYXaXzgU5aLPhAa+RIxw+/Jggf2y1wpkuSsy36+xSB1sQjKmeaGmRwpllLQjvx1yngSNh9aWjJOaR'
    '8wiNhe/4U7latx6HH3O1bGifEVrglifAXQxuQfFQB/thWpe+sDGM+aZRe8XE3bqeFkxe2OWhtm2CNOmSxaFgPQ7gYF1pQOY3HXEC'
    'K7I+toqqx4f9f/Wiv7/9bYnhHQa5/zzxOvHiHrjx4JbfPXq0LakuZSraQ0ZHYviMD/Eu4gYr9ifrEd3OXWiofZx7yIpfEPynP+z6'
    'UwwS61Jxr7eze6AGRy/wz025/Dw86O1cz0z87MVgd3tTDWaoQdxmwaojTiCEoAiIeBwM2cVpWvBfWkKHH/96k1SJC5idgfvHSRyI'
    '73n41/NoNhEaqybRSRKLvfIEDmy1DsKz3uETyDWLbHPVgt1FkExgCyQxLYlCIWyE+SCscHyqc7Ke4HYUrnrseJFb/ObWoeyANju4'
    'PMap1+9IgifJIIIzhbrQmplReNjKwT6nulh6Xd9bAFdqgHN9Jk01eVaDeJQRZyMptqb2JtCss/xtWJeStp0+0Zd9xpLHCW2q9mQK'
    '3uroWY7mqLWa3T06r/1NzZU55FBH/mrbLsGslkdJb28P1wzXwwuaLGTVSTDmsBXIUhnL7Ui+FdazWRmPIlja1cXZJelW0B8Q4bDL'
    'Njv22MHWw+WO96lHuLELH/tkKPAS8hHw49mc5UrwiJ+2h9VL5juLtnE5rsdTAja9hVN2a4MnBHTjtK55AQi7I7CFZxE7myFUALo0'
    'cVn46/EJSjNx2jR5wD7Gti+49o5gHNEXBtpMFSOPDswr2MuEKB8n7744i07OzLmVD/n6J5po39NjeIikmbESGN4LM81QEmNkNf3K'
    '6p/F3Xx+2jAE6eK3Ay9WwXOrnvaPB8mKRiw2zGbjSDzHah55w3DYTkr6ZDCNORNFm/1k66MURBCmgGfspYarPOQ8sFJkLYVaZAod'
    'GlWpUPcOt5/uftMvq9A6nKqWTGEaT4Mk4UIPWqrQ99LArzkkb/0eAoSo005ETVsLD7qgroRI6TxGTD8+JOam/3x3cLBDEsWmuvHy'
    'aY+U4v6z3u7+4EbtbfhXoCf6KpldpEK5w4GzIMQ/phdTBXukScxTz7dkr9/bP7g2RRcIktwFmNpbwCA5OYvOg1rkrq99ctj+Q3uS'
    'X/eKmzdEF+o35PCxns6XjL/YVwOZq+jZ8FTrs4TarBXAmAiXgkskRroGo+fUV5n2e1Q7YCXgU/PkOBx+HDhWuly+PIsyTuHUY8iF'
    'bFBOtYJ0RmiIi3lrleCw3nRGXFs2n4jGOa7nQhDCjLtnO5E4FCCqk96QYJydweaMg3FEUvQQPsi7WnQSvQU+G8RBp/CTIvoSGPc8'
    'aVQfjP3peTiOZzb2rUuARaD6fDqKF6LkIsplkshlHMM1Jyl/Tst4tFhAXirFOzRmiTFq0bZexxOOREwYba/B8rvdLsupsziVlG61'
    'Ab59FkQcrBbM+OSwfwXS8rIDHE4LB2v8tJWWzStwxQhA+x6q/G8gFWdo41wesTjYQRs3B7ueN1d96/YhjUxEFFaVg+7gGsSLXf7Y'
    'f1hyEZGyMoyTeuI5zIx0WKLsoWKerW/VJ9FwOJZA62XL/SlQ34W8JAmTWHpa7BkmKbQrVHu8kCJKyGQYJJeVrHhwxH5R5UtZG7sM'
    'Prxd1Y31YM7fmWhj5XkyF0ObYYKNO7CGIZrCDXadnV1ygLLR5iWd1moeTEMKLfgAHwztj1DZuMKnOQkieC9ihmx4B3pgphLo+mLq'
    'xMKwXyYfTKLNfAk7CYjyGyosVkD2uuJGJwgHllcTuESy6su0gohzUttL7Cmh2b5qfsG+YXCeN+FTE5jj0nmUsQ2dPUAUoeiQb2iO'
    'cYBx+x+lWlrna2Pt3hSkwnnYfSqQq+d6Nq2nB896A/Hl0NfDuIKG6gNlTF8RSzwOpH6J10xPELRrjHnap0piiS5igaq48j4lvjcF'
    'n6gW1Rnx8soOOSmWWTlhoWwyYZcPCIJBvRtq6aYWEZVARFZn6VCwRQi0JUpr2WV5S691K2ucR+azWrZj1sgIAg8/7rIHuKL7SSus'
    'FKSG4ZhDq7RnEacYsSZYe+Wg/prkH0mlwCcgf7HEO6/CKBtPCPvH1scY/oAJiTwJbBp6CvrWJap5s1EfgEd2fb8yBg+75I8K1meX'
    'EpEs1/niDKXvyWYS1w3+d3IWx6m9OSYd9RxYjMPM993eF9c4jo/E61AOZTCexIjGmhCJST8yOMXvYz4j2cvGLoKFXyyyFH44QF+G'
    'fPvhu5ku1pmZWadnwdsQVx1J2ZW7p57t7gxePHvWPxQ7NPyNdg77vWcrWPcg71Q1n8+Px9GJ2omRDrhV0qjl7ZDfeh8C8XrE1nfb'
    'Oh3LLulN1mxP2hTnD2HOzZzf9Q0vcv8P5Oa79Xn5rswXXEPfGc0CDi0iiY1knkH/xeA66MlZ98yHbfV09/nzg71vj3pt9fzp7t7B'
    '4Oiwd9QXV+oe6a3TYYB8OPUwl/us52Ny0YbXVqKeRoS/48ssIAo4T9R0PuNLN9wOfzfdSYILjvgMEDmGUhbU5CyYzS4RZpGi9AE7'
    'F3w37U05IJFURq5MMc/a6qCtRJxFUhKwKcRZfDfl+y/YGtCUyARt2qe1zooBVL0rRSS9xhQ5yyaHtCFkKwvDGd+akJp1LqFZfJOy'
    '9d2UP5mK16v3EUkVwUQFbBLV1HILCx6KICExHbAHcSw5kQG4jIzZ5Qvr3UdtJfAJ9gkIOJNAytGzx1zbTYJIMO5304MRb0Iaj8PJ'
    'lATBapK1HLP6TwSv+ofPdgmp9r4d9PZ34BELjNrpwwdjtxpjyxrGk5ro9JRRgsjfEa6K56ngEnFHUpSINA7nb8NPPzIGk/7LiMUh'
    'cf3TECVeLrQZnCEaXmhOTb/qSSK1l/sYdyB0+s/DdyK1c0waUTOdQQ2FCKIp7WdPG83hVURC7pD9i2zA99MwmURBfYK+wD32qPdo'
    'r68eHxyy1rFK8/K6yKNGiVALZWWCy5IBKVXQvZzIG2vMzD1ekSkKLuE3w3eRzgpV8JC1KVo+DuG+rhomxJtwkcafJ+zFsQdx2d4T'
    'HkzHl2LLYiULxOnkZD6LwmH9a3bbOT6fEo+D7yxCdiSvGvfc5ih6lvHYnwbxlKKFfLO7fUS797i/vy9ZCuisIok9O1ezi4Cj18BQ'
    'e0Iql6Qrp8HNL24J73EMzleXCfJH1FsF/G53j3DtsIGISKTfyiTsvnVdl3npqK5FZNcErcHwKjZc8UTGI7aV1IoGYQjWv2vGMT1F'
    'tg/Cx1MitJf17nSIDQCwWkf/yNBAbKu5utXxqLHi4kc/DQQVvP9ayi1MzYIb2o8tqy3e1l/8LhsyI925Y9Dn+766N8z1YbCrLpAx'
    'w7JsOoe6bMV8ao33wjK1xSRI34ZDRwk8JsUkjEEMcUoh1bJ7oTmANnKbviMxKP+w1nF8ZAKnDOin8TA1F8LonT3xs0QMQt9EyDkL'
    'Qh1AjDBB3dNg9rZmlPA1zw8s1eJeXOu25t1JOB5DAnKJsH1abYvk6jhOoj5EGvWObNmZPKECoJYXovh/udQM3/MgOWc5U4LmeI+R'
    'kome4soOye9T9Qt1QmxoEnS/m7580uukJuWmc/8HsSKShGRw6x8FxA67DZ1V1Hj/ChPKZ/Sf8+kcfaNueg68zmToHTJd5ikuf+Ek'
    'uPxuujs9Gc/h5HPCUQMI3PcCYal1cJoWJsM3pzR8ntj0f/XA4yTKLE/IzU35C5uZciTpCWhGuQ8Wp7Rf5GZVnNOM86EWkq2aCZVS'
    'pjrz0RkoaS6uURiwIU3y5qCQ+LQsbGAWSP6Yo9TgqP/8+939xwcWqbiar4xHe25lD5M5H6bUQAd86hTXD00jkw92GzYN8YzVmGOz'
    'UBMX/SuaTkM5/9GgMQMfYSjbpfWcw62lk2w4H9MZ+Imp7WLG4RI13IU3YvXAO1x3NNU9WysBEzHUI2hXdKEH7nGJLSWVS/OCD3lh'
    'nMaygQ+57mkR1IeG/0lC0IeVK96GvVWXN9KDa2/mC9xsnkbTIqix/6P5VFzccYhIN3su0HoZ/YZOe1Oqi9+8qQ5DTkwa/YYt8yEX'
    'svtNl8se31frW/o36pR19T7f1/TIeydQoFf+Y12ErPwC5cboKeSvHfqz2epm8V5MtDfEzwGHWTcb4bTz5BHB5L3c0BIskPeQHuC6'
    'l34hTUoSnRDOt7zepQgZ9f/mn/8v9dl7ZxQSwqDUfEvfN1tX6g0+y2zVRjkzSLWMWoC/Ghzsd9kXsYnCOeMBMR/4f1Mfu1k4aTbS'
    'UeeCwdnRRDJttNQPP6jG+6uGro4YjVST++tKhbaWM0t5omgkt0XxO12GrZV/p5/Y7/Tv4odcra2lnAH5icoH5N/Fz9ik730mfpH5'
    'Z/y7+JmAvFXeBPuZ/OYakLiKPzlr0jDvpU7qTa7vRYeF73voyffUDR4hb3qzoZ8LUGWTJvEwGFPftuQi7YqumvTocnfYbOid4Xby'
    'ISb7Kf9uQaiYJ1M85QddNsQh3303GNLHODPykRyR6DcsPel5KK7DaadyHL9bMZEONcnnQD9a+KjLbKXLneGE3Lm7NnvHx4TEHxIh'
    'zg5DZEzQhcFMNUl7rjnhn3ecdRXCyQeA5WLiwuRi4gAkCeFY7cKEXsvUdSliOd4MKxYLOW9xNGWPKGGdnF4NkiQy28dzpM86Pb00'
    'Seb9dWHn30YzsyZ3lXpDjlDBTAfpkTqemmutnYNnfKs6zfbiYKh9a9nlcRQjUWPIRd5QnjHMUACLiH5TF/y02Mwtw+FehEPg/Ojy'
    '3019rMMxZ+2mJ3AZwftmwLEMNLXdoRQ6bav1O2uyaXn1w8OQb29pisjuJZuB+8PxWP08CiDmUxWg43xILSIOMvqd19zO8cIjCZiV'
    '5WGWPiiivUTs+V9TJjPlX0DLacOeEXOQ1aqDW0F5aIDHY64Bv+JbatgZUUv3YzurVR/bhp1ZMA3Hbh+8Fmb1qyaPhuXvQa9Une89'
    'qqUhAc6g/ywQAXTHyHL//n1nS5R6SNRBgVsjzNh0p6GI7vSfS7vjXZX/UHeoZ17u0oKslYO5RKjyLh0EWdglQ7Alxjv8WZpjYdGM'
    'ZYtnmTMTAq3LDd6bUsoFnrBotl98AVZBfZfGxsvb+qXDUa5AhlwS+yQmmVDTWJ/ZAtS863jMBV+E6pWIpsUd0vmTywFpcVDPmw0u'
    '7wwducNpb1N+EQ4brYeGiLbVXU0Z/SkdmUVWTiwHgZ2ekNP8M5FMq7reA3gquxXAFbrUzUsdPQpO3h7Fe4Lc1d2VKcbHFhA8jmIW'
    'r045LOLy989HPIAdzcbEE5sk8AmwqpGmNx4bvJmNO1lw3GhB3UAl0iYJulLYIHOEkiw+PR0TtIXrwgTDQifhaPcEOgqdCAy5EFHw'
    '0t/cRa0cyYqrHK2i2zR/tHNkK/x0pSvpLCJ0BhfwqjO8ohFfQ4V49RotOdrS1i+nxvxRdxLMGCq6xkqxEgWmgIY3EFiAaCZ+DJHI'
    'rKzZ+Ow9dTy8arTpLxqT9JUbiwpboLvjYCj11KktwVaO2UNriNrUj7Nzefif7RMxzTy0NplNsYS4pdgXLGA6im84BX0qmrDOiUll'
    'on76nVZ/MyEFWj7he6M6n8A2I5/gr8LMvR/H8yyLp8XvITffkJq9P/53/+beTWmly9Dz929a3b+Ko2mzUUG5vG2L4OXr4ySNgLL1'
    'i7CIjlE0HQq2YMf5ZETDHDnpew83i+K2jDKaZM8CWATeS+UQY5HMzjfFFCihktYSx96VYgNTV1431Id0ZieZWxOYiRPfgIco10B5'
    'rC0O4G8GKKRiuy+b1JtMlC0oRGtQ05G0/aD53phZaI2CIW1zBYcnY3HIPYFD3aYqNyY1VcwK8MfkzNjNN4Tb/426QbhgGl3dkITl'
    'Q8Vh9oZFvWmrW2trJemfuYpigeznUvJ8gaDtccFrkkARO1cQwRJpc2quM4EbLyZwUmrnBuGxV3rns/dj0LQbKyr0SNlonzgeMTvZ'
    '4wYgjtyRQxMXdgbzLogDfUB/VZGT/NeSmkGakI2rCdnCD9P5sXxGf5TGXk7ZdA8nZ+F5giX8+Df/eQllq/4Y0SQyPv5yJ1BB11j6'
    'RWVMJoji+1clVZZ2gx194ZbTILnxToXc6DUn2uagazhejay8lIb63COL4bjMsS+ClKn4ferWEUXY/BZNU9dCskrKkVEdIYexfbzQ'
    '6uIYamQSLX8OntGqKNVoGd4By0cynsmePuXzZPs+GyarYC4n0OmXvnHBTT890lBNBTh8A+jn3XEw7WiilHQrJyDVH3cukmC25Iij'
    'zQ0FsbJDTz57H32+fnVj2ankTodxllOmlH51zJfyb/lsF6sDcjd8b4Bv0i7/eaUrBVafb+8HjaPu+Tc/3XE4Pc3OOuvQDyunDW54'
    '44H0w7pj40qqieVn2Dvg6IPVk/s3pHhiJ4tnmxsbs3dbCwkwDyTEzkKIf3qjL/sYBI9dhfSz+XH5U017DHo+4mqEnH5wjBSNXBSU'
    '+nK0s+HlavVseCn4ir/qICfGcvAAPzvr2E/WFvFzvVmG6KoeNrweNj6gh1teD7c+oIfbXg+33R4E6N+zwp3FyGfbXIf75TgNi6IQ'
    'XsqOpD87UehaFkm9lcYWKVe765s6+lbKp8MOfdvck0rNXg7O3Pgvf7+hTpNoyDZ/kD8XnfTxgnOBFC3cPOFQkC1drpSwkjSJyeYX'
    '3pmbme9GxJc6MDZtrt+iFlxdNtk8D5Jmp8N9brRMT5trWywZE2XGJc3meveLLYfSle96dbSN1OJyL2O7944Th0YxaSvPZ71yPrda'
    'NKgpgiiFcSVfDCTqJK/6airRhpzeC0UZXcpoSzQuwWs2TgHuN3Ka6ThfMA8ZuewjV+7w6f0b8uNGqU/sLfVVuDIl/WVEAuXDhjWF'
    'bRJ5vfGJd9drDhnpM8QxRizJqiCJgs5MvOLAghZ1nCXzkDrlk1bq2RV0RRTRqlNDj+MJugugZQTdUaWgu+AjuDvIR/ir5kdG3x6x'
    'vk2CENe3aN78bnrztN0AfvmsSPZaa9Uuu/K5QVEqMhTUP7gb9uDCGWHZsfTP4O2VZ3Dj+mfwjnsIjyRzEpxOU5PZxHgeGIcQCQbU'
    'bhEAebf6KFYfPfWSJG1JCsupoeACYtMGXupzmYQcWw4nRimTe92zN4rCcX7u7rFw4+kWIvjYiRs6ijl9slBm4q86SfjXpMn8L/+t'
    'QiKYKAmHxelxM/szmiIPl9MLPyjKJvLQP1KMknBqD5P7N8IuwuFRM4CroQ0Kbc+D8TzE4f2e0Lnpe0y0ymeVh+PxnXb3QQe73NMW'
    'kPfFDA4U+7R1zVaph7fhJQJ379+IRk14/2ZdegJjHPvNN1r0feWXqCjLPt1hRvONR6MbH30zH8EfRB1MV21kPMtuPGjS/3Klt9ZP'
    '20Z2QoGuXmsjZYq6hsWUdLCxOr788W/+Q71d1Q4vNfZVt3R2tuZ2lHfhLJoSuPYQc4F6NtO30KoyXecEftRJdMrVBrhSQZWoXEkc'
    'bxWJ461NVXCC4oIERA84XTRt0WVbaW+U+qRz43dAOpHXz8xZSs5hhwtU9HrEEokZGf2FUBpc9YglHA4KTmJehffrU89U/PzMwZLt'
    'WNI+iS+gNCxAHP/41jnASr1MIkRrqUeXy3TYGse4dJBrHGVxkao8yYWzzNW3OX4FjLzUdsHx1U5aV6X25fMrTRcf3+IBFlmojnXt'
    'Q3ZlW47f72FL9MGvsyfP87y7+qu6+6KJyg8/QK6rsTm6ff3diZPTYBr9hqOcqnap/pHclqF/p2eyD0e+38PeswOheSiaET9ajgZE'
    'Hf8izXBTRPs0qYsC3HFtBODW9bdfZv1bO52cI/H3sD/sqenvTxau2J3Pb99WX365tqbW+D91t4eHqr093Lr+9mTh+Kcdym/E0fAj'
    'SrI7STDKfqdi7BAj1hRiH3NmBZ5jPbmVO6ftcz5s1BBi+bPri7Cu3OkaBfeD8+hUIk3/kG2C1vg5RWRVhJof92Ghca9g4Amr7ltn'
    '+y3f8d5eroiixwZrNYyzdPnd0p+59zaqa8zmzj1TOM7dXbW3Ow3HTu6704xeWzea1Lq6VrjdIJczxyqk6p6aLmtpHXRSvsaXtler'
    'LskWLASXK9dajBRFz/Stm4ZFxQoh12vXYfirY1G4KfnxH/4OdyGpmbO3JyzT30znx7lLz3QU65tse/PyatpZf+34f+Kj/spbyfxW'
    'xPUjo7H649Vum+ZWJL9g06O2zPCF9WLeYmcwH/BILYlAKTRX5gN6ZSDSEyTX9nx6huCYJp16Fd1f31LRvfvA7SzOgjH9+vzzlr9p'
    'fC+zeFFv8ruHz95HV2+c0IpP+XGLlc5oOneiEiKNbja8nFtWXLAinrsD/3QTssErot4uJWGOSmNl2zhJMHGDjVLT+h4b/+H0w2km'
    '0KAmjxOS+fW19rJ3xanxba4+OK2WntaVOJ2vWo75zKwFsNA0SP3iFyri81o9YgUkeMjakLtiR1Pj59pJxNedadeG+oW6jRCKJBzh'
    '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'
    'kxNUaAWihbXHrmmrM3DYzJMNFs1RlvNHZQMoqM9GH1WphIvq6M8w1+xrINkWsJ/QQxWUTkGlaingLKM+oyq1e3CnytJWJdzy58MW'
    'bRtOY4D1CtxH0qXRkvTiImSWiiv5nBh8Y88r5ktpxTB0IDVl86XzujvIpcnYx+CXnBN/QSimXW0cLGMdWYNUZBixh3Vfjc+Ddjld'
    'WfITIJ0aFeHdTeGd1uahSyTGg5mw/PmMMHJR+VlgLrnK0goxSdczEaXIFy1Yr1sJTqxWtN/flFbIbbCyFSsRw8RWtCdhZUvaQ3BK'
    'S+xgWNmM9hqc0gw5HVa2oh0Jp7SCfojVM6xcC6fNMHkmVo9IuRtOG5HyVqxsybohnIw4ypmwsiV2Epw+NPYxLGtmcdHb77ViL/Iu'
    'YmB7OGk8bpQkQ6OQ5Izeda4l+RWl+8riwfsYAzZ4I/jpZ6qh1mUKpDrDHOoY5N5Lzz1At8HVIKHYnVChi/ZH8tvrIUXFqNpe1op6'
    'dTeKmBMJsxDbzUqddXfLBLu8EIiPZ+507A379lE5S+Wt6NLOqNv75afoQjIsYymjs3cJ6YQXSZUxne6roE6BFYhB8fYkdpbKjVEn'
    'uejRFVXWaMUkPaAo+bUri1kCxaOiuDH95lFr2TAIBN08FsNOubeQa9ZdlYpfoiUVlqILN3eT4w11Fjh+jiOy0MBnqz2LyJLfOLCC'
    'ZYsuAxVLp8nyhobco6ltqEkKTmidk9W1RGy3S81yLFSiMLicX1ASBZocrwCGNHzyibNh7fFK6mJ2+Wsdre+XvcP1OGYnlbASCzR7'
    'MIs6SJi7eDqW4cpMrXFUw+rm+DsdaBv+bE1OR/rJbXCXFDym2EjVaJ3IjejVT505wZtmn1plzYDHoKxYzdhMfjTsxmdiJmjH5fQB'
    '0EYjzMevBfdTzPSokbKWs4ktmfG7oWopqRH0msZglaGqjZK5iVmZhYx8i6HLvhiTe5hRHFDtvV42Ds3mvecZOuZIcKGvM8KqeG0n'
    'Wv3Usz0cq1YDw2o9uOmNF7D90yJm9fCWEVC6hj+403UJpdaQv0EO0Sd3hv1Qj6fAXheVYpydBY3xseNC+szK5W9imljvKLrwKFfs'
    'L2ipeeQEP4Bv9qmd+Pa+eXI0JWS60kza8VS/ZcrckkFJV0tzNuxNq4odox+9NjPVnRapuYG5POCehx0ql1etJy/ULNOI2yFdOMCm'
    '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'
    '0++zJAA='
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
        f'window._SF_NATIVE_TITLEBAR_OVERLAY={str(sys.platform == "win32").lower()};'
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

        elif path == '/api/window-events':
            seq, event_name = _current_window_event()
            self._json({'ok': True, 'seq': seq, 'event': event_name})

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
                inc_notes  = data.get('includeNotes', False)
                open_pdf   = data.get('openPdf', True)

                html_src   = _build_pdf_html(
                    title, cover, lines, fmt, inc_cover, inc_script, layout, inc_notes
                )

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
                    # Keep a dependency-free renderer as a genuine fallback.
                    # Packaged builds must not bypass the browser renderer:
                    # doing so discards the editor's measured page breaks and
                    # produces visibly different spacing from the BBC layout.
                    pdf_path.write_bytes(_build_basic_pdf_bytes(
                        title, cover, lines, fmt, inc_cover, inc_script, layout, inc_notes
                    ))
                    rendered = pdf_path.exists() and pdf_path.stat().st_size > 500
                    if rendered:
                        if sys.platform == 'win32' and open_pdf:
                            os.startfile(str(pdf_path))
                        self._json({'ok': True, 'path': str(pdf_path), 'renderer': 'basic'})
                    else:
                        self._json({'ok': False, 'error': 'pdf_render_failed'})
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


def _build_basic_pdf_bytes(
    title, cover, lines, fmt, inc_cover, inc_script, layout=None, inc_notes=False
):
    """Dependency-free BBC-style A4 PDF renderer used if Edge is unavailable."""
    import textwrap

    page_w, page_h = 595.28, 841.89
    # Courier's built-in font ascent places visible glyphs about 10pt above
    # the text baseline. A 758pt baseline therefore matches the BBC 1in body
    # top on A4, while the page number remains in the separate top margin.
    left_default, top, bottom = 108, 758, 72
    leading = 12
    source_lines = layout if isinstance(layout, list) and layout else lines
    if not inc_notes:
        source_lines = [
            item for item in (source_lines or [])
            if not isinstance(item, dict) or item.get('type') != 'notes'
        ]
    pages, ops = [], []
    y = top
    page_has_content = False
    previous_type = ''
    in_script = False
    script_page_number = 0
    is_audio = fmt == 'audio'
    radio_cue_y = None
    radio_prefix = ''

    def add_at(text, x, at_y, bold=False, size=12):
        text = str(text or '').strip()
        if not text:
            return
        font = 'F2' if bold else 'F1'
        ops.append(f'BT /{font} {size} Tf {x:.2f} {at_y:.2f} Td ({_pdf_escape_text(text)}) Tj ET')

    def new_page():
        nonlocal ops, y, page_has_content, previous_type
        pages.append(ops)
        ops = []
        y = top
        page_has_content = False
        previous_type = ''
        if in_script:
            add_script_header()

    def add_script_header():
        nonlocal script_page_number
        script_page_number += 1
        if is_audio:
            label = f'- {script_page_number} -'
            add_at(label, (page_w - len(label) * 6.6) / 2, 36, False, 12)
        else:
            add_at(f'{script_page_number}.', page_w - 108, page_h - 48, False, 12)

    def draw(text, x=left_default, bold=False, size=12, cols=58):
        nonlocal y, page_has_content
        text = str(text or '').strip()
        wrapped = textwrap.wrap(text, width=cols, break_long_words=True, break_on_hyphens=False) if text else ['']
        for row in wrapped:
            if y < bottom:
                new_page()
            if row:
                add_at(row, x, y, bold, size)
                page_has_content = True
            y -= leading

    def blank_lines(count):
        nonlocal y
        if page_has_content and count > 0:
            y -= leading * count

    def is_page_leading(item):
        return bool(isinstance(item, dict) and item.get('pageLeading')) or not page_has_content

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
        in_script = True
        add_script_header()
        for item in source_lines or []:
            if is_audio and radio_cue_y is not None:
                pending_type = str(item.get('type', 'action') if isinstance(item, dict) else 'action')
                if pending_type not in ('dialogue', 'parenthetical'):
                    y -= leading
                    radio_cue_y = None
                    radio_prefix = ''
            typ = str(item.get('type', 'action') if isinstance(item, dict) else 'action')
            text = item.get('text', '') if isinstance(item, dict) else str(item)
            is_play = fmt == 'play'
            page_leading = is_page_leading(item)

            if typ == '_break':
                if page_has_content or ops:
                    new_page()
                continue
            if typ == '_page-num':
                # Page headers are generated by the renderer so the title page
                # stays unnumbered and script numbering always starts at 1.
                continue
            if typ == '_more':
                draw(text or '(MORE)', 252, cols=12)
                previous_type = typ
                continue
            if typ == '_contd':
                draw(text.upper(), 252, cols=36)
                previous_type = typ
                continue

            if typ == 'scene':
                if is_audio:
                    blank_lines(1)
                    scene_text = str(text or '').upper()
                    draw(scene_text, max(72, (page_w - len(scene_text) * 6.6) / 2), cols=60)
                    blank_lines(1)
                else:
                    if not page_leading:
                        blank_lines(1 if previous_type == 'transition' else 2)
                    draw(text.upper(), left_default, not is_play, cols=60)
            elif typ == 'character':
                if is_audio:
                    blank_lines(1)
                    cue = str(text or '').upper().rstrip(':') + ':'
                    add_at(cue, 72, y, False, 12)
                    page_has_content = True
                    radio_cue_y = y
                else:
                    if not page_leading:
                        blank_lines(1)
                    draw(text.upper(), 252, is_play, cols=36)
            elif typ == 'dialogue':
                if is_audio:
                    draw(f'{radio_prefix}{text}', 216, cols=48)
                    blank_lines(1)
                    radio_cue_y = None
                    radio_prefix = ''
                else:
                    draw(text, 180, cols=35)
            elif typ == 'parenthetical':
                if is_audio and radio_cue_y is not None:
                    radio_prefix += str(text or '').upper() + ' '
                else:
                    draw(text, 216 if not is_play else 180, cols=25 if not is_play else 35)
            elif typ == 'transition':
                if is_audio:
                    blank_lines(1)
                    draw(str(text or '').upper(), 252, cols=42)
                elif not is_play:
                    blank_lines(2 if previous_type == 'new-act' else 1)
                    transition_text = str(text or '').upper()
                    transition_x = max(left_default, page_w - 54 - len(transition_text) * 7.2)
                    draw(transition_text, transition_x, False, cols=60)
            elif typ == 'new-act':
                if page_has_content:
                    new_page()
                act_text = str(text or '').upper()
                draw(act_text, max(left_default, (page_w - len(act_text) * 7.2) / 2), True, cols=45)
            elif typ == 'act':
                if is_play and page_has_content:
                    new_page()
                if not page_leading:
                    blank_lines(2)
                draw(text.upper(), left_default if is_play else 250, True, cols=45)
            elif typ in ('act-break', 'cold-open', 'tag'):
                blank_lines(1)
                draw(text.upper(), 250, True, cols=35)
            elif typ == 'notes':
                if inc_notes:
                    blank_lines(1)
                    draw(f'[NOTE: {text}]', left_default, False, 10, cols=68)
            elif is_audio and typ in ('action', 'stage-direction'):
                blank_lines(1)
                draw(str(text or '').upper(), 252, cols=42)
            elif is_play and typ in ('action', 'stage-direction'):
                if not page_leading:
                    blank_lines(1)
                direction = str(text or '').strip()
                if direction and not (direction.startswith('(') and direction.endswith(')')):
                    direction = f'({direction})'
                draw(direction, left_default, cols=60)
            else:
                if not page_leading:
                    blank_lines(1)
                draw(text, left_default, cols=60)
            previous_type = typ
    if ops or not pages:
        pages.append(ops)

    objects = []

    def add_obj(body):
        objects.append(body)
        return len(objects)

    catalog_id = add_obj('<< /Type /Catalog /Pages 2 0 R >>')
    pages_id = add_obj('')
    base_font = 'Helvetica' if is_audio else 'Courier'
    bold_font = 'Helvetica-Bold' if is_audio else 'Courier-Bold'
    font_regular_id = add_obj(f'<< /Type /Font /Subtype /Type1 /BaseFont /{base_font} >>')
    font_bold_id = add_obj(f'<< /Type /Font /Subtype /Type1 /BaseFont /{bold_font} >>')
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


def _build_pdf_html(
    title, cover, lines, fmt, inc_cover, inc_script, layout=None, inc_notes=False
):
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
        if fmt == 'audio':
            if ltype in ('character', 'parenthetical'):
                return 0
            if ltype == 'dialogue':
                return _wrap_lines(t, 48) * 2 + 1
            if ltype in ('action', 'stage-direction', 'transition'):
                return _wrap_lines(t, 42) * 2 + 1
            if ltype == 'scene':
                return 4
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
        if ltype == 'new-act':
            return 4
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

            if lt == 'new-act' and pos > 0:
                out.append({'type': '_break', 'text': ''})
                pos = 0

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
      @top-right {
        content: counter(page) ".";
        font: 12pt/12pt 'Courier New', Courier, monospace;
        vertical-align: bottom;
        padding-bottom: 24pt;
      }
      /* BBC spec scripts do not carry a footer. Browser URL/date/title
         furniture is also disabled by the headless print command. */
      @bottom-left { content: none; }
      @bottom-center { content: none; }
      @bottom-right { content: none; }
    }
    @page cover {
      counter-increment: page 0;
      @top-right { content: none; }
    }
    @page radio {
      size: A4 portrait;
      margin: 1in;
      @top-right { content: none; }
      @bottom-center {
        content: "- " counter(page) " -";
        font: 12pt/12pt Arial, Helvetica, sans-serif;
        vertical-align: top;
        padding-top: 18pt;
      }
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
      page: cover;
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
      font-style: normal;
      color: #000;
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
      display: none;
    }
    .el-transition {
      text-align: right;
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
    .el-new-act     { text-align: center; text-transform: uppercase;
                      font-weight: normal; letter-spacing: 0;
                      text-decoration: underline; margin: 0 0 24pt; }
    .el-end-act     { text-align: center; text-transform: uppercase;
                      font-weight: normal; margin: 24pt 0 0; }
    .el-new-act + .el-transition { margin-top: 12pt; }
    .el-transition + .el-scene { margin-top: 12pt; }
    .el-stage-direction { margin-left: 1.0in; margin-right: 1.3in;
                          margin-bottom: 12pt; font-style: italic; }
    .el-tag         { text-align: center; text-transform: uppercase;
                      font-weight: bold; margin: 12pt 0; }

    /* BBC stage-play conventions: cue around the middle (not centred),
       dialogue directly beneath, and mixed-case bracketed directions. */
    .format-play .el-character {
      margin-left: 2.0in;
      text-align: left;
      font-weight: normal;
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
    .format-play .el-scene + .el-action,
    .format-play .el-scene + .el-stage-direction {
      margin-left: 2.5in;
      margin-right: 0;
    }
    .format-play .el-act {
      text-align: center;
      break-before: page;
      page-break-before: always;
    }
    .format-play .el-act:first-child {
      break-before: auto;
      page-break-before: auto;
    }
    .format-play .el-scene {
      text-align: center;
      break-before: page;
      page-break-before: always;
    }
    .format-play .el-act + .el-scene {
      break-before: auto;
      page-break-before: auto;
    }
    .format-play .el-act.page-leading,
    .format-play .el-scene.page-leading {
      break-before: auto;
      page-break-before: auto;
    }
    .format-play .el-transition { display: none; }

    /* BBC Radio Drama Scene Style. */
    .format-audio .script-body {
      page: radio;
      font-family: Arial, Helvetica, sans-serif;
      font-size: 12pt;
      line-height: 24pt;
    }
    .format-audio .el-scene {
      text-align: center;
      text-transform: uppercase;
      margin: 12pt 0 24pt;
    }
    .format-audio .speech {
      margin-top: 12pt;
      line-height: 24pt;
    }
    .format-audio .radio-speech {
      display: grid;
      grid-template-columns: 1.5in minmax(0, 1fr);
      column-gap: 0.5in;
      align-items: start;
      margin-top: 12pt;
      line-height: 24pt;
    }
    .format-audio .radio-cue {
      grid-column: 1;
      text-transform: uppercase;
    }
    .format-audio .radio-copy {
      grid-column: 2;
      min-width: 0;
    }
    .format-audio .radio-parenthetical { text-transform: uppercase; }
    .format-audio .radio-parenthetical::after { content: " "; }
    .format-audio .el-character {
      display: inline-block;
      width: 1.5in;
      margin: 0 0 0 0;
      text-transform: uppercase;
      vertical-align: top;
    }
    .format-audio .el-character::after { content: ":"; }
    .format-audio .el-dialogue,
    .format-audio .el-parenthetical {
      display: inline;
      margin: 0;
      font-style: normal;
      color: #000;
    }
    .format-audio .el-character + .el-dialogue,
    .format-audio .el-character + .el-parenthetical {
      margin-left: 0.5in;
    }
    .format-audio .el-parenthetical { text-transform: uppercase; }
    .format-audio .el-parenthetical::after { content: " "; }
    .format-audio .el-dialogue::after {
      content: "";
      display: block;
      height: 12pt;
    }
    .format-audio .el-action,
    .format-audio .el-stage-direction,
    .format-audio .el-transition {
      display: block;
      margin: 12pt 0 12pt 2.5in;
      text-align: left;
      text-transform: uppercase;
      text-decoration: underline;
      font-style: normal;
      line-height: 24pt;
    }
    .format-audio .el-notes {
      font-family: Arial, Helvetica, sans-serif;
    }
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
        'new-act':         'el-new-act',
        'end-act':         'el-end-act',
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
        raw_script = [
            item for item in (layout if explicit_layout else lines)
            if inc_notes or not isinstance(item, dict) or item.get('type') != 'notes'
        ]
        processed = raw_script if explicit_layout else _inject(raw_script)
        parts.append('<div class="script-body explicit-layout">' if explicit_layout else '<div class="script-body">')

        i = 0
        page_counter = 1
        while i < len(processed):
            line  = processed[i]
            lt    = line.get('type', 'action')
            txt   = line.get('text', '')

            def render_text(kind, value):
                value = str(value or '').strip()
                if fmt == 'audio' and kind == 'character':
                    value = value.rstrip(':').rstrip()
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
                        if item_type == 'notes' and not inc_notes:
                            continue
                        item_text = item.get('text', '') if isinstance(item, dict) else ''
                        item_cls = TYPE_CLS.get(item_type, 'el-dialogue')
                        parts.append(f'<div class="{item_cls}">{render_text(item_type, item_text) or "&nbsp;"}</div>')
                    parts.append('</div>')
                parts.append('</div>')
                i += 1; continue

            if fmt == 'audio' and lt == 'character':
                block = [line]
                j = i + 1
                while j < len(processed):
                    next_type = processed[j].get('type')
                    if next_type not in ('dialogue', 'parenthetical'):
                        break
                    block.append(processed[j])
                    j += 1
                radio_cls = 'radio-speech page-leading' if line.get('pageLeading') else 'radio-speech'
                parts.append(f'<div class="{radio_cls}">')
                parts.append(
                    f'<div class="radio-cue">{render_text("character", txt) or "&nbsp;"}:</div>'
                )
                parts.append('<div class="radio-copy">')
                for speech_line in block[1:]:
                    speech_type = speech_line.get('type', 'dialogue')
                    speech_text = render_text(speech_type, speech_line.get('text', ''))
                    speech_cls = (
                        'radio-parenthetical'
                        if speech_type == 'parenthetical'
                        else 'radio-dialogue'
                    )
                    parts.append(f'<span class="{speech_cls}">{speech_text or "&nbsp;"}</span>')
                parts.append('</div></div>')
                i = j
                continue

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
    if sys.platform == 'win32':
        # Keep Chromium out of sight until Skript's title bar is covering its
        # client-drawn controls. This prevents Edge's Downloads button or other
        # browser chrome flashing during startup.
        base_flags.append('--start-minimized')

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
    if sys.platform == 'win32':
        extra.append('--start-minimized')
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
                _set_windows_app_identity(hwnd)
                _set_windows_window_icon(hwnd)
                # Position the still-minimised app first, create Skript's native
                # title-bar cover, and only then reveal the finished window.
                # Edge's own Downloads icon and close button are never exposed.
                user32.SetWindowPos(hwnd, 0, x, y, width, height, 0x0004)
                overlay_ready = _create_native_titlebar_overlay(hwnd)
                user32.ShowWindow(hwnd, 9)  # SW_RESTORE
                user32.SetWindowPos(hwnd, 0, x, y, width, height, 0x0040)  # SWP_SHOWWINDOW
                if overlay_ready:
                    _sync_native_titlebar_overlay(force=True)
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


def _post_native_window_drag(hwnd, user32=None):
    """Queue a non-blocking Windows move for Skript's browser window."""
    if sys.platform != 'win32' and user32 is None:
        return False
    try:
        import ctypes

        class POINT(ctypes.Structure):
            _fields_ = [('x', ctypes.c_long), ('y', ctypes.c_long)]

        u32 = user32 or ctypes.windll.user32
        cursor = POINT()
        if not u32.GetCursorPos(ctypes.byref(cursor)):
            return False
        packed_position = (
            (ctypes.c_ushort(cursor.y).value << 16)
            | ctypes.c_ushort(cursor.x).value
        )
        u32.ReleaseCapture()
        # Queue the move instead of blocking Tk's callback inside Windows'
        # modal drag loop. Skript can keep its title bar and renderer responsive.
        return bool(u32.PostMessageW(hwnd, 0x00A1, 2, packed_position))
    except Exception:
        return False


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

    # Skript's titlebar keeps an exact handle to the Edge app window.
    if _titlebar_overlay_is_active():
        hwnd = _TITLEBAR_OVERLAY_TARGET
        found_hwnd = [hwnd]
    else:
        found_hwnd = []

    # Enumerate top-level windows to find our app window by PID
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

    if not found_hwnd:
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
        _post_native_window_drag(hwnd, u32)


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
        while not _APP_SHUTDOWN_EVENT.wait(0.05):
            _pump_native_titlebar_overlay()
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

    _destroy_native_titlebar_overlay()
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
