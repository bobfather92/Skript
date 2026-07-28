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
    'QQh5opTzlrjkPLnos1ntvfeHfwYpTCPpntaL+SZbx+yOMsQYd3KhUoSqp4ArB010Yp9Z04cYOLrQ0MmeBEY6HCS9s7Uf/ub/Ng6n'
    'fMqDTvBHlEjOoDJa11YMuxBLDndOJSSGuW4puSzyg+CORjGTlsRmBcQhDC8njZZqlElynaGjF79ZnXlyC83cz+Qb9qiK5+SVZhvk'
    'ZIgKC/ZGFzNrFAzGY8g2/VDFqNcfDbM1UXEKT2hoMMOMEXsnaJNHLBinfz9j5QBNegRydSbDswvcCYzocB6lFWbcdmVhI2RYwpGP'
    'OXt0Cxu36nz/2kuTGDYb86NpV1RZyjF/m84CbZKdk0IPHN1cgycta8ph+jNr/9//8z+SwIzvHzBkynKOAJOXs7Ga2SV675azimAh'
    'nJw1Jzfry+FgLZOuFYqawM6ZaH7xcnZ4PkVhpHogsTd7rSkr4PF0Zg2vLqesgEqGmTW+o/Pwjm7KenidMrOGV1VTVsDj8czaZp2N'
    'tfH8NOvVyEp7SgB08QI8bK9Vb0Ld+r862NrHcCtTtx+jhV62LLxz5g1LZeb35RCt3gQHprXE4pnUv7CVQ9Q1M7kY4cqSK3Sj6F57'
    'v/QWSIgjTo88AD6VMUpbwYjaaXPBbYp/Q27ZSPmVJ7cICA6t9+91cc0MhwM58ie3APxe8kCAhK/wL0iS9w7Zd010dZlMdUOAku7E'
    '8kypDJ36m1dl7WVKejqjKnLAMr+dcSYGFj8dEwxWZ/A4PZCSV0Cyd/ieO81Pbq2LfXJ/HuJUvX+ZkFUJ7MUwLwQUwa3D5FC3QCKq'
    'wmZsiA4+jI3rrL33K79Jol6xUPDvHRri2mt/TDTgYp4GDeaVPCHiwkbEhUQEAhyPiIufLSKQO02DCL5qJxTENgpiiQIENR4F8Y9H'
    'gSshjJEJsC/IQ115wPMoFgO6jISD1RmSZbvaVuqH3/9TFo+uBDEOjQjHReOPHQOx8QcGQeZdJS/87Sjq47HoRw1Cped5cBQZaQT2'
    'jKwcYmhlVIu6QX+Gj1irM4buCT0D/kEJKHbbtP0oPn7v50i3s7z1wF+URSzL+Pe2p7S8+TPNkhFO5rRP02EZahTTuzv0MFOxPf5q'
    '9qxU+Kvgor9ivn1Jb+Oh9XKNXp7ZL2fo5W9HCb52lEB1inSIZlpQOOqxd16xr3KalDkEKEfF973PqzDmxvGSo2jfWf1JT9H511HW'
    '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'
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
