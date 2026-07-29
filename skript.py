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
    '18LV8g2pENDEOoKaZ5R7mHT4B0/7/aND8qKkvtDWiQW1tAVNFel1D7q7/bzKeKipc9LtWCW1Oxa/ztY+6DzoHljC7LtmSMmaJh/Z'
    'kLXq3FL82qY3OdfuysHEBZ9xdlAZpv8CJHZKZqfgK7V63DFkFCHnGaHFyH0TgmABTJnyphFjSXgxhe+hqy9DwWSUzVA2eL044FQT'
    'EKyJI6lah5G8aunIHtB4skA5QhqTdMdEKG/lkMovkhqFXgKtJf5hc+56T4Z+l+oOqyItNBPyuidurbfrhVJeI0OomOUpicSTTGXQ'
    'UnxA/FzU2MtdN3JhckieUFR7HdpmjxgyPXOeSPN4oKS6cjiIk5HzkDFCQWmGBHD4bfZRBDGnFUb+7DjwQZO02WZOBuUPYUzQFGrl'
    'nSgCHMIIBEsyQqY+y0rKT1Cx8ofsKquthoNdDqDgCIbntWfWyovasz+Ff2/W8fl5fVUbNNRG5JCuHLNuxt+f+g6VwRipV1jxYbLi'
    'EobKe8+58mC5Y07Paw8I70sTLpEeMuSSZQWGtOyEDYEGq4wtwZ8gOWIuAOyB20RDdeAk7RB/YROXuxBfAQvBDKzjUdCiOqDhxCOR'
    'fAdsyTBKGgkcz6W9RZBMJPkC9wyNVOhLSgMrVOwpFmNqQbVJ4aHaTfRHSdl8Nkev79gJeLdAccGxNncUxmoTLmkIISFdX/EOHYBD'
    '2s6jwD2NxGQOCM7egXA+w+20kKYGLbauK0IBdkuQk3LZSJri6Rn0BO1ledP1qPWa9AmA3kUsQYipJY2BEaPL4ELgMT1avcEFUgW6'
    'RjyPkbFpCilo0g3DOZaIj41IzLpANk8xM82mCpSJUVbG1oQtk3Eg/lZkHKdTg3H8ae35+c368/Anz2s6g4BSCYNg//Oz0ynQ/YvC'
    '7UCjVE3fGyvnEqOW4D1E3IsJPxbTx+xZlbE02UE1MBN+ZxuWG6rYgfLOEuiSn7znmrTDNTT+W3G/tdjeTu/EUg9LrUCH9RyOk0Rl'
    'R1B4svb4sRYGG6++Mkofw1rG2uCLamTORLAOfWKdIrLRSQGsa94+qU2dc/FQebzxA24Le16Nek92TN7KHZMFcHcoLMRGDoH7YUoV'
    'kn8/ovqzvgTDVm5setUQLe1XWg1ar7YAWFJJ2wpaxGlLpf7jbD6kOuDtFMQU7VnmxccCHJ3GWNariJV0OFEjUIMOCMow4C4o5hyu'
    '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'
    '4L1VdQT93iqGoeNfOj/5yf8HAu13xIVmJAA='
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
