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
    '4PiS0TUTDmjMeBv0CKKI65DrbLDg3hOYmb+zkjE2jEG8swb5ziFufl3JTtngsmaL60p+Kadu+H622zyhBgtcYR0l5We9wrrhbU3V'
    'JdBnUrRve4UTaaNhPH/qaFTcahjElVdCb1g0uQ2xCQRZ0moCJgLiUInUVqviZhy3ju5pni2UJtPlq1bTtVxGrtDkdSn26tfJGeO2'
    'zUbzu28e/Nd/XbL/Wt073zW/Yx9X7L8WygyuFzLtKrK7gLabos5WlYPIRDD1h/CIN56WKjIZq8pLswrM0zN0Qy3sSaxvC3DJZEdc'
    '0695WDN8RU6kWoUUVwFY9WGCgN9utnuBc1LG9XBdukkWeDaDoxD8ZSdn7xdx/h6z+E8q+2A5MyDYFwWED+ANsCP5qF4D5jO0UeE/'
    '/CzUeal8/LKA4AFKkmtrNzvBBH0c53mKegCkjQeRnWCBsm3vecKOJQAlf5MA1qwQqVYhGV+GMTKANj5tsGT6/lH2CUH4Tyr76GIx'
    'yeZ64GQ6VfBNmc4NePi0wLL5eoHowR9+1iNQFqr8R1J1qIEWskf8F5H5Ol6eJZyAnJQQsCQkL40qYCwqN4kALzSYPV3EdcBjSkvt'
    'FjAZhpfmFIAdBNf8UQLWXHxbJtPNgk/ii2cZ1i9+OZlH5xliS/60spm0UCYzDP8EBAtgTlII/DU7BtvQLIUCBnXdemnA8gQLVBtN'
    'gWhIZRF369U375WVkGXJIo+Y9HWWgyMyo4hOrC5CtkdlU9UI/6RmUZlEgX+fpzOx17hJFngef+TUKH7ZmdnqcbyS1egvE+jg+avj'
    'v568fPSHg8fHDMr8tMAWq/O4SIvnjNOLCt0kB7y80AzM/LTAeKTbw5m5rv1EoghRoBY4p10idUMha+4r84mKjDJ2tnuJCXBumllA'
    'nLTcVQXfj+GeUuThbwtAhCsPjqgagKrKLOUB4LbPf/hZ+jmo9e0CurPspVUW0LQXyqoszsmESraK5Yw/PVxOGR8Wa8JJ8YBhrBIM'
    'fpsAsL6PVjE0LH+a2b9PYi5O8R9+Fsem6qvoUTAvVAFRjgbX82h9u4DoKALsqzmc/LTBuMO0OW9YflggLHEOGUw0wY3UTrBAszz9'
    'CWJBzF9lBV4aoLQOZeic6sJcFfAhARN0sg4TwKpqVTxP4mKdG8TopVkF5JKXU2B+m4BoJ5YcniJbdU4FwTyrArw0QxqXP+1sHsfu'
    'NZt90U+LW1TmUxW5fSSSrWJLhth4nv4EcohbNpRnV1AkuSMJeWnBAlwWcpNIcCUNOSk2sM/lvTSzADx+eK1e450lUion062CuA4F'
    '9egPG4QvRW8NYgIcKWUm/PYAnmb5SxGDRMIZSRQ4hIXUkOzLA3IrDNZ2tD49TT9JMP5lAaVLIYy/TlBDo5unc9zCwHQk9oxPE+w5'
    'f4QCf33ZdzMeLs/myexRDkFCUNLzE90ij9f5/MIpYaW5BZ4kZ3mSCEj+4YMss0W6FCcOJ8UFfgoH1RR1UeanByZUhhJMfIbAXnCv'
    '125SCBzsy9jySZPCKaQz3KKwgs7yeC4KyE8X7BnY8AkY/E0CPMs+JrkJhQkk6Bux59kJLigjtiQ3JkB9u4Cv8uRoPTkCl+JHaHwk'
    'CnjpbsHXbCudquGLrwCQh14v3SsIBxqHLK00r8BakobD/SDp6O9rMNq3q7MTvSJs8CY+1DcF6GGvGnVH64WCW/iZfmV0TcI0Cf+2'
    'Mph0cC7O8Oq3ByDP8frDBAGrGLWlmtsfnWEVzXBfYDvLObqMt74tQGSIikeanzZr4zkWEblJPjhei2nBx0/0iySzwzJZmDI/mb6x'
    'oDMkMtevhB+jSWXOy+XL01M9FvPTAmMb11ydt40vE0jFktKhpHQW29NRF/okLVbz+AKhnDS6wEv0QCpEVCqZLva3l0JF6ybR4IUF'
    'WXhAQk4hZROV+Cg5ZQKqCcZTXGA+EwKOf9AgemK8NLqAqY8jUt1CL/NUhuYVBYwUF9ikXuvbBQRB8UmaJ1OjXiutsoCgMTLdLii9'
    'lwCw+E0CWMubSN1Q6PE5qG3pojxvQwWGfqwil6yE7Th0760Mu6h+Gqx+WwDibBfPmfgPQOZ3EFDdCrklVEaw6DN5uidSg4XkyfM4'
    'cwvqHKuwHdLe/DTBZGH/qIvuWUOZVBV/AtxPyQrcLKs4ShOOJOFOc3B2rQxFmERqsJBBjGS6WfAo8UVYL62ygOpiIIcoLGbwiF71'
    'JoMj2dpR8vc1PICP54cz+Ps0TTisn2wVO0f9jWxcf1lA6WI1TzDIIgDpLx/oeZzySzUb2k62imWnpRJs9IcFAtcFsofytwWA1jmP'
    'ebBQPmw7xQc+WK4XjjxDZ/hFyWLhIhdzkE/U9SGWcNKoAiab99K8AlIHoD88kEJm25SL9498carfJsCxuaMdk1sZ56cOF2WfR2W2'
    'MriEk0IAizk2vhygucie+xmWztZJ8YC17GN+emBCzUSql1SiU5eR5IE/iy+ydWn2Uad4wC9PjZCdTooHbLEqJ8UD5sowSgkm0/zq'
    'rMTqIor3hbKs4o7MFJSX0Df26SnLEFD8wwXhlEyo7CAJ1dlssR5x1ZSbFAKXE+YkueATNAIQv6xMsBxjG6MUpq1vE/ANKALh6ZJo'
    '0fo2AeVGK7Xg1ncQ8EhhmUoOFpPrzk8ki+CqM8ExgQKVNhvWdxDwdfIhLfQ+GcwLVkAVDBVwrxnI9KqCzhVDVbZZzZ9fvv7jw9cv'
    '37x4As/0jS8aaGgBDWmgkQU0soDSWSmFZvXbAlidfZ9n6xVfVsaXDVQwwWGVSCD1ZQL9ZTEntR9kulPQgSfB/prEudDQyJ9uttTP'
    'qN8mQKxtxd7gq1DU76XTw9n3KJpU5psVTYTxFFlLONOsYqrNUMhaKvOdiiD2+OESjPyOs+OPaExPpBKFnqfzebpI4LW0W9LLIoof'
    'Z87EkelWQbRCNg9cTooPDMZw1l5FJVPFcssKjUj1C3EDKt2I+PYBTeMOBW0mUkVK0/TCKGWl+wXJUtVF8KKaQJqT7hckr51VcTKX'
    'qIQ6gIay/OLwlNCYMv7pg+nLIcHcqGS/GN7tTKcQfsMQ14N5dAXiws1OoEHFvcQ0tvDg5dCFXzzMKdr3s+ji3m1EoK4KOLpipdZ3'
    '1xeVuaGKQJ+I/HBFG0e47fAUKD1AN3tjNcFu1erTy3UJEqI8APqJfhFQMTLecJZqmtNJNDixmOxkuthR+pNdABIoUHGulebDVLJf'
    'jEkYTzMzfo5M8EFtHYuXRhTgmhANzL8JQNRvMI6lQWUKAbyKp1at/JsA5LoIh8CsVL+QODfrcEL8OwgIdyguMKSRBebJ03kWU8RK'
    'ZQaq4MdduyRPCxVg8pIDzlICwOyoyS2N7BIqOVAMBV8X1V4OUTiPlwV/B2SybzvZL6YOdaqESvGB3YMekRou5O2wVfpZDgHn2xeZ'
    '0TeZQIPyC18LmCfR4MfW5KiUAHC2ericPcrKMlvYZYwMs+gMkM/EUunfzvq2AJNpuojn6jbK+rYAs6kmaVIS3wBhVoYkeP4qS5el'
    'sBeTHQ3kWIXVq1SAVx8mCBP5zpPZIYic8qeVnXxCszrZqPVtASp7NgVqp5jAc3bM+n3ySaHS+jYBF7wCWEkv81dJDoKUrD+YZ1bg'
    'Poazvn1Aba9ufVuAvCW2K8mOOCkWMDFvq6oZW+Ea+8AWdwpPvEDf4BSuyDcrKvg2xXdn4xaDTCcKym3XL+rmWIXhfGzOrJ1ggTIm'
    'lMx+75ENme4XhPMjXdTLsQrje9F8Bv2HV4sPIifFBC6JNsqq2tcg5JvDtxMsUOFDCoDETz9bMYXHwMaQgOkMv+ibdarrhg8HhKSu'
    '9SaqWi85jp84vJBMh4J370bwfrpIZvic8+g9CKZfFWzFg8nSk5eP/xKl3AY070bH52kRsf8w4jHYjU3Wy9k8Qb8VrKLs9BQ3QP7s'
    'VL5DjeI5uCK7iNbQyOQCS/+ZHcpFpxnfY5SedI1R8Aoe8Iqgl+I56Sw5ZZCCM180BXhb3HCoaFXH8Vk7uuRvNMdR43k2W8+ThngI'
    'KR1U8bL7t65azUvIufXNXe5T6ttb33zR6UQocY6jVZ5Ms+US9NMlXGbhk88OvJ6NyiyK0WfehCGLR4OGiKqMMzH+EXU6rKICJNxv'
    'WavjnJ2glW/r6DHYVazieVKWSfS//+f/ihbx9OUR29rYcf9O9DHOF1EySxndpGwSSti4hcvfTmdyNjbcI93uj9i/u/sik9HEaQzu'
    '0UVm0k8GAydzwHNvD3bZv1Mncygzk0EyVNVOUIUi283PJnET3FLLP71ub69lw4pGKNj+UMHyoGxqLKe9JEn2zMyOrCe6He/Fu3HP'
    'yhyqzJ14Z29HdTcG4lb13r63u3Pv1M7sFNkptoz96/f32nv32oPRLnRvp2WDns2zjzTocKRA82RmTMvt2f2d051TmQmWn0vdn9E0'
    'Pr0XK3whkarMncn9yWxHDzOeG5nDSTzci81MNRDevZ377f7usN0f7sFIBqp7WQ4XNApde/G93qnq3mqds4ONyrw/uZfMRqp7rORM'
    'gTi4NDM75+CweuxWboHwzlbi3ILnqK9APFtKr9PJhMnCan3k+C2Xye1+zP5N9u3Mcz7Yvb3VJ1UP3BRN4lxXVPCEDk5+NBj1JLDO'
    '4o3c7t9j/050TdwkccW2YV0bfOm1e5tRxzDRMwCZajHwPse6PnZGzT5GxUUBBzvdP0zuFAss1Iv6q0/RkP1BdPXa+G9XU6gAX8wE'
    '+IiB9ndd+B0Xfn4mqx8w2NGeW+CeKjDN5vN4ItBl4osNgZ1o4oKdLeUWcPw6uhvF/f4F++tj+hPb3Rm6lsm8MPnccGyFCmlqDqap'
    '5WwUArK5TKc/toCUy9WrW7e+ZnvFAsWtMfgHW8Uz7suC/Z5kn9hk/4SfnLF14BJQlGLF2ZbBho1kAofKcQRRBPatjCmI42O3c+Aj'
    'YFnwYEhsE7r19Xjc+ZhM3qdlRxVl/RK13mO4ZKI9HCjEB12iA3cZ71m5iXrrOLZaCpY7ZxIBjsgsSSBUbgVAbUUGkYOtgUiATh7P'
    '0jXbP0ecCnStnekcnAkLLCM6b1V1aox8xRmSnsQO6xZMBzTMZIxL4ZhiWXZO40U6vxhHX+ELjq/aUQdc2jAmhOuoHT2CxxzP4+kR'
    'fsN2344aR8lZlkRvDhttJuAsi07BpLjTfV0pIwbGBmEt8ES/U5Mz5UzDmHfDxa+cxn6v90HE3J1xg9FxdDqX4THhV2cmb8zBY6h8'
    'Bx5hZIBTZI3n6WyWiFSJP97PBZM3zpFuYzQTgvU3EwQPG1RSvC+zVadMyzmyvUu7I0uhGwAHE+flYt4tTjuyDDuEzufBKuTwhgpH'
    'i5RxXC+VGHMMeo9OymaDEQ6c2LiIamOZc1sht6g1CUoDkyjFXGB2aD46ko8wrsQkgmTOcK1HLqagOM/R86qQPFZCxTIWLt0+CNif'
    'OiKe4/1er+cibomAClGdDO2NL+rNQvQFl79jEeuF/em65TqzPD4ThQHbgmv09DjGMkKrQX2/2X4izmK2dNWuqTklq04mgtNTwLOI'
    'shbuc8rkas3h+vdNFse/MpT6O6dpiR5zweZrP1AZOrC/9FcGuh3p6GRGuex4mBb74J25ZMxgheLyMoNAovvWGu9DFzDho+jVLpva'
    'QPvQPca2CtYHC8MOdsU+04EgSmxlrsvMqfAjIyO2605KGYNWoGe0a6EHq5asuLfvMt2eM7NncDvJPWY7sxrcKMJLBnHC+sA4+92+'
    '5pjiEGYzzo3UoMdbwef1BkQx1VCF3emcHWvJam9PR4MJ4yGyOqQFXpFak1i6s8hm7AR2qdd3f9CTVECCdvEv2NY0bbMl2WS0s4JY'
    '4vF82gTO/zHqIDNsuQPglU2zFdvM9AobgLiG/+vv8e2fLnI+kGxACjTsXxQYKMwZ5D6ABQxephPFq/vdwY43YUZbK7ep/QqCMXdO'
    't5kd1YyD0qKMyzWsKXML4QgQC4nBMp5Ljg8lA7PpXgBx/Bld4TJfvmB/XBdgeN0Rrg55cidZsvVEcckwh+QziMPHKoDhKMZDY1l2'
    'rAtJyBJorgVFf4euAaPmIv4k2f8uzKl0ZxUas9kZXduVkKfegnOwzioHR9yMsJN31J4V3q8qxAeovXuaTdcFVhzdnvM7JM0/OXeU'
    'mxeXW9hR4n//v//Pv+l/3HPX8eHxs4Po0cPX7PPfdyz8nPYLmI7Xh48evXzxC5iL21y3IZa7v4kqvUhre9GZkoS3OrPIxSuUNWU8'
    'KSJw52v2vIOpl7VkUsWEPTlUnS+QEfe2H6t7UsGud3UXzSOmISnqRCkt7vR6ISlK6iZUx0EPgwqWe64YjZdR6hxkj2MQOoNHPEGc'
    'VGLGbkHHVqhQZiWcd7iNAsNRdygbpXYXuTVpDCiRit7tHegubDUfEuW00iiC+lWKHDsBMBQRPmb5e+wibhwdEVXbFEVM8dqgHXbC'
    'O7WPM4rMeKjHjqY2LXipk76n+DCJRx4lg8LrwB6nlNR3JJEFBzZZM4yoZa1Efq+1GsK7R3agLrxvEi+ecSDpLhP+tObEVYVUEacc'
    '2bDmyBR9ELgTMy+HAkf/YS/ed8QTu/YHjY85I/zlWeNd1NVZqzybrbmd/CaBBWoeL7OyyavnNh8PGuUHCFMmgr93yg+dbDm/qCX9'
    'YGUgApXZenremcYrsEJpRbf5N+LEOEBWV2guLV4e+tE2clCTauRtqNLizNKLuqmNlfxZ5tl6nr1RXY0OOKpm8+7x7D2KZcsje4dJ'
    'f/AIQDxLiELCszt+d9D7dF+cI7XogVJKYOKVh1tFss5hwUEmEPOK47Cbn4W3tipdX1AV4x1MOJ1PkvJjIlWCvrLH2nFAmW/vkLmA'
    'r9ogDQXTaVrK9kOCAq0w4yg9G8/jgtWA/tAunT7wSRMTe8aO3/AC8PJ6Giu1wVmqMK2CVtupr7DsGd3tzOMJUJYrACgWGma5+IGd'
    'tLtXsRkbKwSOjmqZmbQZQLpDh2ILEYQ4+bkJMYx+NaQdTn1VW2LlLmOqabfXYIUkpEHhUfhoYMl23p2CvTNyOplsVmUNqlRZ+WTj'
    'nog3qW4dcreUlbBjO5OHLurtrP2+V5BWnSW9yd7oVAPP4GY5J2H55X//Xvv+DvzH73ntPufJrKVW+UTohD0BW5GKrTgyUB5cmt2d'
    'auHcX4CDjdIwX1zHQDW5tcKak/QswjGg4Qfr7ntu6tJSi4/t2/O5oaqXg9kZkItE69VxJY20UKXq0niz9HkDpe0yAQWaKL0YH5Xw'
    'yMJvQ7JcjKxAIxVBlaCVEzfb3dNF2ckdGZ+gNnxgwYnWuc9wjwQI6QMJHlEDVg7kaOHPjzpyAiqKhX9jcm+wCrDCnL+odYRnW3TZ'
    'lV+00rCQnpIDp0dv2wldpl7pEdCT3x+aky/AqKnvq6kHCIZdX6YJ7Al8xH2TdKSttSSZdCnRL3CezI2Lja038V1vgYysBULjasM2'
    '0g8foa+5r9TZJ7ZSH1RsVJXndY7tenuRKjFTVmpiReyZ907BLbtKFNF9qdrWjDseaq2rU7amNm48OMuz1Sz7uPSpbdJReZeUGKrW'
    'hwTrMOpdhy7CTUk2njCSWZciHa8g5L3Ob6I7QHktubmcluRh3TJLqqlZsFG+Z3INMVeDnrEYPgkLHoVgac/Tcm6sd3u9KrMCc7WZ'
    'zMfCGoZPMXkHmkQSKIbFfV0GoJe66tOe0JtVC5Kk5UZdXZ3EP8lGiLVZkEiCMd1YLHTQGOD9I5Mn/9vfljx8dPQLuSy5XcYTbeNh'
    'cwP4Z7S9rvraanI8+XOmJQhQGju2GAPDe8N9IJ8MvdKhZXhh20eauhrqekCp0dU+bGp0tGrWM6DTDNdcXPKsDhwVZPQdtcwArUVn'
    'qpwE1T7cKomuAmU4ygGpPfDtbLYcINF52gbQ0WNdaVrqymnDS92ZNhgQGnBlKiDga9YP3EbfdFTKQXXkKJug9fzWUFDvWPzdEpo2'
    'Hezq6Kih+h1cCr1r2kLd23BYrLyJCRmToUTRJzb4vt7gjXv+/l7P2Jo3X9AEtx+503i3NhUlKk0dw5Lc5lsfswXZK250IIwW0Cpg'
    'C4MvVQkuFjGyDM795YVmZZSoIPE8smywAnpv2iykUklG35xUqhNDZwKHBMzx6rH2XWTU094MqpQ3UNeHNPnYKbOzs3lCs61u+aE0'
    'joBmaxzI0u7RS9g7vuop7I4M623gSKgDcbCrZtXEoajDxSPvLcdOW33rY4yNUeCzS8AAQ8UWgwxOsjlSNP9z8WHdUgYPZ6gLMAeL'
    'LQo+FLgavXLGQnMUrXBEcAgv0mFdggKd9RJt/T8nDnyDTGD2NJX4OoLgKtsSNXVP+HW4Am4h6gr4FyKyP394+CJ69vCvL98c/xKk'
    'dmmX5kuAhLAQOEIH7sDEfP+v//lv+h+f72cHT4+jo8MnB+KY9m87HDHh8qBjqcHcU1LQ2kO9DGttfbG65YUcdeoyeRn2HM5KewXj'
    'kZN02pkkP6VJ3mT7JD7dGrT7rbYRGZf/Y3a4I/kh1JEIf0fbUbmhaOorhaDEcTdP+OuqtjC7UAcameGcms3xBR5HqLrxPdpKb0L2'
    'Yc0fpne6MWvjHUo65zE8eBY1VmoERTu5o8/nh6Cec5Xr6qpZh0SLDg6HcqLRuiOealRU93g8nnBn7ip2MBdDv/qqhnLT1LELrYRK'
    '0YRtD4l6IFVppaYBuRTWNnSYtlwWGCF/fyrG2Q7DcaNjYVNiwgcIsA4+gxesnjK2h/8O5DPKQZ+twt299u49uB4dtSqoOESKlKBN'
    'DiU8xq8lWXjk513EeW+lQtdvgouK44BpgqAGIo8KJuHwe0t5yBpUPLQjDeu21KLvbD5qkeLljY985DnTXA5S0VXJvC15teICxsF4'
    'WD+w8fal8uLGnftz7infnnSReEko8nvCJsnT6H9OI+UbGFRdEeM4HxL2Cj1SNbW72SDYt0ZQpzqEK6UTqnG0hmBGU7Enu5hfxh+k'
    'NxhhxKcWvUg2BFoXafWRjqyGW3E61dvT7JksmeZQQOn79DExYPHDLVXT5Tk7bdn3sXaav3K5rqKyr5/hOaRNwxsvjtydr/JRqr3x'
    'L+JlulrPuUsy/tQ+TxZsdRdMUugtiqiMV9EsgcemYHYPZTk5XIXxsPmaSuoJ3fJCO1fzgnt3852bcdwiG6y0fFC68fPkQ+7CVTwZ'
    'M6dGrTdgxQU9bH73STRnLNYcYsonzfu9WXKmVGbuaIwH7NT1s6nRUEazNTpkV09c0fqsA0k9ahaM1hMmiCXltCstmIpJh0Hc6B53'
    'j7Z0Ggll/GCvcuUELgGuoSuNyGezV84oay2HipcQRlVacUiq0TbY+rkTJYIBSmsbNT2xmO7rW9r4E3RvM0fb7nImuOTr7gE1t5SK'
    'ya9t0Gnh9HrkYBCDMT3wGbrAVyYdqL31rYc1OcAihVWbnqEHsnlalFLkgiykPky8tG8pLyzDet49VSCBmLSkkDYSQppepiSr36TS'
    'BftItl+XbFRTSoLhF5QROyzGjgApcgiFnDm0igtY6aJlWyct0h3PHMJMyMcQQGofwX9NXKgrcnlmU95s6KuGwYArVdr2NlMl8RtE'
    'DeCdjB2/U3laMNX3QYk7cOux97N2hWHtz+A8TSIoLSSOkK4KD6PRneiUddqeeeoszGewvQHKwoB75Wds0/iTSVPJX5odbgTxC9LT'
    'Hjw5PH75Onr4+uDhL0FNy/3jdZBBVPACW0e5pYo1YKTDl9ciTpfXaJmLXZUaU//ZjrPbwV0R59fgaUw+eKrLELUk2eOiZM+7ydb7'
    '7GflnjUG5ozKtkOgkOjXud2ovSY3O+KqU6SOJ646tXC/XLUMZk3LZ0M80M7owIZ/jr6aVzGERp6DF24hN8p+nDn6uHv3sTr9D3hz'
    'G0VxGd3fjWarVG5xhj0KL+J4IdETYS2qU/zHEhks93eW44/+YCj7wnvBc/zO2ApXcTlu+63r77TakAfEsNsLuc1jzTx69Biawkeh'
    'fG9i0m26bHPNN9sl7+FXma3uco1J1E+XXdkTRXX34cEdPC/gv/qjkWWq6/uYq+QQlTYN1nYMjuNNAT90uu3veHv9AIw+0N/iCH7d'
    'N5DyKs8WWZlE+Lz043nKjv0/ZRC3/KwbvUryRYzBYaYQDqZIUSqNLyCY2jRGqwDuIRUXcSEvoODRTLZIopSHBy8Z2Pev3hRRvJyh'
    'TqNM7sKaXrCf+QVLAefqrEqF6Y/pfM4O39zPpaa2tMi4emQsflr6sr+xTkfi6W0ECx2WiLBG4vObnQpPrJYoylcLDLnDSrVZykR9'
    'eZdDp+mnZGbfnwzd+5OBSjA9De3f8Lmjb87Ta8N/TIrr7u0FFeeU09YNVuiWdmLXbB9sljun6byENibzdd7cU/bx9jqlPVKOqpy0'
    'XRGzIU7EzqRYz+jl4coy6BqMwmiznd3uboO53l69q4fbs940me75R6rqhyw3vokIayIL436hqHp/F5gBaTdFzIM8RddBt3JjKxGl'
    '3QTjFopVr6Ylf+DUtnvD0jcqJJUO4HG2ziG86qs8XSRftaNFtszwEsBuP+6xf/c848zhrqWqJx77VlsqDcxHvqHHTKSxEtyV2jMX'
    'QI6eERtF7oWQRHGdleCcj6Kjx68PXx1Hzw5fHBxFTbbkpMRxlrQiU4LvAjFZlttRxuPb2JbIoq/oWfxy+1nzrOi0HNMfMMlIFkch'
    'AmQI2AJ27nXvRWwzyYu72C4bBpMBxE5jLwJdp6wRDrVzYQs88+uXApMp2SjSsTHgWxav8qSjbYs/MirpTCDcJFu78Bf4wphViw7C'
    'RYpjiSDozXqwZNuSExYm5lWheQkp6RzWQUi08+aW38u3rTTuIEybERrbRbqEhwkD/o5hnYNIjXEvyLq5I4/yYpU8aKCOq/HO9kdj'
    'yZyWyvKeeoZXdf9G3NxZ2EYzCvQoxOmkZF3TJHIKwSTB0XyCsYmgJS1WV8yWk+r6M+i5xxsPFesJaEa4r5R/Pj7k0oF3JmyNTebx'
    '8j0urkjYVsQomqXLNY/EI/pahZqrzRMfsoSJyzJvIrjQgq4XrWrbGL4uOvrlttog4ng/fCeMY1cMncRTJQFzBXLljHlYrkBYRUtT'
    'GRGvsrENhFBBPZ62vn6/r4O4WRrPs7N19eK3md59TaIDOPWJpQqnZDwKNvvdnkzlQ4JDAmS1nBOgtAAUNWKFPatCft6oJO6KwWm+'
    '/K+YLMPZs91xPYsBhuBuz5vGiVbm3hAHs7343qDqfoEQM61gCY5QL+Z/aEv2VomR76Ug4LpBakEIfzvy5lG6eKl4h6L8TkCwOxTn'
    'uFcGrmWMmsW5eAYtvKaion1ZlIxrtmwtD2634/i0TPJavqEO8DIIOTP6ED7P5squx6oTb43Q2xXfzVubma1RoSPmTyYTyX9RXO4k'
    'HxIMyWIbgihyHfV6vro+OvjEWizwopThQyDpI1xGKO7GR5YWkZA2bDH1NhB/hYf0G3nGGa0If3PGSw6XZO/3232QvvtDINl7NsnK'
    'Z2MmxVoFVJiNoIVPRZnt/Rr0tvBYZMvDg73NyrErY24qHHIZE9iFH9ILBm374dtf7RjOhgULH6krWZKRemYmAR/i2C3ymRAxC9Ua'
    'Bwt2sNPa4BCjpu+KLQ5W/Wo6rvt23nh7JbATfplmj7nq0l1UJYikA9L1xvp2PEtIH2gn2Ogv4yHP45d/OngdvXr4/cEv4B1PdwqE'
    'hE8UKy6TbnR7VnFVtvHiCwnmj0kCYdMi8eQoLnFdlGz1FVETQ40Vqte4WecJ16SjhZ+SONGqI53jHbd5BelefIf31dCJBw/dqrzS'
    'VHe0hZ7G8ue7uTPHY7mCNJ5fkgMyJi2gDBED0oBqTDKJC6N8WP/S27Gf7yZsgDdhezLAgJ255z7J1/R+s8sm/Zxoy0v50FxutXmF'
    'LtCoM5PQUI7luixk2GqTNtD2tfMTrErjeXpNX1pbae2FMxwkPMOlx64Ob8B7RPj7CogjrtTDzfeqRByJpr29vf3NkqFnc+ocEgdh'
    'GzcHv+lytXZ3b+pBsSvgwoCEwHR7Op3uu/Ncm3h8F3vekZkcieVQ1sX3wJrKXTwFurrwismoUMkqm2UPifyApr2u2i4YFF4Chcfm'
    'OVBfGyBqjSITCDrVQQPHmk/Ab+/u7l5vNvpBKrJwb5tRe2gOHACCBybLoqP+REjEbJiFED5D+IcjswkPnrAZ7+hMLgwgvWZNk3lC'
    'a2LWxDao8yz/77X+uP54q/W3Z5HA7jYkUH9yTVxtv8ys0lXrzFN+mLXM8vi07IC/S+9MzH0a4W4R3GIs3V7PYE88aWA6VHDUDreT'
    '3mw227V6c5om6OH5Jtuh8pXgD/O6VKn7zHqsaXJnZ+dzsyDPPMIlOsmjhL13bVozELCB1HDZB0rWZOcoCE1LIeVs7WeLa7yU+FjH'
    'U9lgZHpnqtBzSXlVWVuYFKxleW8oW1KmUtqZcYm8Sm9Oj3INVchZNUmyb8kWQ5LjWRtkfdqzhruB+uBKTI1mOBxWVFSTGHlQKozx'
    'HXA2JPbAheX+Ux1olS0WtwLi+v4dhQHfIJzlteoIuwb293jN9n4yNJ6eccZTIduR8b7IgzthIPWL0UQ9f/ns2V/xsuPhYfTn14fH'
    'hy++jx4eHR0eHT98cRy9evji4NkvwddMnFq23KQJYe6ajEg6Hrn69qHht6G+71n/omsYUCj3a3mbbQuXB32pWrBjlLveaEe9XtAW'
    'vUorABoWqR4ZjQzbboXUrtAd+dw+XqYLYSO6yObzC/7CB/gd11LwAHvvk4vTPAZdnAF0yS9wtSuwnsk/FPv4a7OPsfiKaTxPmr3u'
    '/T3QE0dlZpTsmyXF+hVPDeQQPvtLZXxyX+O5vT9xg1alwwHV49D7Nhfnr9bzIomG4DX8NF2qcJwu1jnYZdT7TRu2q0uFvCvg3eqT'
    'yexXTkeU60DX871/gAjoQxxdfzxvueEJdWumj0H6qslz5uadbHxjS8JakDT+D7kl3uiJzZu+sHvAmo6LrdrEE2RPzUsRpEYtrVfX'
    'dc8zbhd0Wd/n2l69iKF9SjGDsgVrtliJmDRaeLf8QxrOB81QbaHXGxibk6AwwtW6uXigF/AIoUBywSt/uX6cpemuJyx5yXmQ/1R9'
    'uCvfqgs1JxuxeBRKPPUNPaWvOgrhVPf8YLD7ukHlq8IzKxmpg6AGqwrPU3+Vb7CQcTqC74H8yw2yZ90zhvhF7DlekW40qSI8jkgU'
    '9rxIFlqfnSXw4NcuNGGicsvAbloU67oeXi2rGJeYcQC0WYvysEs9KO8FjIZ2Njj89Sim0gltRQQqhgR+dRHP6UlBYpgl0ywXyw2b'
    'Ls8Zps7O9yt9ke7p2WHSm1v9WZ4kyxblztKr0zzJDkyyx/nrgEFU0J7B2uwsWwau2iGCMY+sfoNdz3u/esaZLEshbzNzq1BbiIfR'
    'NTzkgT6Y6x6onu3Yq+ALAdNtlvvCgiZSItjktmRa86G7FI1oMg3ReoWTSEQJX9NpVs9gpLe3jcXIhhcqnpemLT1xVIZQCOGjKoIp'
    'idjPcC945SG7pv0JeG7baC8y2mAv8iQtFmxN2+HaWG9mIj3odJCbFOPqFqfDHdf0atcSTfBrsygY1eAqA8oxcdAN8Y1fKxk2DCFX'
    'BoUb7cCcWeSZ0jm2xm3bZTwVIC5tWFPkO9nWudcQow0P20ggs85Ftu4skhjMF9NVYRKJkUfrM80g71qRae4HO+b2YtaI70rqWqrV'
    '4jlDynW8kFCq9Zf3iVNP2DcNfRYiPVEFB76FERrpPY+PSr2tOj395Wjmjo4fHr/5xURo4ZbTgSAtvaSX9PtVNxHXiNBi8jYyjLnv'
    'CVPf3wVtaX2xr9InD381g2MXjr22815uVYARxOS+Y207u8TCxeOszw/VVuPU3C3iDxjnxC8iJWq3xHoZLsOE0OVZ0volKcqfPHx2'
    '9Esw11xks3iOcTzAeSGtD3fsET3uLC8Fd1uB5+ha0JGeNypAqsJJ15JdDEfYxoZjDdSLo2bEleaQW53Xt/SG2/djkA7csMOjQe0Y'
    'c3p40fmAeIW9s6VbyBZ5YNgLPTDqqFCuRkdWjvpqEFZeUS+ZSGWVmkRx7+vZ934G58XuVO0GeXqdO0pvKoaWlHVf6WCJ58gbHgCH'
    'HoC5aHLvi8PqLV5oUi4Lf2HQgVbBjsDQ85oSrh0cjz/zeY6UIf0oNuN5kUX46jgFl6krJg44D9dBVUu/3LiBZ+rwsdlSQGt3ENvP'
    '8uDmEbN2K47ndaKSCtRpibrS2zTpn7raA7VuY/v411WkGHjE47RFh8yezYyQ2Tc3zh3UM8512NkGG9xdc2G8XHHP0ZxncqLPVqWh'
    'j6/yfllN7z4v27OYD1Cp0O+7rERbOENnSOO2sKDKS5u8YM+qjgqPPAhEHCLI0ozStmN3VGhovVMtPU94/wbF4qJIC1Cvdk4TJs3m'
    'SSEvanydx05RWbDLsBRP5igFm+GydkK2JIK2z9CPxce0nJ4HYugq9KdL3BoFcUkLBDti2p681nNvpZympP2UqexR0TsiHSLbLgv3'
    '8XnA1kcJils5UuMdrtQoWH5XlH2U1SX9BtYKu0H2s+ImUT1IFuq+oavDQ7ZLH7A2urQm8D+enifT94xk7vgopg5seFm5dWUGcmiz'
    'K5AfZMWI/w+xiCJerUbbLFFV6Dbr2neFQpJtjj62s5Gy9KbqD94IpE1sWWIuyMtkcuK0h2mnncptuqIZuY+8gMf6gA1zJzECxVGG'
    'ktvtJoPAdnItsdjm/fy6zLqu3o94VBTJJl3LcfJw4I63UvI11xGUk/qYz7Hfui4NqswMeihsCosHyjqDOIU5vUa0uxtqyFoA5tFH'
    'H+36iGx78+Q6vYtFdAzaPh7FIVKYcAeZLkirosozJZ8Jbvpi1Mc2qbwMMjdzpdYy2wsszptyuF2Lww0/H4dzkBDWuruGaEbxWcLk'
    '5YTAoX3D9a/dFT43zvSgKxk2v0yquF96yAgSfHZCbdIi1UhS4edD6jjbyjTpJ4PB/vU0UXscORX6Ja1N26EtRk2JfDAQwr96hTvU'
    'kZT9EMLm9q1N4ihMePo6FVQDrpKmyl7TOcP3pPHeJnWGHYKIZkg1w/WQjy6dfrLmltc7lG6wAaMPqnbrnXN4yn7pv7+yLE3cV0+O'
    'wxpeodg0PaTf5FkPvWd5i5Va0SS26HtJcwQq7rD47nLj/sBdhhUrJBymVyxzuBNh54i4KH2Xt4bn/ViAdjhoaN1bLyly150qYcnt'
    'XeM7cv9fTSexLvvfHbQHvXvt/mgAXokHrXq+ZqWmpxcP8Mmdr1ULOretsR/6jwaH2rAn5GaBPswPqVAMQ/PBvGJ9e72exZ/0VHXB'
    '0RHBmEzzBBrxvdCGoLi/sj7lRGKYlMbTJwyovlF8Z8QPd/UM4Z0wDNHR44MXB9GLh3+KHj188v3BUeSECOgWSzJO0VnOmKPrugsS'
    '2bJmY2U96/CXBQU3NIWdhG0dzV476p/mLa4W8K9yizLOS69eXlNH3pV6+Tnbz/iNLpFp0eieEMhx93Ah9SZmechwVLH5Ip7rC99l'
    'xwhhgOPnnWV98Zzb9q7lqkEOzGwTORu4CHs7y+OzM1BLgfc6cMvXMjpld6gf3Y3kmzEGAieFfs1XEPBmGs0LdW8NQxjCFZc7arPR'
    'wTYaR9NDgzRK1JpBVuNyvahtrRyOp2NqHnfdB6jIjPfDRgK14h8xoSGenRGR3fbqWVb33KN0hafj4SbnWtcZiW/j6o6tA7IH2llv'
    'tvHRD4Un9yezndr2Tk6LcDqmW7y32+7f22n3BwO3xdE0Pr0XB1u0Cvotwj70qWy7veBil9eLfn+vvXevPcAIAH3P2dWETc+ss1rn'
    'bHcIn0itSsweFcmqjtXy/aDKGNZPvAiFGwyIa+JNCft3bze03oPMFGvRedN5uqrksoY/I85x4uXFx/MkT0gr1sGOSZRcrbCZN+xW'
    '8wYXcxViSnCrcLdd/hjz8csXfzp4ffTw+PDlC3vjte5Wn4GXVBn2yXKruJh2yEjrA+5vwO15zQcKG+Ks13znLWUq1sdVnp2mOuK3'
    'sovAW6o9EbFgf6tAtTf2gtA3nzeyPsYf4hJeRzEiC1zT2JA2wnety4bdQcBKy5PF+XujzhkAsd41+8OdWXLWtt4I9H7Thvem9+Ld'
    'XTSFaH3+8MkD3wvIfWNR3FYOtPwo3EPiSSq4/uNPVrUzLDObiippBCpngro/M114sPYen6ht0xPZkeGAzJWvcs2XlIxe8YEk2+L4'
    'gYHx/A74rFKvwkTnzHeVshDvnHhZiTqkWt0cbcIXNhgBEXEfaVTNu1TZvsTAaETjh1ctkW0aIAZN5VUEFuOoOnSt5YfW9duw7oq4'
    'PRrNRub2HHj116qMvOGQkGHKOFkX1dYM3F5mKjZGz9jKXiV7oatsWUue+Q9mwy9h3a2lO6I3qw36IGPIpXd90Kt6bKj8I2erdGqa'
    'x0OVJSQWpmu2qkeo2gRB4oKXJ40EKtT9NE42uY610BW8Z5Gd6sBIybNQxQ5yz5LH7Wc95HVa1WPlfsWlDmkrxPXXzsicA4HS2Hs6'
    '/Hp2T57PctsiT9p7xgz3MeveNLFfQNvovckDaG+q8HMafBhPCrtkDfJ+TVK0I1AO5RNpLWl1TrOstPXRBq3XMWpX3SlOgxGGPw/d'
    '3dtMd8GFV0F1n4e6tqYljq4bPqTXYvXjc3AOC7EGXJl6ynKooJh1pU7rNET0c3JmBUX9Pb84sJu3vFQ4lLZ3Q2m5QioeEMunhrG0'
    'nCJxC0GJyLYd03D0GUVkJR//DKJxf7RZNA448DAQwkTHzPwmhItRTZ2VwT8ClRfrSbTdpu9Xd9uojodC0F6kpITmTroyBiBu6IP2'
    'AaqSWW4wwyA7uKHB0qYHmVtdTxPhKvoEVd+rdSGtTX+30o2apMYxeFN7o+dJUcRniZL7wGMMZ0kLmeNwxQopEEOD4v/6foDcGm7i'
    'tIemgAOTbePnOqOMgJTUE1CGxEVx1sG06/izMz1U7/xG07aqtAv+xWBt8kktkvmpaW5Pe/MjqsFJoarB+xOqIpEhHsHwujYb/1Iv'
    'AQKDsisl/Bd28oTRSZE4nRB6l2LhaLD2rLCSe6Fnb9RWdRP2T3BgYtmHZoQYVJ29zNzK1E7mvnWlSWlTixWW+lfCTh3Cz+JNp9i1'
    'mUh9muZFGYn1DuFb+ZLwV4kzbjbNPHLNPC5KkLPns5bfxfaGsdSrhQ2UcNKviWuynkx8nSO3vqOEj76+iDEe9FBa5l1rpXP5FaMI'
    'cg21G0TQ0i094r2yvLd7uiQBxK+AtT+ufX3e5T7Quvd3WnDvqz14eSD91pW93txps9B0MxvS0GMz25slSAVuPJWrGnSFNMmpwer4'
    'puqp4SuOtWH09nbJV6LdHGq//OHIFpMyrq/pMN4ujzZxWl4xcUtpRLgCZWm6nKXTGEIvi6GqNVwiwGecf+qkshtcaJuJIiKFxp2Q'
    'UampdLCGxg2yrIgT5t5yz30DsMlzGKEwBnVpv2s63qvszXhZnnNKbg5asI3LyjoYhGQc6UcFm8oP6fKjYp9QUfNn5b3ftHdd139w'
    'c+Zxlz3gLkPTQaDPXrqKwYBvjbhkHUyYtIUUp0htBuYgeFkZCu1b+7AS8lKj4oDsSg9EV07j8pVE20kVIdzs2GqhtyXcwwcyfE5K'
    'DAvTJmjlOxg8ouVEZaFpyzibh3qJNnyn4oUO3WOpee/pRX9Usr0HIsiL84aeAvF9ueGxkf1mJllUrAwmzJWMtczlTOIM8eW87yyP'
    'CTrAAv96RZmsQKA0POxZh8W+5Hs24U6EB61NHiuvXB3PIT6OIJU8+I7A1PJo1jVylSybfVRsd9V6ZfVhazlcP+Izj2fmy2l1NqOV'
    'T9czKB4Mrv0qZMNjaS6VUT7d7bciIW9g2m2tcP5uBvoZ8VfYZFik4ENs/hzQO3RaDj5d3Nd9lOIXpN11B9Q0BSMEQ1WifAqYS3c0'
    '2ObAtGH3c8OLoBhEPnS++cnLjmJKKaBhXmppiwWatNc8fVskNy/w8OZdpPZ36RtafwbG1JNQfBFqtCVwJ9A1S07j9bzUdX3I0mny'
    'c0/nDd/0hXzP/beab4XI6yvAnIqMF4Ke78TRCPwm7oza3KrLbur26Wg0HBqhB+Q3aWbgumvWGwMY8xd1HZHtuk+zjafeoB0ET//G'
    'NWfYP9gopMis8lP3MzwjrbiACquHaxtkmii5LsVUParCyLJKHMGohIy9R39fp9P3ESx3/hAhA2fDEVxcs63uNMmTJQSzl+57YJvA'
    'EuIxlhehwTPnPn75+q+PXj58/cQ15L5dsLYuJlmczyyhp+qhNx1P0LCoBlJBy5o90ku+IXBUxHV0BqXfJKmN1ul6ICpiPXPqiqMj'
    'w2Qx4QEK4zlrZ3YRnceFPFnwAIN8uPDcAxoRFYDAnSdwb5JPmcCaljLq8SxlPRfoDtqUdY3hMcSv5Qo1dEw7A8PxwhhPGrw3my/n'
    'tn/7S3gwGoaC8mjHZ84QwFmRxWP2appdtkJeNahWVtG1XRENtIqFTTq4fJBqfxew546dm0KYRYMmLT/Xqy/KooV8Pyc6yC156Ge6'
    '2qOEuafI0saWYXv0pVQ7u6a79g1ni61u77nh8UavIrW9Vw6KLbYKgQWxS2xwtxT2wSSqqfY7IEvc5G3akVom/JkOxnwZRYA5edMl'
    '+Zyv9qM9YOy6b0lDcVB3VBxUbXEpM0ctKjLVYM9kbQaXhY3mjAliqE5HnQdM38f4olDBftmo4AVPHqdwSdTvLRYgPyfRAx4hlody'
    'NSK52hFniWiwG+Kl3zRe63Q9SaedSfJTmuRNiJANWAGr/hH8ui8R9DGdz+F4uDxLzMNqylaTkB75z8QkUUAWXpvIjw4ntFYgspOE'
    'gv/lnjTAZPbp+wsxomxlBqpRG/Sgt3+9GCqu03o17doxl3WtvhcWLj6Dx75dyhdfj4vBXizfwZ4R5h1ZOsrKYaVH6DRFzIHwWe3f'
    'g9pOTPc89bhQ5dVAf6XVy7Wwt7NxboJmF1UezYnDYRBjnDHzK0N5Im/dhE37LdC+n4Y7gYP97xZM9IsjDK8m5tNdb/aa9F5gmzza'
    '2dk9WLPb3Xm8nBXTeOUE2ZbRrk2ep6JoW+O2Yvzc1MWFGaNzEIdecdeWc/qjcJRjcwzXDvG0wXmA62KYOxmWUrjb2WBIKDOS6x7+'
    '480COy+lTG4Tk3FNX4V90lfhnuMc9HYP//Gew9JO8/QNTii+izUO53nmVt3vfdbuKx/Osn8oG13aT5pNsyMLsMtaKzoD+abWf+Sc'
    'J6skLpsD/r55n9iW1cps+bUSz6fz7KOudth2HlC3iID2vUHPX88b20a5NF4ZUTHk5YHXwr2ej0FezXAjYoYuYvB2Rz3mETuPuTIw'
    'rCMVmctzNrKNWZn11uQU/9kPhr0IPFBSYTSssRhaJFdO1iplJUcMDIH9YJaWkXTTDNI6H1c0uZDbSjsC66kYdiAwz0HU8eaUPI+J'
    'HVA5CLP4kH5Hy3Q7PJC6DNppC7iGQwOM29mOMHqnCr+3t9OynRpbFlsjUmbjz1l7bfhvxLBwz3PvahAAV7TC41/xh6F9LyCEyN7f'
    '2PKXFEYMTxvX8kbR36PcUehUywGiitCi5OzdKuccQ3XpTATrIMii+HDmSJg9y9Ku5zhFrjRwdkg/TIaGywwSg86N3Gb667cqBilX'
    'Yo24R3sORZmBZyzAndZ2/ev2W86WZHdWb4xBO4Nd7bKScqNS7eSABwjeLMTp05yl74iXH+JCvIYN2lxQvDQYTyEuVowXdzBkFeyw'
    'd+8HGuzKI32byFMbGZUJZ38mOCXoTopoj2rtLbzQe9Dgcn7jHdy+uvoj50p6cyX8IrijYqV6p0vUsBvvQaUXBB8h5fl6MVnG6Zzq'
    'mA1rBFFEk0QtF8CXqx2UlU3zrGDdSkFPlq2n58KMnzK3V9ulTcllls31C3RKwziy7pd2ZPh2u+4d+DdkcXE7gcghPUJPWWUKxroI'
    'nQv4Gbc0XX4ke0rykCzTCskx2A3Yq213HVr5TGtY4TK8qGLPcvwh5eXt+/fvuzPRg3/3vSpCikvtwqM6qNHAVIRC0U7xMUavyBu2'
    'Izreifc8WMxnwAP7/yHvXZfbOLL8we96igozui38DdBVBRQIiuuJkWW6rWlZ0opU9/R2+EMBKJBo4TYoQDRboYj+tJ83NmZfYB9t'
    'nmTz5P1yMisLoOTLWrJNAlV5PXnyXH/HTpaG7Wb10O3QHa8BzxD59BmEQgyywjNtfTntweUaT5Av17vt+p2AZYzwNGh6qqHOSGHf'
    'qq9gJvWFjyFyjg5ChdO9H+zGsuGa7BAgI7InRSKGxDT3G6hp61subXF0rNuToih8CB9qI0g7PRVY62L9icbKskThSmNwVkOuXfbf'
    'F8+vrl24rnGPOcgw0K7IhKLExV5OlKW+0VzXMqVUFj346Iy/OdXT6ytyG1Pn7RCHi9uezOGz06BULoIFdlMtFvNNPa8v0OoOWBdT'
    'WYo3VIMQAX9yqxDq89NzoiIraz98XqVV6/UiBMt/HPQWQlLYOrtlB52H/HC6eXbWPS/gL0ObEixgeg5yjUy2Ucf1xfM//XANtaYu'
    '7TP8ZLte7/4+LXclkf6qJZErF7DdIJuy3MjemJxM9Y+4sPmX/GTwJ06qAfkzsr7M2bcn0xH5M7G+7PMvJyPyR34pKIr9Yzr9OuZD'
    'vHXroaF8CohMTeAkG5E/E/3LnmiB3AmT/mQwML7syy/PJmeTkZzbdj4er1dicU6mk+mkUqvCk/fZt+wekwhm/hXnxdY9QS3hd0/Y'
    'gJxCJmxcDS+fbsdaxi1fouZ3/AQq9oGHJYXbYSu5K/UxFJNiMpy0eLeB4Ta1U4kSBVI8YKTQ9KIsLGQte0r+DNACs5rz+qLtkju1'
    'ePQ+JwPyZ9RIJ1rFRGvM7Hgi1e3t89dykU7I9mD9DcifkZ2b4+uyaWUo9ZjrwTiKQ1KhPYnqCI/UPKlG5M+k7Z66kXKHnX9Ra87S'
    'rgbkzyjyXRpF1ZIiraJ/fk4wKJpZWDnvbcpVtfCtbMNYRLHgw3igDzgdH0qIiPLmmUocPat1dlEY0HiHEqq4g3gFKO6ljGDZRUTb'
    'YyKPvvdLzWaDw6gGOa7Dp2YUM+Gv7TY8JYF3DiFF8j43qSFnWt4OjWcLInKX9Q3LxPSw6+hGZJGpxgINNFEhql09FQg/dO1vQB5W'
    'Rl3SCQtq5TlV//rvhPYPtWl4bil+vMxQWO8GemiROcMbOVHD22i8m2G31sMVshIzHaFRb2R3uiIWAGwSLvfhgmZwgGDE0Nk9HYMT'
    '7IE3wQri/XqnyMb3fl7dtd6/E748/1wTFkN4Udf/4Fg+5PX95GmX/Qvux/PC7/yxppbYElZouvaQeRRR3MiNKDCMSbUesVKw2o6Y'
    'V09oMe4mQfgzlIhOnr168eLpt6/ecFzdB6+szObwmnIj4IDkWl/RVNik3m33E6gWmJSrabJYr98BKr+ULVhWANmWRTkW3Ey37jDR'
    'kn9/1wn40jTcF9JntZvcutEa/twAqQub5C9TcFuVYg8lW+CRGrqhh84cquiNnOjYAQuU6GYYWBqs+3K+3a63tVxfEfZV/UzUgcU9'
    'stweVDWBocd+8IZttcj//SSBZ407+dE339s+kvWVtiwdLS24rnl8FB0YZg6Phrex/Od2lmotJNRscbJY19gdaJauMvJZ/cDpKhzZ'
    'cc6pGHZRhggzw5r5yhH2b2QyR+IdnvIWaZErvQQBotMu9pWNdtIYb2ClzpPVKDxlYCIjAIOlGEwHr1itBdH9NchigcltQHJ7/YjO'
    'MtxAAIEnrV9L4GTZm7mN+cG41Pc0RCehgO0apxIXgagBLEpG7e4FMotJACzSJ9qzPjRi5Y/kXhH3Rsj3Ptno4Ka4uzLoAjMqvZ17'
    'AE71CnBtMo6aPSCtUolC1br5QigHfKuC3NKXxZtp8mI1RDENYjxdet3RBVFQTcpklTjp5w3hor4E0gCen/VVLKafYnPVcrO7dwoN'
    'DCToVxP2TGaFv9lg1CYAxZl4GQ7wk2S+Iy1PdD4Ai5hMIBMLYQOyFLh2/g12TV+05nIuq4e2OeDecssQPWKnMFhLKocSdxOhr55u'
    'KzK2907xbPH4Sivz10oIwBCwVZsYDm1sgMlDIwtGhu81M0arKIOa7H53a4cjNORlmCAuwpEtW6QFVKwU2/MQkiyKuw0t0cX4eee7'
    'DUKSmH20EnTLj3S+u2pQ7k2XNqtR6clJdM3cgr1Zm3K9ajuDtXULG+1haBA+evOeWyWkYIpnCPk7KPKB1PEHuFObKR4NetMXPQoW'
    'vB+Cl+etnP5jv9yw+hpmoSYmGmP3K16hSrTH+Z7dHpcxsfbw+lP6+IQo0VxpK/MMx+8iMHrPNHHgBVgnN/MVyLvkrq6S2jAHs8uL'
    '8vsNlEu5W7lyq56meADvjA+B8Qj2bBOR4PamYmzeMG2OwNZjyFgqpwKvCknjww89BOHc4rrrXOuIZRfOcd+23fZVJL25fVhUoz0b'
    'GeaY+wVLGT2lzNynt2Xd02QEFVNKgSDdo2eZwTXhqlxN4NbbrDcCoJbWiu+xz3vs8w8Y0IhTglWGwvfTh8DViKrJ7MuVP3PwNCWu'
    'WXM9ZraZ5UasraEgpvHVjo12NDReG3TVCL2E51FRJI0tvJaHCi1D8ztW9i/mlu0gdQt5dOVpTSRwwmBiDVCyCKadxH7g8iJRbHbU'
    'rPzgZXXXtrSyliCjzTN2F8k7NEPFB6ai0aGDm5ypYNmtMDlFSL6NRqR+s5XRVzYTr3641etWfmjIFMrDWeNbvSJlTAVMTL5whvVz'
    'o2c4D6GZ1VsnSlV8zoojRovinvXjCeqRrWhUM0jjqqx+JpfRd2+efn8NjqNXb99cfZK+uIQ03Zbigjuk9s8ovvaPgcWjtBlTSm+F'
    '5UYxiQJYOo2V3gVDshYhCL8WhBdHmzNKvD84xI7sTySvtLAr9NGinHjRVyMkQ+uWYeKU26bkwfRCAQgroGBZfkcBsCjs1D6uSPuz'
    'XW18WMgRgCswodf6alfOKZLMdj4xam982qP85vIvz6/A8Xv95umzPz9/+afkwQ6vJsEyf/i2ev/NF+Q0ythsw4TQV3kzrOawg1EQ'
    'Vr/SAk8hRUfB4IKaBqJTc/NojPuv1WimFcTsxY1mC2gtEWNRAfbp0H2B8phpNVlvuX+Gin27W9LGza2dxn06lOMnw+0RkYjoWPW7'
    'wJmSml7aVtPD2Ei4yAjDRvacOhg0RKXDwOc1hBHS0CszysmLNRh4k4cfYW/6rccFKJ5qc0W+BnXOEVbcM7oK4anqlJblpr6HLKET'
    'FkX30ZOJ6lH3hNRbpCrP2run/6nv6ZFop4hO6CjrvFn6W2857VhePiZlKSu4As1MU79vLtIqGaAyY5VtsUXugxJsnESyCww/6ljI'
    'wL43Dayx9mFcKlFD0hqfs5RjvJIKf/CUrIprY4y1CQ7s1hjrP8IjaLQGuVDO2IBHX/hQEhRjdoe2qMoQovnnEAh+eE5TJ5O/PL/8'
    '6+Wb5JOI9bfzmsWnhqCnIm2eIcipkapeFDoMrS0QzZ4KW2yV6og4BHIJWpSHU0ViHtYY4rhpH7KEXJJA8HePaRms7oW5COwmtVzQ'
    'EvQAUQkECmKmsMQMJ9VmW/VYjigtM0URMe06U2b3p7eLHmMyzUZ+qWAYb2+r5dp3V6sDTzMrwqJXqJqB0WNdcm9jIKOXvqClNpsH'
    'A8Unfzg/ua8QnBxUCwe5fAcXilrpo7KtlkYd3X2oDKy0NR5GYRZyxKMnmqPoFFav6czldlgqZ+zuN9Xddg4SryXPqihZdlAJZ7wt'
    '38+hz3q5Xu9uDXnF1w4lMgrLUk39iDYirgxEV9US36Iu+5xhu2jyLP9ct0Jw5BcTqDy4v44+0yD0fi51+lP/pXNNvn/17O0VTYZm'
    'v/+mp6RCxHlW9+WiWoISR+6bcpfMiHwAmBXgR2UFYyihGlj9LIm2K/I0u1qOKPl5RmR9wp9pzRh2QLoUJX8sRPOumzRhxOp3WWpd'
    'Xb4H9J5SRnLhGfj9QuCUKWOR9rFx/NThkJPAvuLTwr5SE0W/VXNEv3ZTRbAmgt+bK4M+4m6ADXPWCBSn291Sf7A8urAqVVEVGUcf'
    'NDMNGhBnnbfJo2uaRaYBSb2/dcqof0tW4Z1+WeqU7DQayAOzQDztfnj6GZ0MRd1mF1E17Sa36+38n2BvhJqRcC8RdSU4DON28XPp'
    'EwxX1JDpnW/xbAjnMUQTcJ5xFANVyNd5VkHzi2ocRE2A/9oP2sK484COGuZa5VBkdMQsGFxwBknqQSdvpEskn0/zgQ9VJRId3cix'
    'r6iTiMX5SVhy457l3JyQ133C3JoQ1Emz8inNdSlvrxNWn69fmzydTUGPwDcNVJZMwoxUCqtz2NpKJW1C54Dx5bGqpl2aDeciIToO'
    'CcNq0A9YN3GtsgX8b7BeRnqKY8RnA48fLDdK07gAmiMJoIlff0N1zSXNVlnjmtB3HCnPYZLVz/OdyP0DstIKo2J0VJHHMQdiAynJ'
    'eIpcUVOeO8j+kRSTt4Ld94cEHkgspkX0+P1HvaFh2zcrFsh/UTQzqB2Pw0CVMzJ30B+LN0i78FdkqqJmRRuzyEOEilya6PDPFS8d'
    'AtWxdEo0eRxIBj6yvFWo98fQZRCS2GuP9xJpPPkdxlyCZ8DPkgPe1YPYlQKmDpEC2yK0ZJDz2LvxtKk8dP/QeDirDKgI/GmfLuTe'
    '0/8HEfJlApZerbtLpr2sk7vbapXMp4sKo2Mrj/wwMuY+w8/FXw/me0amlfRGmYiA3sTVOFbtMEIf+WqpkOZOSDYZyfHUDqJuKv0h'
    'u/YmKw0mIzkcczuSSxpIGbIrmfgASl202aOzTfQlljdV7sQKa54sc1mCDi2Xcg2odolYou8Hr5PWJglEixnrD/zpoI0h1X5AUoTe'
    '6Dgb3HkGs/meGnKuwTSxZuUB6eGnmV5dWSrbo53ynnf87QOUA5Wz3vbq1FnSCFdht+u7mKJOOX5zpv46AAMoApCNwpzOQ1qHcDy4'
    'xTsOP8rD/ChvsHJZe4cxG/MZLyM7ne3GUODdQvw0sh1GNi/CiiSkHbu4FhZNq3swoOcDohELFC/Wm6ubY6TgONdcEnAe8UPQtq4v'
    '46shqDu4jdUtxOp608j8GkOuawy5Cp3RPtOCmYxqk5waRP6svmsBUFLz2JwpHQL5eiQYtmjXbxfDiC5QRsF8cICk4Ogzonn8slKf'
    'Tv1nkamaqq3de+pQxMrfwdcbhpCHfA3HnIWzAfMsd998sXv/xU+Jw6vRXtTJd5uBJwA5B2nGHo1o5tEjy+C6v0mKJ8kVtwJvK8Ar'
    'rJJdOa7pzSPKDqxZnlYF5gcq7DI78LwW5WUM4GgGOMAbY9CfkQVkGkPgBCcbNBeIQQvHHST+UqZH/00DTOP4ejExWuU5U2pNQ1Yv'
    '8xZUbGFzEPg5smoMuCwhOxVupyeaZby3GzvFbFoXsrEuQ5doDsjCFK5sQSUj6Yl2Wj+VFTWMyxMtJiMQl1+AAU07I8njl+X7+Q0g'
    't3dEZWyeju8Sv4igdoNYvUHQFt3xUbyh0qAxjGfUOcNgFjomxII7kK0J6aSBUQaGUrBY7ETWPfss4VZXP7x6c/3sLcW2fvri04Rb'
    '1bMeB1dFBWNVwdyPgTksbAl4lIK9+WiOgMueQvT8qA+/p8T940JKveKWP6Z0cdNpVTdNd1ieUz+gz1+ppvdpY+FocVaeZ/EpguH6'
    '7aATsPorYiEeFpWqiEOlGnpS+xFUKmS0x8BOmSROEdRjogHZXpqvC8xXjIRwB2m1mprRiYkVb2ik5lgFTqwE2CBdNW06jn6Ut0Q/'
    'Cvo24uqtH1CaFw+ebijdoU38sModlHiMdnqb7Zyosff+8LiOUWR2kDoAt4HMC3qePT3iQJZVOh4Nigt3wr0pxGBr1qKTWToqR+VF'
    'Y8h00fE3F1dvAlQqTZ0qadkZq0aTqkPBwXyJZLib7HcM4AlqjQphaMKxnWIvBoVDxvOBDsHzQ5Kpz3wZA01GVJ/poIl86cDjBFh/'
    'omLHWAb4H5Rb2hMmcdOY90JNpiHi1VoWplTFWONSMI023lX3TdhyeBqJh/NNtBaP8xVZyOLCMO9hgwMc1iYGHSAy/8PAXQhZoV3A'
    'jRQR1rTlImr/vo6P2dW3D2Kp4t+MKLWT1xfIWbC6M82WjJtIpzFR0PZkVf4pCtOesEmyYgp6NUl5Iw/5jWxZb32ko29/8O72xPZ8'
    'tAbVks8V3jMht3TM+J8ftUl7MuK45A9/XArEueSbdTxgrV3HUEOTS3wV0hBfj0xGHlpl2oYW/klfXRkNKYtanrqRuaHFgEXXkhLb'
    'RhFsanGJRgR4N2di9YtwUFVoAPxzhhnmSp1nzpqLK0VzhIz8OEcGDAuSVu7jhseWRNO2v6+XHjcmi5p349YJDYDQ3oWCsr2sIA9q'
    'hFfk7ilmT+bmg8Oh90GrydHA92TffDBLvZ2fmU/mgxR5kgiY89m8UTIXXJLJLhUa0RMQ6QzQIsbdlQoTllMwcAZEUhoGbwIUvEVj'
    '/mJaAqtPYaN8Fnj6F6/efpdc/e3lswc2kQkE0ZpozQt6HaAaaGYw1mBi7gEogOiF/SD6pTGvIxRMu6njMrBi82tPSJ8st4GO5LS+'
    'X00oRAmaA4y9UQF4LJ6YywGtJrfltm3hz1YmN6McqPLnhrOsfYCheafZX4qb2BVJiAkfaa2S7Ui4JNsr7KsJe+wNZ4GuynFQwK66'
    'XahM4zFsRNjiIHN6xdohglmDYH+woUMJqluyaKwm0IcIVJE8RbA/fFCAPtwST2X1TIDqmT2OOib9TOflYn2zB2BKlvDiD7aRvoJh'
    'JiIF+HVLbt7HfYjR7yaTcjF5DLkyd0mPRo91Om7ODzxfWM/fkuf5qWZFFG875JNiqFp4kPIbn8bfetaIYiE9Dger4aFt+zub4k8e'
    'edB8RWJNs+MHxGJnpqecwwnIxjjExKDVAxkILYBh6fC563co0gcqL2z2PiEDBQHISQRuY4wwm+S2QzUqtq7wu5O+yyGiLoyIMbTV'
    'iubcWJcaF9mNIuZ6PrjSm9OAcBMNYNy5QMJy0JsPuNAtIdidh2DpbFRpJfRbFh+i/N1BwsIqoJuN0uvEs4AW1GbfK5MHIRyBRpnP'
    '3MReyIuLEF7j8bjd2KlSUONysmSg43eQBLFGb20P6IUtNjtYoqy8sGq7t97OqRglYj4v5Lf03cmiXIJt1Ucadt49tY/57Ll9bIhY'
    'jv7nUWy+f/7yu+SPyZvL1y+ePrv8JJ5/f+qtPziW3q/2vfoVNTCR/6kw+K0W761f7f1R+mlDlXQIx6a7U0kgaZq2isD3eOtPZtvN'
    'p3bUCwMA/2nY1tAb4bqXU4m8UX2efI+YL5v/RepLtfTkq4EepSXTZrj73gy6YExp2MKMrJx8PPqSNI2ayRtchOpt6f9qhi/qq+gy'
    'hvVmx4siMLSyH1pKlbsuUEuz1OBiZoI1S9cZ+JpaZxHaVQxN4gN5zUghDkAVjjCDW0CYww2wgXxXOe4u+5FzZRv+6eGTxoY+pG/n'
    'zLuYeZH+PkuiMmRMPAneWRUmwplrwz5rwKWVNLLe7Gp+SqyaIwr9Lxsap2Jy+67NmSri3KS4tc71pZjjEEWIywn0ic/VaVS2EC5/'
    'ojuHjEWhRxto90nCKBgHOaKszW8dbRGfQ5NcspCn7ddiP+VzPs5yyhv5LHE5bncRQTlUnFEmqAbzU9+F4zSJRDbVI6sNmmFjk2ee'
    'JiVLyVA03s8lpF89u3x5mbx8+pcHRDsXUbkrgaQfiF5ZCYR8P/49aab6GQGC47j2bJUIRYDcSYTZKnn7nOU28BgmfRkhHPk6efH8'
    '6jr59aJFgVdqgZc3z+CfgZr2dTmWpSLJOzv66w7kd3L6nZdlBXfzaTsIQ4VauRaO5goegZqwIc3fnyLUL5rEf1++qTcnC7mr7DgF'
    'TZYius3k3b0CUkcXVWhiufIsyhV2qvYNbS9b3JysiICTyWSCSDnC1CA2bkkUvEVllIbJUyn8PIzFRZvs9pT8rMKFdtOIVLR+58LX'
    'DPxPIvjjjRm1NFSisdXWuFyt+HhcZKesyqp80ITEnWGJO6ykSEOaoHYLOGDwo9HIU8TBP41T9r/epFxW25Kvi+snOSnG5+Npoe7e'
    'UTkeTAcXES1TuM/E2zLn0+QoT3ub/XazcMQE67uIHglHD/RI5lIOirGay1k1OT+rFC98RhOheB0GDrTFb6IFB2IURRrQQmSWATk3'
    'Mm3zUAGaqDRlVETznNVAtJqazIZwJaxCporWdKRfs4HJ7dzOLh4h6cUIRIcHVNVXWKShWJk7NRgZVm9MLy/mvuGv9EE5lxHtvEtW'
    'exBEFIXU5ENe5CgWKqAhP+RMsyoRqRT+qDFcThXA03wFIddqKBBaqekjTdxz2LmII8Gs44+XlRwCuJFzyzv2p+h6yMbuion5A9nN'
    'eoUazJFkXXE1F9kiP2WBXWyZWanCqVrm3RRRK9UZcgKezdhOYGX1O6Sg1bmVguSyQzME8ImjCeqP3pBLWK4CylnN3TQgdDJRjZ7v'
    'lKlX08OzBCzSiFl4dseZAlLdSu2ivYktx8w29VseWlxpJ4ZFFGsFktHbHa++1wZiAvEUhc6AndAPKbou74tPutMCYrOhXt3PWAJP'
    'ASV3ZwYdb7p2Bn4QpO3efHmDLXFe5mU/v9DxIh8EsyaAHFCYJj5WeA6rV+TDdUZmRmfHb0Nm3uMTYr+sx/8ge9KbzXdPJtCTd4UY'
    'e7jRS1+IYThhtAMFDjXADp1MUTWdSo3ChkntGpNnt6Fl6jL5vHQz2IdQBAibWQNa0kBRB4nSWBjZWoYupO1skKIxsybjL2k3uDYv'
    '/V7WrmUpH5tOby2o1mh7WtUTs3HNQMq0Md0FQ4tLSoIU9CiOhOGBRpzC+QXmSFZ+ZGR89aaaBO4yJQ46ttChPmNoBjap+T5AEEUa'
    'OLsW/IehqTg8h2tt7AzdbOfTHmOGhMMkXye97CKK0w8tgyzTwQZKBxN04DopffV/fXHLHuXP3BJMqoBtkgU0uJw6ua2me6IumZdd'
    'Xe32G6auoLddmZV5it92VnBHlrdSYahu7c/zFiNr7T7WHHrIBnju82FL48mZBet5sy3HngwQdDrqAyQoVOcpQtLX2EQfY1qsMadG'
    'g85TkHkMOnYLoLjUFp/Enjk4EdO0W41Czg1zcX1nhLLKxgIbzkaISUQjHOFrpV8RgSuBCQF9J+A1tduc7lmhk0ht7SxaW8s7kemN'
    'Q9Nv59xKuopf2IZdK1FLy6AVbOhHiq0xm1cLTXni+fj0Q/vGseRX3es/0GlTb8N14Ls3N3UEWTZkf7FfbnOOOkn6SBg36DqfUwem'
    '+zGMh+HXf57t18PnJa8xTui57cbNUU+3iEq0vdthBUY/lu6qCS83una+L8UKCne4DznM0F2Kjm8kakMAYYeugJKadBVqmCLEuF8A'
    'FaKShnK61O/q5I/JM6Y8g10BMIMShkGjrun9GCwEzunwXf5GhmOf1Q7XTkNui5ofrX7oGv8d6tR8Q+SGyTsiNUL4s0/1D732hP5U'
    'TZOvIJILJHW7qBNW0+lkOBy6pgWWgCInhhZFD9/cw07cQogezXLzOu+wrBA2y+TSEdPFDJFYNE0Iar14Ty2MUhMCKT+8PIpwblh1'
    'l5oXr4ByikKyA+O4qGXAP4ee+c/HVhFri2ZeW/4Kr2H3Y9zQYy1+uekoCdsuIvs+JbrMTRXpOgp5USL645HVrnThv7YCpj1NQ1Px'
    'bp4RgFbNI/i5+2Bd7p6IMuot7Ho5qsUZlGdpcuJA6TJDNZ2XCWiltSYzwIdtrXTDX8BK18Yqp99Ccn6tTHDm67vb/XKsldk5dyCt'
    'pLHNnSfW1ME2LdYI13bE1hcunIYeRnhC0WZMF7LyIDvGEN2lbGSmyO73NS9hzPtPaXiCFal2HhT0dI/A9xSFjQejSb7LsNngsiR8'
    'TZ1721vKIdzwqD18b5FcDHZ+CZsQ3a43PP0cPQ505DrgJxPH97v5Akxuk0VZ11WdPK5vS0CSLifbdV1T7wuVR+oOf8/3lx9PDeur'
    '9/NDRTQrEA8rNPnACGc/jHnhwJhroqoxt2gUcyRhCxrT4s969dKP9cDCHJf7HZSkwrhsQ44Ab4B93UXJCwWIYK/BfLqCggNxs2ZI'
    'ih9LKSJ+HlUunB3jbkFtd8wFjRQU+rmxITe363qHb4dJuG1r0iAFupF1G0SlPrtYby1XScwyDpVKrQ5DD8OXh1eZSLtD+tcQwdz7'
    'VnsuH9nIzemI/PkVLZecdsBgpE9IkRRjGDxi+RPVOvGGrbtxeBGogR5l3pXy/Qq9NunoK67oWFEVLyDhc6kZjJhdBzUbBcs/uPzF'
    'HzwYCjn0ITIHLD/IN2xVoFCdpSl3ukELxO+ddtqkQgQtRt41935tW42C8eQmDhv8yVE0gKzwGAWjjUoiR0fGpEEY2m59c7OoEkE1'
    'FQ1FYd/VutnohMUzsbRp/XhEG+xHVixiIIO1773sDYCPVNfyzcE1lUQxcOr/Ov8nKH5XO5Dn0yfJC6LpAgxiWDp9wL+cCd3N/9lb'
    'sL5NT5UPtUpJpuCA7udx4HR565xFb8SfPuLF+mbtssx85M3Stj1+iidwPGoKTs3OxmM4GCP0YHBh0xkP0/A/tNOXeYkY3W6deltv'
    '7bIauji/MKfcK3W03qdAqkwUhA06z1ihDnuV6IA7CIFcaKGPYiZaKtbdYtKbTzBEuJxyLc7MB97i7j4CJe3awM7yC56B69xDg+gs'
    'XK16jQFLoHfPQjPw9C1cTbVy9wujuXKrnKW2PutTe60sUmNq/TRtiIK1Sjk0kYk+Sk9Zpz4N4fLn3oRaFmnTnrfNSszM8MDyVSa3'
    '2/WySh6Tg7mBYdTJV0QyK7erTvIQjJvVgPhcQPIPyOHzoxDlm24Htiww0mMsN564Fq+lZtAUDRCnvMWVojOneaQRRxHvNadTXi/n'
    'c8ki0QS/29CUCc8Va4TGUWDF9MKq1NhAvh+tjiLpx6L5QNi/qZEMfO7pcOEti9WGa/tFEhpaa8teDj+dKfRs7XGFHRgCBxQVdGMT'
    'X3GCpWI45XPJr4FII3EGVdF6Ia659bslqERcKV2b9Zx7rUut5DYkdNstvuRJZNEXRZAQEtXgxzhF075Dodp2zzoqhCPA2KKKnhSv'
    '1wGU01jN1q5sJ8jeI9+1qJcSku14L8tqV0bBH3oPktLx8ARUPK/PHtsAGdtDyp68yfWmWrVrMrSnOVqYUU9AjQATD2KlOdiauIGp'
    'MQjBhSlAjpK1SsFD1fqk2fz2BQivhDjqmuhNTNv9FYgFfDwfjmOQrv84zCE/mt0fGuibBzh+2zgVW6HWB9ZWo2bvMgW5mWna72FI'
    'Uy1rRpnMlbdb78fxuEY2J3dam9xW77eYBSAbhKzlfsUV3YBTejLRfvVbbLvekSvs8Xk6rW6aVVWt5cCZp7l1XRTbA9lsZrVAKizr'
    'WPMavlV8qYm48ivWRXAWtZbc1IKC1duP3Q6iHCxnD+RgMa2O/GCnIv8CHeF+ISFHmW1+5IL5aFUg7dcXc4VYql/SyPncxPtjnCx9'
    'u/oCUuhxyAIXDLPmyADGNk5nGg+2pC/du3E4ff3hnU1mvHnmxpsHkUACfoiYDGtFGLmZG8OvRFiSVXXXg2tMIMiSlj7znXxiDMNE'
    'PAtAL+t+I+VmodKNMJ8xm0eXfUoNaQbM5WGdYI6ZJ3T1AcPp2fVTkZj+ucQZEf4xkUL+AeZ+HPmX2f5zv9CKwFORP6bqaRg9JE5n'
    'Fg5jaLRHmMpjV3NSCvWSB4hpMYmmI1OiL3rLx3xEltjQSGVZUhopuiK88nGmIik9KmcuUVLN8Qz5WmMOpMB4pNUE7y7VL27yPCai'
    'DYIiGrxkOyhcbCPjcSHO2besXXkTuUet2yg3biNoG0S6pKFtehto5XjOCqsRYfx3BVXb8YCsC8oA3rBgYup0+6UVHB5OrccKt1VU'
    'D1FzrMuWj+KQxDlEyUltMTISyNYaSrS3T70VH2lzmCA4bERaPUsDhSO0kb4v7asNiVlAHSR2S6w+XYQJBbMK2EW0PTB9QWUjLndv'
    'FA65dEwo7hK2UI+1pQkox+GpZbmhSPEmV+tddZQNbOhDib6IxoXWa080GkVcUVKwwatdtUmm610C1Xaq+hcJUKnJGE4nayIEVoBn'
    'JD/rwbg+NEgyAXuYEbDJJR0sVfCjMRB+P7cYhZd6rLDneKOdIi0rFb9hqCKvtA3MaHAH0AZdjxB7ds6SgQQrE+Se42QtDXbeA92v'
    '/UP8SuuYIkl/ZY2kG/EiH7GfuHzaw2pNEz7I5Zj8z7/+m16GEBXA4n8W98lDqloADMGi5jzxzAIypSiQ8kDkYRrzJCXfxX5LgyWc'
    'RyX+RvwrrQtkalqfmhbV9oho7cB66xA2Gvo/0XmyAEeToXZkY/pJ9V970kVpQmM9ZFTdeLfC/dWNFYp8xZ+pTkHD7zLNlAQAX4sF'
    'mdG+rlw9Eia7LN9RONQlr0RL6JCsfz2vYQt8I/dopO1RmVEVid/5Jp1mRYuCER+jRm26HSNjWLyMF1E7B3g5LTETcVQMTI3mUc/m'
    'WyXchu857C47dDJxOnT00Fto2O0GG6Ng40LNu/mGggz+moJbxHrWZHCakmV4KXPTfoMwlENZLrv0oGscarFZB2hKHup3ApI86iYw'
    '52+ZrjwV1ho9ZmYMQ0RcA7pCBk37yzdi9GwsRgMfFfTLw8Xr22qxOE2ubyvC47f7BZHHifi1JpfZbg2cnagRRNwrN5su2a8d/YRC'
    'gZPV2Ow3p36ZwSippB01NH0BETGytAt/c3LyzvMIKQOoKV7AQJ5+OCkh0aGgjfKEfWXY06sTGiUJtWdwg3PLO78pKOcgn8UIK6GU'
    'shC5Ymhfv0XRcIXrp4muG5yTUZ1U3CYi7faco/EdcUzvrWsw4veP4XdXQlLKo9yZu8zJaaBGzodOWpBjY8gFPktZmFFTse/c8pJJ'
    '82lqqaSsJ/LUOxO8OJezlmrWyLk2mKXVE0+b6Mnwsh6h2/dkvbk/RsBFJ8Ty7JsrYqKYPj6dmK+VCp6KCvw9t921Jt3d5oK+Na9t'
    '4U08QgZ/Hho8YmAMjWZjD+ai4YZCVzEYkfVAis2oKTGlJRtAxdDuoXK27j5zuNeZq5PRaqgqerP1ec/6RzIpv771UPVqlQQYb6Bt'
    'NMg2hh5HqHXd4zQSzbSvpmgrbPH1+KJ0l+P1wIbK6kXnotEiaZ4j5Uo06zva10jfvUZ4zMVxSgh+BXmhS1vZHxyrqcl5UTesvubY'
    'AkVq4mdZPy2dhebuV2AqfKFTLOhNc716L248XFiOwKtg9aOuTOGg9fcfd7V4oE9OB05vRrIZQhFxyTpngZ3V4mZ113E44I5cZIAk'
    'cke0Bzm8yEvCuouDitVx4n3TJeFFq9VmSMslfaJkspGoB9cqwbQRWOfcD0xsC0+nZ+HKS7r6wheEV+0W+6pqdrOV5GWozUwwl3C0'
    'jBALJUCV4W5RbtvcHwBovGAwjSJWiuM11iwaBCiT6LBEx8tm2w6fgymGoburE/TARL89s8q/m2gMqBUGr5+FyAzY4rWMX+ZvMuXE'
    'YrT2QxzUSywnjz9x4Ll8OF4YbJcNpmiALxbIGJhW8qBj0PHylOfZe4xGpwVGuDzE2FvNCHCVxsVkNuwgUZB2Y24J777MvcCPOZp4'
    '7e3GY0N1mBS9WKrVFJPi80HbZNemAGiffdXEAfKZNodBEAs0yEBYDrFITHGcyZF4PITl6yIWLS3Jlim0lGN8EjMObr6RgYqaRRKV'
    'Dz+B8QZcv/UBhhsbXGKIRA/wYslBE6VPm8ZDhaDV9g16JmGOVQU2CKPSwDEqDWLsxQ/kp0gOxwc60GmJypZplOSsh0f4ylGza5Em'
    'pUkjEIu1L4RIiaMZ9Mj3bcY8Qoc8DJqYkqbIt0AFRDuEwqCZTD/QMl5bmc8C8izq+aUBHFPwEWCk62piEap6QLeLDgYKGAIO6l3p'
    '7A22BGw9KCF2jwgOMndVV0qRAN9o02dxjOmTjkQpp62uR1cRNY2cWiqUj6vqF+kgdy/SHD4TN6l+a/ZVvdGIjIXIa7ReAOh6mNPM'
    'V3W1i9JDrViTgR083Lt/ookEB5n9VZsyrJv9ThUqCudqLgTOCUFQ4GvMlY1e9R5w6H24bVp1Ju6zshLX5adqIElaU3opt+wBd+Ul'
    '1oE5pcydktAXA3NKPRNSK64m1JtWdOlTbFDVz1BFiVwoXlicHls/Lbv4flP1QJO0BSCqY6rCQ66eua02Vbl7nHdNZbODBDOZvWlh'
    '7UGLSpaPYoQNI4/2IAL1YTSoiQwbrPXHGd0PtfV/Tru83LlmW3qTrXpYdKJN7IFrT45Iq3z6Ke5bykVpMiQoRl7xgA4Hyc1hZZMt'
    'AGjzLW6PQBOjg0gxZ0bQLm2LV2lrBkBM3XHBpaias6vbNJRnpOeksLRzH4ZjhIesaKUGH+JTTZrtgmoavW31X8FAaiV422+uN7sD'
    '/M/WVAYtp+IcFx3P12G7Ufz1XFhzH0A1Q8BWDw4xNWDrPQ6g+PizEAxO7uQpWlySobZSDknxchk8awfHEnaLVlrt+CsCNUVKCozX'
    'sAuQ9fKEnMtJdbteTD1YT4ad9RbCyz7YGeoBZJYmlqMbDYmgmescJ2jnJsIG/KunnGnyEGNPpkLOxyw0l8ITc5P5OU//EFzTz8Ol'
    '3JxBj37xKWWV2NzBmAiJ1JNDaBWe/xR5hGk4iZCzz2HQUnkEr39QgqA5hT7Pc5TIEcgtlFvTd9EQW5JYcYTVLj9MIEaMfOFkwbZQ'
    'S4E8wYNu1Ye3d7bx3ZsWk9l6vUPs+JkRgdn61I8ewvjfyj9jWrW2mtPX9dk4FI4MzMGA9DOC48k1cWqvIeZBMslYJEflqzIMWJnD'
    'iocIJ/6MZvoHOPBZ2ETeVlnuJj7NWcseiJAC886FB1BeNXfKo1u0rRISveNVPMjm7bOiB7RxbVhytnjuz9CqSGAl7cNyEbZRjhdG'
    'ocGEVhoU+00Yaa9cENmmmnJAh3+nBbOSx1pw/xAiGDp8kawsCKRecEOCgaE1ObkM/qwCcAt29IfQvALtKTUWzZWbBN7ib6BB8mam'
    'B3OzZgM1ZTt63ZGF7WfNaGAbxG4UehoL1m0fDmkWMR0gZbNzzyBUkID9hj1sZPUKkSjnrAi3xFu+7GxoLzILAcT3Ecrcdczwm1wV'
    'aHVNtQGdyH2FqQSmaTW1F0noXpENGw4kCzxOe0wICZa4Izt3jq7cWOpMScjOkc8VfxsOMnWkG2nXRwj29nKBodCh12Qj/agDwJvI'
    '0Sbyz30q9MgtNrJzbGDnrUh0GCJROzH+Zfl+flPuyIXINfFkWy3JtfAJsLVEeaWxVPpZV5ow89CRy+FESS1wPiq+oPCUCTQiMXIn'
    'EkMB66nzMRjoH8pIPhdlOm0uBqLX09VFZGbyURIymkmkbu2iuIhN0BPxEfvJba/k5uVluZpv9gsq3Jppg7ty07slE1zAJIWc40jf'
    'HlegJbAFoPehuPW43EriMtBVg1Sn41ep5rAXDJ+KciY6UoYqfF7kRe7JzcxzrZydTIvmp/P/+b/IXyi+RHg3VxmSy9VtuZpUrJo3'
    'e+Jz/oXzy+tFkSvnZk3k2s18sRCVcyerCbnBdqGTHECiGiBFwM5PCxyZ1oAmOvOE5zGYMRcFSis7HXFEPmpT620W6x2TDxsrREOF'
    'rsSuzOypV2iWjBQ6hOiUXLmL9c2+Qjs9G3azs6Kb5bnT6WBSzs5Kb6fGm06nk9tyS042Xo4QBpvlw26eyV5Fp+fjs2o68HZqvun0'
    'yspSu+vrBrdyI7k/+jUEI6q3c0OkdnsYuzUfxS87jPWOaMQ+akOKz+N2/WZAOpHL/qbaLO6T3e0WEg3mK+CnCTWEUblUHfIteW5e'
    '1aY9hgovdpmVZgBiQ/bxWKPCnkw9mFOM7j5Q50Far0LRBFZr5fuSfGP55GgbUgjAIu5lrOBB+RpGBpbluHSdy7K86WyGo6/5qieo'
    'WdrQk0hsvnoYr3TAOXYQ9duKR7PahadtIHFfozlWo8BukEYPodjZNuUqemoqom62LsC+rV22KdLj1v2cdTdNPOPnQF9fdpOaCF5E'
    '1tnOZ4jx7bRwkkuYe9AqGS7KTSqZ2i03GVnh1VqzqMqZ1otMzcROPh2IP+1ANQSleVljExC6QH3GcQMPreKMlaLCDw5SDwPRB5CR'
    '12RKPrjDJmA+JFAIGypAGg0MmWwgDQd+o69lxRU30F/m1R258iZkVLuE1Ybh186y955+12PfPZyMGcB+lGsqO3fi7of6HTAMXQGI'
    'HLHYg3iAA6Rri/K/vyHDI1cxWDjlavzXVrN4mnzNF2unj4BeE9jWKn/FYQo3ZpXU1pEN28sw2YQvfwZdilfq42YIPnGqDvUq+kAI'
    'D+nBjyDq0nGcqg0Q216Oi9eWCcbxO0sRl4bnKYFL1/17BuNN4bf+9d8JmRyR/LiixyG++TZsZkzTQ65+0phUX38Hf2F7rl+9ffZD'
    '8sfk9avnL68v3yRXb1+/fvXmGr56BmteJ1dsgZM/rbvy59db8sv8dTntckNJPdlWhOwX5YZIHPUpvP67WSZqGlBGxew0uVzMiQAA'
    'FeD6aZos62RXbhIaEp2Q4wxETk8Ij86uFsKq4ZoMGQfoJqfbMfxnPh5DmYwSfmH/JYRKOPOE8qruI48dqOtWEu0iJt1TUHx7s6qk'
    'Z6pLzUDMwsV/n203/KftWPwA1R7JT4/IT+/FazNel5v9OoYGeZ/1AsQTGChmYWKz6k0Wa4h0//t6NVnMJ+9+Ij9u14vqmy/Yanzx'
    'E+V8IQvcR31D8tPkarkmCiV7JSG0SPgHQEARATapCBHf88/AnddUoQJ25ZQ8Pt/sZOEHueq0FWMFiFpBfqe/dB+d1FuauN2lhbrh'
    'px68Sn6lazRe00U6Waxv6G1IS1mRtVqTrvhikW8586uruqaxY6w9UW+L/vpIK0XBvy+z7J67DM3R0bUU1kqZSSHX6AlbNLmkvxvG'
    '9vzl67fXyY+vvrukDH+6JUdxlYzvk/+4gkP6v93ulot/E2fzCfOMwmeweoyOkv/5P/9vsDiV27oSl17yeEYWjfz/66Te3S8gqhJa'
    'Zy+8fW42s1wDKiprZgYZabIR9s3XcDdO3pGbtpOwQVb1O8I/oSFoiYyUPFYT2t9Nbn8E99TjLx/zNp7wgXW+ZP6pBQVUrSnJk2NO'
    'xlhTH069TkqNhVNzYK++m5MWSct3t2RNALDvXXVPqZO0ChftvE7K3a4kz0x/R7xc2XhFIU+6bUsQQB8be9/5BTA6YZ2fbsD6NGX7'
    'ou3a11Abd1HtgB7It/PdLdFQE0pFdH+uiJRCtmxb0cnUO0pNIMsm1Wq9v7mlZEFY+ZxyQE7C5NKqTxP+j1wa5TP7T9Nbxk3h5hmJ'
    'dj04XgTNANMHjzb2vQz9wR7QpVb3+4+RQ33iSaHSm7M8HijQZMj5gQyNLPQVu1QSdoXXdMtq6kYCQyURIsgWwbap3cI3AJUI7Ig4'
    'UQSr7TJ/jO2QS+iWiK45wowFjW9W1qUJhN1ZTXODL5WlnhingE2UriowvQBdn3BRjOuBdi4xupTycv2ZeV38D8gcQ+cRw2SMdcIu'
    'blgofnh2twof0VrS7Y09bixoyIzIGCF9GtYPWl6tmUq2N735akV1NkTZbiIG8rYI68DyK5teZ6Lj7XpZ9W5ZWIxhRWjsXYrhvKX1'
    'anFvq/SRjVARUmtGladu09qJ0CF6ZE/l2nbd51hH6NM6uhVo20LrdrabmpPyCFZgjWoM1svIMdFn9RFp9mjQ0R9qTEJ7iRoUe9iN'
    'Z4SQIMEIvGcjpebjxuG5/RqldsgflHXo7opDOrGpwEhucVc7mGtbyFzb0Qjyz/V8W3iRiphkE2s95oMxAcushm/zAGFBVq7Yx/ZU'
    'JmfMx1AftowGjQSthY1D5lwBgvvJJ+uF5XRU7ntX4NALZEYF6TP2jgJgm3A7zZzdGTVZZ/fMFIGLhA98GHhiK63Ozduk2HVt3XeD'
    'QYPEgz5g3Ff1blsRXekTXPbBi0fm22EZkU5f3qvEZ+x2njluxSw/ZR7iklkMF5fnTP7zITiKiIVCexkn1j9WNxb9GUFu1jxo+2Bw'
    '+fu03JW9u/X2HQMlBI3smy/utvMdGd0XP5n0eqqe22zX0z0zArVsSdxNaGOYG8VZf66RUKtXQgeGqRpAl6Hl6g82jUsu7X9WGyLC'
    'EFtxFenZ2P4JaX8soxnijzl6LPDm656yIH6ibk5bc4Djzq+hdaTer2ViovME+qJn91Fo2YhYWF2JwdmOTss/ggG0pqYxcnvvPcYL'
    'zZCNEnQzwRkGetGGE2eOaqg/zusJOizDTI8NK28elmHaj2uDjer1tqrrZFZVU9C4RVgzb7cntRfdtmPwex2No56Ui+pxeno+tAqq'
    'IVoY6/05DSShFjnG3Ewl/QTc/zRwgo2nq3/CjKpmsk6BMgmrFf0d1PCjhxB4F551HxpP27YNW+WPtDXTVkl76IBgXu/W2yqpfib7'
    'k6yJ8DRflQtpTmb8I9ED1c1BB614OnfOQ9w5bzDSFdbL2j71A6xDDPGQCGivCRLtIRAU3biNIhq6ORI6fnJWgpjLSfTl31OAmIYp'
    'urcv4wxqmYwWhApjs0HJc0P8UXUpNknr3diZYfSwxW7Yw86aTqUlKckWxExGtujiQC1H9kCFJ31po5g2n6cm/6NtuHtsXIHu1wG5'
    'G+3fkYfdi8PtRGMQsUR4mHDTT5sM2GnIepmy9MDjBDSNIj+1IONyCUdcidkepCFXZrHkljOv3MLT5FiBrw/JyWwOiW8VRW+R/nKi'
    'h0xZMBtEHe/2NflsU95Uxmdhq6y6/n7TXugkef3m+cvr5Or6by8urx79lj2pTHBQAslrsqHJag+CC5RpXm5q7grfMOsNuRm3YKRO'
    'YOeTPFmv7iDewRBDTilVkEZ6tIVAwQcz1uzZer+dk35fb+fL6ssuEYtWa6r4oq5Bf14bVrpSB9ejE2EfU4/dLpkzfzmIVcxOB17X'
    '8kmy2S8WyX4DgT9rMGMm5Rhcp+LCobM149R7/dzKaeNGrzMaX0p7/PbbZ0ldQpHgRKzUmMaQgkXWalSGJcpMPj80JeECIGwAYJ2e'
    'Re+cb/rwv9MN/JCwBX06SOCUbkuohC7gczOyDkTCKsj/4MfslPwkkzrtPbb212FWvKrsXXlfJ9R98/Z5MrndrpeVmDG/bLtC3Vch'
    'Olqwzm59c7OoWCLrCVgq+deU+bCfy7lgWSyCR5RP5i+BXa8uiRy4W5c0yAYSRmryCk/OJ5+sNyCv1fx39hoPHvrner3s8T7H1m9i'
    'OOKFipDmP/bLDX8CtCfIGGJhGvwxkE9n23JZMdsrgPyxEC4mLLJXzd+58sTfp2nYNPCYx2FRNBi+TBB0SSbfu1vyp+mAN5MdB/El'
    'k4eHy7Hwp8C4Z3Jl6k21WEAa8Ib8sq1oW/fGqtBAd9E9/40ihdK4MP0DAPcyXtLWjn1Alw8ihIN+PS5iQIAW3H8QeFXer/cwXFjB'
    '9bYHR5f8tiznK4mvECDOsEzYBMwggKY98plhzbSimZ32+OQUM/7u8vunb19cP+EHlzosgU9xfZ2RJI861hkwkJUW69boKbWeR7yZ'
    'bZfNswS8M0aUQKjBoam0Xjje84nxJQcgtq30bhcmnG7y0HPirSKwvLhanCEvHzRRmdyMOio+ynPC7M2Ugqit+SdxNIIEadZmQPVE'
    'z9LjfWobon+5Iweo2n3zxW67r3iEqC5MO134R6UjPKAeseQwkkWPOG8wuIDcnuwZDXolgr2HR+yN75NpNSv3Cxb1RQPAyNkvd8mq'
    'qqYJkVm25MpY0cgv8kv182YxJwRGGIS4TVVjjCOinyJH3cdzlSsBrv7a5TQ36oxpgDU252zgqJHKo4sY5GW1NCUBaYDMh8lAt+Vq'
    'uqABmbDTTN79Z7VdQ74YRFqu1sl0vScL3eOyIZ95EuYIVqZGGkfHoYtFIxx+nIxFD69IYDSfYdOETD5elCbPjd4MvtawISyadUYT'
    '+WGeILzCu9RQqk5Aw/40bYG0gPZHy6UxFzrcupxVu3taM/uOXsr5YHiakycpY6PnEg6YGozOoJw25YCJUD0mr73rlTMaD1wy9mAy'
    'KvkQS3kmT71fIwEfZGP0pugaGTQR1UbgvnRxN6JlJBtA1M8gr8DdwPdcKF7kVpjNGWekwwaX0L1skxDFbi0UVMGm2IGh1h0ieq7U'
    'sXErHGDXL0RSDGB7W5FS8zR1Ij0dgMJF/p/PjQdlAniYGUy3ZKNpHqnCK2K507ZB1wEW8ktQ9Bab7FotGQsEMRdii62O3/Wo1wi1'
    'Tl+cCOA5YEGBna9H6jUae/ew4STFH1l07QVaui9cLDhCvEme2h063NKoMtjsIjfANMbY7zk31ymTAd+Xiz1RwAHD4T5xBuZTWMLN'
    'iK/VNzHyv+/2C9yMhwuswctJmLDS1PLdmPmV22W5CAi6PCKU8Ma722prKbZgzaUk+YSTL3zSLG40rrZuQGdGOxAKCAETNrT7OjvN'
    'ioClD5mMW7XPdEz7AIsfYCpkN2/XW3Quebu5NMziwPGNyTSn3dav0YvCmhXher+CCXH2ZI0NqknSweWHDI7WrPFKFzQdlskKlPXU'
    '3NZSkh8WoCbDKKk0B212QRlgLMq0XeryOP2+a3wE71Jp8IOhHPjldHEzejTZmGwMA+0CaUNkD5bkwJRbAIxAhhP6MkbtiGFyuE7w'
    'EV9Xo6QAvsieqgOhrBWlxrIac96hRa28d3NN+POAzzc7TRvGyIwoYPz95gs2hNtqNyeiMlhReEe7+wXpab4jB2GCRjf0+/0W3VA7'
    'OW3eiFTOZaTyyfn5OdpPURQN/Tx5QpWUrvXhuJpBBEy8/dIeMzXCf/FTZEuW+dUyYkFrtBPI1OtRwvuCqiCMYzAN5SthlTXtsZhR'
    'DGvvJ9M4eqTJ8peyTTZYID0Tf2ATdNv+cYPZ4e+3M635SM4hM+oEYLQWQ2Lo6kYcqIbW/v9ApIcQxqclBraHDjWwj0E22bWgDN7Y'
    'T9HumI9RjX32U3zQ0f10WyQbdbdJWfej9ke1ZC1r96C34uYX27Kime4B7zzoWFrtfujFByHXJgIpF4uA1PBVWyqB5qK3w3n4oXyj'
    'v1oezmeMnoOHmbNm2mMyprDZxw6uDfnib3zuGR0oJjPDEFXVjpeSP2e8wkHCe/fwV3/3p/K3I37zngD22L7ZD+XYeJO/JpJ2h9aK'
    'rEOvH33xe7o4gHoa2/i8x7At871SVMckCWruYQ7zbQXh4tI3x+MfwWvKXQbUS+oJFFE2ylAQRdiydzDX8FZC8npYYmJ7hDUZhUg2'
    '7Z0RWdXSdvyCkFA9KTdkj+oxs0GyoAQIB5hB6DD9jM5IhcuMzagNn8v/4vgIl4boxBzLm0iOcIL5fV2RUT0fjSXq8YPKHUp+m6z1'
    '2mq/VE8jNk6xfX8tyXKTNXoHQLb/YFW+389LyjW4PRLCsMrNZnEvn/1+vX0Nx+0xg4hbreXpgrisaipP1Z14Q4QfR95Er0SQpxbS'
    'Bc1UcM7XMEzy6z03zEPgOr+HXn/3PYsSO41V+6NVyib5q/vZ7E/44P0BhUdNKyJO8VPEkn5sabPpfhoZFTX1HXdr+4Zx2P61aui3'
    'L0tTDmGk6nxP8wmSK55PkHy3XW/IZbEypFA76yCAvy1HN5v/XE1blUVtiVqtFd3QK4vTOKUBxDnRFNu0S/+cnhUdq5xTkYpSmnoa'
    '8yDFSom6pSQ0gG97dRyYb5arxPCrZ0t4MFCnww/jrkpnOqm/F3gpBAyH3l83tKgPKRar8OK1qcWBcttvnaKIfixTOsu72XDUHZ5B'
    'qnT0uza18dfqOeTImDjerGySVUFEPb8ql5VVnyPHizR5i6NCM+RqnVjNpI2VQ2TtEqeK3feQ9JNc0pSV5PlkvUq+5ZgIjyENbVxu'
    'O2ZS3ayi2UENlecCRIhWwT7JqqzKhxj8/Ele5mV/aObUTVLyZ6JdYIUs8OAruu2WLghCzhtVdUMk30UqcmiV18SZCEHSa2tav78h'
    'uysE3IFRKWfgpy/ZAHpuTvJRPurLilY9KZSW/XJQ6jADVTpD2kRPBs1rzKsLdwpEbLEL0cgi67NKVQVRlXfO0rMUGR3svP2eZ4Is'
    'x9JuYsibUD2dp+faBGkCHgNzsKaWV0hzOVktvbkzQoUwcPcI2x3go86qfplVyMSHZV/r5pxsiz5qdi3j4yanqELGnRsNnpHmJmiD'
    'vnHmg/4IJZ/CGGdZVlqz0/n7OYt9EfSsk3M+sIupiJOuaYw5TvJ+Fna9Xi+S1yUtXucwrk0NyX1mIZK+UYmkP/RU0mpfecp3CSIs'
    'zndHngC1lqMLvNxGu7s5sqa3UUDTV9VPLaXJrpDCXubzPvIiBNbMnYDnT0d2k/i1fZIXeTFw2yzSglK++L1MyxTqfok2KehgtVFz'
    '6qfGnHCSzRXJgjEjNduDZ2UlYbQomV1qUa+sczIYDC4StwAQrV3mRj9aJR5TVdvUgYzkFSnXyw3EOtJREu2eZw/zXAr+QZ1QiZSo'
    '+bPFPUUHB9irUyHbs3mCtiqgoZsqoQ4KE8jQp+x8tNv/N2xZu/hTjEC6/ibYToeVSXrzsDUSmdVILTIfToe/HFoAw4OKSX1LVJeo'
    'zfopFAOja0HxjJ11D/A5pxlIyOxan9WkbxlIrbdloqd4+OYRBZF8NGQX+I1gpz6RMEZPETzYV0wYW0Ngi5511L5hBExT7Z1Pmhkr'
    'rhua42DsFh+JUZAXY8f6ylks2RHFpyPfUnD2jI/BdG1g/BsbBOfhxiA4H0cGMSFbunPYknBKsFZ4VlCu7AFGoUVJ96lJ9CkCmNtv'
    'pEJ6jpsf42NSDxLag4eewYydEtTDAps74W/llpZbMI5vPrKPb2YaKFi3KaKm8esO6YtfDOGFZms0kN1xrBLxq7wezlOzNHjmFjhV'
    'FqMwoHQuAaVTE00aY7KaqQZRRAc5+TPxFo5EVislf4aYjQnMLtTxYZiYiqLjX1rHKATzds89Aw1x4fVSF+7KgbAaHcLE2/PfQSv+'
    'Oy7GxSRUzN2vtqO15+ykjCj13FxdXIztp+TPSNOmyT/fD3w7ZPE+P4szKeo8P7cZ8Hg0Hgnep0B2HutpiAXYpjq8L1Si4QZCIRUg'
    '4kXX+ViIC7jAIIWF3BA8crwLwT44i+ificdsg9WL8p4sPV0uyMP+YwIR9gm9M3V1j7wAzS/g6R5klLESSBsiiVGpFn2I72vjoxTs'
    'hnXZ9Cg109I4japKVtVd8voKci83RCScJts9uMpZ7jb+qjaiwxoQZHZYC9X9EW+e8izQwxrY3e6X4wPfpabWw16dAoZN06ZOpRkK'
    'exSe21LXnfQZ69UeGxW+oiiwOtX6FcWygwda2UgOm6bNkw6Vo/I8u7r6JEWn1IQ1am8PWkh5T4qL9yjLt9LTtDuaCq95gzEkHdVh'
    'HcMGtQ4CmyX4mbVvhxH5o1lL3SOKSMH9aVGOSrwb8ZpF9sqsWo2q0Uwzl13eVwa4m3FYtWIWupRoeLZGD2YbY2+QpZzJIgiY8OvZ'
    'V0dRyEeato2aq4x5hq9v9xXK6T/ogLUmSq2BNnzma0GwQwOdNivU/lwDx1uV84W9PZQV0iRqSw23d6hv6ImKcB/UlilWHFlts7Cv'
    'u/6Mp5tzyB2bsE/8zrLswgvhCJas22ryrtqyYDQ9KXJ8I2NRdK8g1Q9oSdP1aj4hQg4RT8njj2meYPqHJC/+0GWBO+SXIv1Dh6Jv'
    'fE35r5T3MZITte6WOvaKeUytCkWAGYkI63ZtLHQ3PSam0IZ+dMbjqXXumh0HaYp44ka2NY/RuiZwq6+qxWK+qedht5gDW9tHqElC'
    'DrqjPxeDl56g4dB1wUv93r6P01NJv2wzv6U3jTCOmrjxdESbnutayIce2kbYjo/oqcUlR9Wovj3H8/PzwJ15NBPw+xZ0N0JtbBRb'
    'FpzhDsg/hWaLn6ZTw74vXvYY+MltoD9KZLJqJ61aTb7F0RjW3bLl90tQ2C800zjMaTMHrsIFKbnhk41WSUcc4Uc4UIR1mAsuuvlV'
    'VMefaGzz2dlZYJtdUpZUrm+g2q+uvZmoiJX7tPuPxoI46z8ejy+sZ5THRt/5KrVQB5QyPD4fT8U9SZ2qd1Cz1i4/aFlu5DGR0w9I'
    'kvqRMywy/Y67dBLlQyyftOw49M9GKhfFqV6RnWajzoVlG8p5IUTTNNRRUIuZBnml7PyCal8tplTef1dtWDVKqmLveLzYL6Oi6Gzb'
    'dVs3eEelW1ge3pHrEqUd6dIH7iR1xxJ2SaJk/NufBycVhg0MkL60Ak+55UV5p04x49eq5BNjhAzZV16EJu42eZhD/wqi98bO6HEy'
    'bFLa24FwrvOsmxVFN8/6bhncxOQcGLBJ4AkrukBLcGBXDJ+zOeV6zC8ghCzoeLNR2h3Qv+Bq73iqfMBdhWJ4aFTEri7XT2kMAaUG'
    'ZyB9fByzGaHMUWhRIMr78mf4NmFl4Se36/mkguqaNi1MZz32JYWEU+ZrKoXoQgi/K8EWQG9CxZAykHTY4PSYOH4mxJEQhwZ4D+hB'
    '5sGCU6RRon3lcdIzBtscgijjAa1ZUoiYv1PojwkoJYS//yQVSHpR8VuL/lxOYOo9fYKsYo89Q3sXvttDHZ55uVjf7KuE4U+bqz8l'
    'T/TEE7oG2dJV7bi6JTb7GQ0yEKZqF1pO3obmUCaqImWToYhpWLtya1RrHXjDGkRfroZluztSJYbZupfZjA/WBWppERZF478/PAoD'
    'poarFCYxQFbOhWtLkIbzwxEE4+cltklOy6ytiY7fKq6ZNRRs0oYaNyYHXQgZWD5qHlieegemAxWZIjfIO2KkrHiksVw6aX/x0xNC'
    '0QDVNeVjFHf3ag0bTHRgEdWu1xKTPlWkRkLrxXlSLTdE1HOSDbwQ0LxqvHlGWcQSFLnTql75BISnk12d8ApTifI7P77+S/J18pr0'
    '3rHdMz8A1DRkGNFXeUE2Fshyd8uCjb6fL5YJi42nlvb/uCKsgSLvrnbbNc1wm3MlXCVnsOe/+WJGXoZ0SnJAWSnkhkAftwV4WGuh'
    'iz60e08eSdBu8AoUYuoQdCXK/9qT5UKFgrRGp+ZFyKruoJYey1s5uJVqNWWtRBX5TJpHw9vx6ccGdztHuFs2MFy4GNgizvn6aPoF'
    'xiusaifBevVZjhSrd6M8GGa3qcyZ8p9ZLCbLkC4Dybihpbe38PClzx9y6ft589IPwmufhtZetHHA8ltpmpoFUKgDoDLpDE7TjP4t'
    'uWKfV+yx2uR5wDuYdkNe71Hdq25CjDOrdvtXz4QOxjJqdbr0GDssNcqd/AtAJWRlgmpr5vSrl+wr37SpSVe8biId8k3Y05JC89Vk'
    'S/nik0S8Iijd1xj8ZtTOlY3RJHStoWAzKOofH5uwiLJ2H4sXOxcREU+9AWbwc4zUZVkeUJBKzybziH2hhEN3m18t5zvwZnMSNRVd'
    'tUKna/6cxlym1WRNDgBdCLpCu1tyo9/cugJPuIrUR09fPZqDvG3DzzBBWTk3lBsDYm7c4uOIFYwtGFSz1fA9wdDGpC6eCE0p0l00'
    'Jpr5iKvc7baPWfaoartjjJQp8XnazbK0e150oQ5tp6kkl0++xVw79tI/oWWR7HEbwYd6Whkr5/b9qzc/Pr3uXb2+fPb8++fPkhdP'
    '//bq7XXyWBNAEsI3dOGkk6hScDo50hSP5y9+TP6YXP8FFIfpvt5t70ElXE3BLPPXPz1VdRqsyIRDhR9NswsLUVz8a6shCk3q3CzH'
    'NtlD9RWi6tZJH8qcJbPtesngGyh+MHdj4iFsZqE3Zy9br4HSaI5aggZl8nwoVyDHpvw4O03Fp2ze4FKFrzpiORzVk+ZsgD4jbCNE'
    'EKpJ86qhW44AxYoJ0naOWitLATtqwWI03YxeKGzZ+mpeatm+YXXysHXzLRunRbkRxji4OagLSwlxd+T8FvQp3pilKftYzlGLrOx3'
    'R66w3hBylagjZS56ihoUDKf/9V/IXVFN5rP5RCl3DayIDtbLQMgV0IPI36gp+1qBCEuqQBzVyq68aadKyKu3pdaQ4joDqihkTsS2'
    'L5BMaVjeQp7S3Q+lMXcUSYcuDL12YJYQhl91FWMZEwmp3N12kzFh8+8qeECaUEV+lH+1uYHhA8oSLTI7k4Gzje0ddRm1PQ3cagqA'
    'ESEKiNjibOjZ4oirLH7mAlLng5K6qJx0XAcxl5z/rnKWIvWvgxmcqNbMrTZ71ITiLyF0WuobZFo2N8DlVIYR9kkmV05iLpGGRih/'
    'UA4TuUa+Ofhn7XCm+FPhOZRGSlL6EOvVcFE2a1zDAy1Ibe4CnNMfNXXTDtNm8g85T8uwZW39w/FJttFfHWCV6mUOi2PUd5ZqkaCH'
    'jgsR2MxEMHprq6dqCkK+r6FE5Yrf5PB0rUR9zM/yoNdLfK3bw05jYlqEoZmLgKn4YXqNIA1rXFQwQMdFv2gaVaxYe9h62MlFbyqQ'
    'ZSHaBRDuah7cABiBhlWB1fOmRaLD8FTHoFNlOQ5PRdMGR6kdIDbqdJlDm+FX2cFjgfjcACATmyir+d0011y9tqXLKIATtaQQb9Zk'
    'cw6hEUbkAO4EujYTnY3wH3cXLEvocwpplIgC5NXkXQJlyD9JLs2B6TdQu5ecpN6k3FA1u66A94ECSs2wHKKBfMvKqTsJuhrKmpZ+'
    'm2ZuqDIlqX7a7fPooXM/+JqLuNUvGjDYTCQnM/hcWsKfg6L5ZTepCS306mo7nzWbdo2IGl8OcTg1SQ3Sa2GFhZpu15vebL6g8Knj'
    'xX77mLyIBJBy0ylEmTeDQ6mtOxUQGR/sWG4F93dhvzOjsX2JYbDlgUQngqznmzgYAGeHjSC8QfQOi+jQQ3c4d4z3o+mgGh24uUOc'
    'zVJO6oAAykl68xbK1XzJHSB0fZ+R5X2+YgA7SSXFP28u2b+/q+5ngGhUG+9z3QKseeZWahIm/RGS4P/2eACExy/X3Tox9j/zvZR2'
    'LmQ0iE4c5PoV8DVa7Or5eVle4Chf9su0pOMHM4i9moxmaBAxGqatPL9kR84QmDc0uQKNFI2naCz42wZVuvCs151KJ26KXgXWiLZB'
    'SHk5r2tr5YbDMx92nR0nocWcUeuRae6hUd5Glo1vMnwgTnD/+TmPiuZC2W21JFLZAlqjQOZB/jJLZ4PZ2I7IpcszTLvg4cpTeuRM'
    '/9dJnvcvos5qpiSSxvFhJD4cnl/Ev43QeJ4O07GVZOLOL+tgKCfuc3nRbjphCjSbZoGsZkAXCBVEmoIG7rkg/GuReQiFipH12Mhw'
    'qUZWzVa5E0l2LtOknEWRUK85KikcmDjpigUDKRZotwW5qSt6UWj3xEd3qn4pgAeXvRF79oyMY1slk3KVjCsK4EXUYen+mmzL+haw'
    'vJebHdxmCxaM99dqMVkvKxY5SKToCiLxyFW0mwOOPARTrHanyfNdsiTThmhAgDuCFwEtlPIiHrPPLKKn9nZN6KDErqltIYSYcdw0'
    'e29Pt8sYXasrRJYwh8/6593zvJsPhsBbRk26l0rFgLAbgLnS8qA1LPrBiDod+W/nIk7aRX1xgYWHVHODP5n4yhhkJjigz+eiixxk'
    'ntXbDVARIaPJfjyfEMX3n/Nq+5hcNINudlpAk0PyUweTOPjrhrSBCws5EzFMqVITN/wihh4IkmkSB7LtPPNau9wourLjA5JpRlgj'
    'eiVo/Zo8c9B3z6xUO6USd0U6fcftXDNw4aQ7vUd673tAe7sCcayD5sEOnf7zQUT/9W67Xt2oy41rvluoPrLZbzeLquNfQGYur12O'
    'wzBj6I74uCAL32cFwKmQ7B+nRBSWZ+4cThsGTq1JgII3+6GB9AV3kVoPBf01swCDG6Aj6DopgESPPusEVwXKVZM9v/cyQH0bu5Ag'
    'VExmw46ezzNrGJ/oAk8iO5v0y2oaHmNNPoZwHGyUzBoA8i7/Nz1NzzpR1O8zLRiNKVbWODq/QGQ12e+EGArhlbtyufFkzcdMTLed'
    'jxwIiaCcF309nsxG5M/EK15m+aBbjLp5nxpo1JI3X1lNkrWfCxuuPIEeHT/PGEoTg0yLjp6xOvSuQ7TCcDh1yS6EoH1qS0SLuTTO'
    'WQhv0gSl2W+Z8VyH+BqM3t9aIoum84lwdd1Oyrtfb+49/eK4erQ0RDbbGuzfkIy1ZC2lt2dWoQGfNbxz4S/T4BP9eqC/+LA5jZk+'
    'uS3rx6yCOzXnVtOOKiQeuhvNUyGENe81avZqE7+B7O9aQJwSAUiLy2pXYg1S1H+HIdl1J2ypYlDwTojUfrNak6t80iPCvlZY2Qw6'
    '4EKYor6cfWQTqGElIw32lJ3MtDUS4T/ToPMm55P+dNJMKpjsfmZkUDPyhAVha/E1kYCTZ0SaWS/K2gqlpisAAAWESHr7FWC3T+kH'
    'bP+QyJEvk//51//75UVQqnKSK+xg2bZ/k6vLZ2/fPL/+W/Ljq++evji0FaaYEd61JxLPvauRjQYCyN5+6LSesZ96s/V6J30rZmZM'
    'rhdjsLIOkE20JEtHnKRiZLWaejHJyRghJHhno+qYo6KRVT49ygc+5QzX6PAJIaQdmF0WU8VKeBt6ZBF/vPeeLrNbN8Q1hCLMwrLX'
    '2bpAX8WIie4W4wWC7oDzDX/IAgIrMjD6csFQTDFeq3UiGNNp4cy7MCJHQk6BZuAFJ77GmqxjQo1FPDE1g3KxMC3BYjm4MODh+vqT'
    'DiCK4bLCUVGsR5ybkX7Tq9czo7PF+oal4besG5QaPJXWDBp4YlO8t7ofW6rB+WOPvkVevnhrut4pALczHZUJ8yUU6R88dVa09k7X'
    '76idwx3EDRjNkBGczgDbDXtjS8QQ5Hly4+M9iG033phv6HhiU4ditBZYRy0zPmN0YO2HjR4TLEekGhsMnLZAr2pd2og5MxBxgzvl'
    'zC4CcGGmj2mI0AVuQWgI9vJwTpuu6cAwmqLqw9mwm50V3SzPuQ/LYmooybEmEaLj3vkzSB+iGUSsRbNJhCZZgwhVIgW23DE6RDvf'
    'PAAvOteAytswoliewwaJ3vGiI+uSJ2+QwW0PPYo5SvGdC3Wv6j3NV7N1/JHR31TmNudlA37o3ONsjcDiRu9t790ZESblv/TR+Vr7'
    'CKr6uFwlzpXMSB01DeinRPpprQbFRd90ytIR8v5+NabVstDjjAzI4AToiGiLfkuE0YA5JI4aYZbmxYvMIIJcSBU10oBYh+sN1CeY'
    'aGD1hqR+ES7856/k2Kgw2m6yd9V98lUCqi6g/N3RaD+2ejx0aindoGBnUysbppZBx4n5hKY2d6S191W5kFTja0rjpkhbIuzrplol'
    'm/2iriCdcjbf1jtWqoeOXfPswAVJnu2xZ9mCp3/o0hLKHxDrRooMo5AhJURCYtAi2KuFsBbqL+uhJWQZxHCAYG/JXUpNbKQ1zZVl'
    'jjgDt2hfwl0fpPL+Sv7CCv718sWzVz9eJlfP3lxevoRPftNT4oGI3/GCb+S307ta1X97ZMI0OSpaAJvAdRs80lGWUu6NZWTBw3c3'
    'InxX8Bc+Hh4bqoWzGqM6CCCV3uC9cbW7q1g8LeaaJMPT+lf+SOfmdY0ATgI6Y7bB5AKDjxjrB5eiMZbJouL1rHwiBNKKx9qqM2wm'
    'E5keOp+nDYUlBZnAHakdgSQHR3awO6KhG8zArr3IDOvBrfZBKFOBk+spWosyoLl14V0TwETo0Phl1hgTjWxB2/J/YWqhFY+dmWvx'
    '1E1OPhaxhN1uiP/O8FaavTpRAKwElq2i2yjsWhNI8d0+an3CdUgncN4Lau2B8zZHMwWImA+tjlzRwUwSWpvlluEr+tR6/Dq3m/Sd'
    'xcRHBsgIXK2vm5xMB+Vo0FeHc7Xmr1FCCtYx7EvPlU9PwnkUvxS+ZzZqfgdoFmsn1crGEnyYC8GE5hkaRz7ixlNncEpnf8tV5mje'
    'w9lJmC4cYkP4CxazbI8MR77Ubtq+UTyB/mbgX/rIxmF2rGdCgvXc4Q4Nhwn8vIhZptDKqfyWhTFD0Pz28ul1cvXD5eV18nXy7NWb'
    'Pyffvnr65rvfvMRpiJ4n46oEAqwqDnPxAcNj0qJBBePu3QvToV1GeZCe6x/2iFpyQ0gL7uhyoWpFTOZbIpgAGgb1b29+7iKMlkit'
    '7Cu9KEVqmDOEK2jA68Jd2KGnH51JKq8BJs3oEVeMN5iuNOaj59KJCToNrlwGpTni9l4zVzJBljuQ7CiHrmqNYZvDE8QTkbOcSHgN'
    'PUj0IiokVzMUuvjHgy7ZmyHPX/IE6A5pbKPXoOixd5oJLkMpXwTtYTHBQ50LexFDUcCn7MExh6I2iohkeaw5r0E5cWPnGr102O02'
    '7FxEx3gFODoUTvRYFq0FiQ4Ay4MdnneMho2S0ZlbrLWpM1y4o61PAOJKtp2nqaj5I3sYOF2czMrZsCpxB0ZEsYFBQUOSh2iRyj75'
    'jnJSHgOTYjOCfY1UsgThEZ46xmQMK/NTr7XgxGHCfmM1kEOLqxn09IUZ8thTLFYbX7SOL6+ql0Pxxe16R357DOLVtLrpmIM4nW7L'
    'm5s5DdE1kdW0JnkLObwuC0ikA7eABDDwwskQPis65mqPSX96ZkSaIoPq8dVZ73cUDU7zi7tsELRv/mBvPZvR65ZHMKlmWaxA0AML'
    'joc+RxYPbp405jyEsG7moNISrc7YV/slEk7hDd4woyZHfrmzmZWKYdCkd+bGdArJN9uPeHeNvk4uQ9uXAp7GSs+dRrajqKvBMA45'
    's5PH0swV0LaCIg5Ym4HElHi3Y6hf2SzStcAqn7AKOkcbBsLShAxaHXUuNPvmwKWNgB9RLM+0qiewME4kjqiNYF7ubNGskMACX7Sz'
    'TmzojeIY7NdtxfpDjIEofeh33NAQUWCJzck+eaLhZVrmQS1m2eON0mhKmAeMIFpFGgcxGRW6Jrr6x37JHbC+wCxz5AUartTG3Nro'
    'ijWMPRp0mjNm1ASrHyn9JGdJc6jAuRYpcFKU/ZF+DUEjeZk05tCO9FjvrOxPi4nVyLi5kaKpkT4+nWw07I4G8JcPRE1nQvGqjEZg'
    'd0IR4jlLkULXtz/S5c5yjCwwN5mYj7lLqFXV0h5zFunkrBwPq5H5mLsMJ+OyGBQD87GGiebaVITnGbMDhv0Q7RSsvqvopqbZ73dn'
    'AHrx6k8vnr+8TP6YXP3t5avXV8+vksvvnl+/evM7MwHV96s1XLQPYQCyMHxsm4NPk0GvA6V+wy1CSU6YVcwxe+05rv3FnmvY+nJK'
    'HqfISrYXTEtfPctTV4mk/1zY4HtYfT1EqXTT8ZlSScOwB45y0jcNKGKZ+FrFR1K5ugLMnjuCZYp/K67hSvgjTLLOw35ZnJ+76aRD'
    'O1+jL5QQZyJPaLyHDEszkRY5fUHgHkhhXUo1PUE5/NcdoZ/dknphAh76sCTnlQYPC39DhdGzwiVDc362c481Eydz0yvXBtMb2XaW'
    'YqhOrVxHWHbdFqMfbWN19ady4yk+AUOEtXYL+042fqTsC23dTQ46E2hPeceMGKNm3Aun7O7v7p69/uHN5WXv6bPr5Or6zdtn12/f'
    'XCav/nL55sXTv/3ObloQYuH+JDeOfffg1jeDs9gc2pWm0+45s88POhdBR6lhgM/1++NMJiA1U7Vm/wKqpKVBwJfZ0+fpmzSrQC5e'
    'o5USIDWqSkKrZAXz2bd79JtwfMs1XDeTd4bEo5beLFPfZI0fdHCTsWvlwPKOouz4KQsihHHX1U2DL0gBm3pzs3ym+2OqXR9kVhvh'
    'C6Xr2PQcgAWOAbx0GRq//F1bF9DrPjRk+ovknjCig2gwLxvV31xzeeh6n2hh3FyHddCxi6/qLfQbtefc0J5ZPVTRAjOAxFOM8JhE'
    'EP6wcAmfenH03eObBfYR5ZC8wCEBxaRpfd0N4F/5R83lZ5l0dmH4kWLcVKEhUEGxjrSP63RvBHX7IpK0PvhxljZHTJX3JBG6p8aT'
    'yAOdUURXN+2hcby00LYWk1U4qaBcUnFViJPxbtUzubI/ZyIXJlbUoN6iXLSd+xCZxXhoBgYyz7hEOzy70W4rUMrZdaQ3xcP3C7tf'
    'lVz025YqQVR89url9ZffJV8nP74iMuTrp3+67H375vLpn5Mfn7758+Wbq9+2OEkD8ZZrwAArt++6ySncvqyulxnXxkSrR75iaC+r'
    'O0LX/Dcrkd+ME9zZUa4ZgN8V5N9+yq2+j/zQrihQp6me8i6cSgdYCZyP2uSVzs7L185XFy7EvFtvxoW9B96oryNaZcpt2cWgh4YI'
    'h52vaBKGqgU725Y3SxGtaUu/0l11YReImK+c4Wfk5pivDthXbFfdfTDVcfqJXg7Ag0ih7IEsboohhgOCoh4ISf1OjxpWSPkthdEE'
    'WPq0rG8rV29hLgfQwrVSd/SGW1QlW0hm2zBoy9IfTt/Ptzuo3KvAzj0nyc67gBp2e3IDkKHWohqvhsQutg5Si+CigGfq5PE5DX2A'
    'Fe6yQh96NS5BC9SC16OPsh9lSRCof0v3J/mGtLjcQ4zElAtA/PVkPYO9ec/qWX0F8Vzk2lhNyY8AM6geWpEdYQ/Rzs2SP4g+ZMWs'
    'WwH1LVjAR7hmvmVj5vEoZDiwfrw+lhgUsjlG8T8FJfLlBbpnkpZ54LDXbzTiwfa2ITZzgljyvINkqqR8VtdkEnLBoeryFFiKlk1w'
    'NydaDEMtmvKKY9Ss6pstR015hNc5hMp/brD1Iy9qcwBuU1rqcnet4PRn2cDlO3j+ry3fPUpQoApcDQwmVfB9CibwwC4QOocNGOs0'
    'VosDIymsmt5UsgK2vvM91AZPhHbmBOn6rPTyCaAG26jRsL3GeqepXU0zlABiPGqbRFglAq/E0FDcVOmT7pCwaj1YaWsPh23sGal4'
    '4a3oLL9kn9Nl5WUs7Hf4d6oItKL91FNY2f2GTow2utovezqe3aeYlH4lu1VW7Ws8MIkUf8AqrBS3iYITd4OUHTTe/R4UjtdP31y+'
    'vP7h8vr5s6cvkqu3f/rT5dX181cvk+/evHr93au/vvztaxwn9JbvQaQ3YZAs4xypgeEWQMgvoqq3ICl8CJBi37mKufIhDUoFVN6w'
    'beo6BMvItDbw7FJreqc0BRwzU59upnr+q1l0A+S0QZTR/FESEQLpqZ3cFnrqUTyyB2KVfsTmLFM2zRj9vI1zOZCAZmHmYMmxFsSQ'
    'bV00szXrrgrIqn1BnNrUmNJB2Bj/Hf7PBNZq6kcQQi3IvydLynfPn7549ae3l8nV9dPr54SnPbtimHm/A4YGNccowlstUPm0qlSJ'
    'NHI6SI1ngBMaG5sPZoUaiimtFxA24UbNGNmuUgYx4mpF/jRpiDTLuU+sRRqD/ElZdP7FoWzBHtCngccbtUj/MZJq2MhYKu2hS3TG'
    'AttiF0h2GYVzRJ8tV+/icYfE5RVrco8Khiej0LO6D8JZigNd1O/ffoplnnui7FtEh6MeDy1AKxukimzH5OjDE7q/RSq/MY7es2hH'
    'r+xQy9jQQ4Ss3CIvVF3ADyo6AXNbHUdUFjBdMfIRVvP5cwPGyFA2k91BoHb94QMPBDQjYFP71WEDYlTzgAParXflwsOeKCfKzWRS'
    'yC2lmYdpDBhs3jEjhTKN6GnPCHpqi4Mcy1dYV58IOdUBZM5j839+B66tH56+efrs+vJN8h+v3r55efm35Menr383Itk/yM2zqu57'
    'y3ITkMnI6Xx8nr6/6yYjkM46png2yluJZ0afjpzWJKURav/HEmL1aSKx8rouyk1d0W7oT22j7MWhJW2zCFWZpKdUboAYf3evpXvr'
    'MRWhWGwzECj3sxHt0s4dpdnJgjrHM5wfShAkG0IrqQsuzGQqsUosTkSukh1+hA/CiDjwAvXdbedgLab22ydqGNsFllmajVKWmiqV'
    'hVyoDyKaZijCYo0PHig3rgF527uKnow9trhUUTpGUoyF5+4ZIYiSyI5dG10INEDVG49A4LSFTpi7mgZoSz5Ua6vQmO2Vxq7fBrxm'
    '2kRFGRhGyZE0EqvzhAnanGzAUKMP/JTXR2sMcik62GsBaAL95RGaDYjuBzRejr1DMnUCtQmL6qZaTVupn0On6IIQ+iJl1oPkUTnW'
    'Xn1X7ia3WhZDboAwYKgXuZHQOaeVnnvcUGozmiU5pItKim2cBgcqjv1qPq1ASZKV4JNZVe722yoZ7wkhrqiP7pQeEP4F5FL6SmoV'
    '2HXFuMlHrRWRQuqk+RaGIfchMTycYxuB2YtYPiNj2TA2EIa4M9JYfVGExgI2B7n1vUFuv68MhqsfXl0nL55fXf/eMgNv1wwFkqfL'
    'Ga6fqOTAR2jVtZvozEDD00LR7HjVvo/26AJJgPqjEkrJM5dIMKVHSUs4JSwAJUu78HckMzb8iEohVw4Sj965cBw2Qy0W4wFglcwN'
    'iMBWenRaLxiAa0+sf7tL8pFTJ0cIii38XHYJnI90WDxyC4eX7beoMYPKf7wTXncqGrWKXo4UqAOIZkOvQTpW0HjYRx9MPF+hPcqn'
    'NH9lO3u4vtYjCawWTmEARKowPiNWTzxy44zTKmRycVaVD1htKEyfIs7EgQVbqRePGquh5374LaQSOmbxdQuz+52VakpUR7BBKRHs'
    'lqGHRr3Ro4gq51EOhdRkDIxMRhZGCIf4n/tr0MdnWYVjCh4q4P+Rt2ARMvXImvUZkuiDRO3bRCQYAmG5CTM7cX5AfxE+Db1s/UCI'
    'svJS/llYtT6qN30Q45gx66Dr45He2Q44EvmvA11rxGtLFCk7WsKHUeQSKr8wmpPKnboX0VowIiKjc6Wf3FJmlCg1qz9UzBp9Hi5X'
    '7XlR9Mf7PCDHas9zd1vghSWhi1YvLCqidqkXzpuep1hKPIFbmAjyppdW611Vmy/xoonBnhb62uZc39NfoLWcdzzaMoxO6fCcIDx4'
    'be067ygWLTEV2WBOC/DJlpxaiKmOaCcrOvacpzpH6At24NPQ+Rim2LXZ5L9xSgJGRwbJXim9N3YrnaJH9YrULmfs9XI6Z2sHBqBa'
    'sFhmWnP4ZHxCmhUtj0kDBzndMHBqY8MpkzExKGxidpDtu45xQOwSrMMTGtTcTeTvGqY9VgsWLUDkO2eqGx6DFV71CJPKL7byhbvy'
    'jWUHkCIDzorY6y8+jtwG3iBhmFJaa0JDawzID+Lf9q0AJKSGblMlCzVeG0HNrLdGDzCFw4LgLikgcYSsJqz8gdRzvAKkPa9Hvzs7'
    '1rM3z19fJzRn8rcfvexinUNwOkT5xpqzTBOP35ZlFCoY4JnZYDAxBxC0WKlHf00WqxE1WA0fwmCVjUhLeWqykk9usnKWNWiyOhlz'
    'rFRVY16ImGg0G5o5NbyIL4/shonGxTPQqU0NYPlHWj1ht1mlkUvI+gHf9OgeH53K5XGDxGWl28ZqwQ8hfhsDUeWDY+wJ9tuBdHuL'
    'ZJWHhichy4mcjAdno9nMbFwogNEIyLIVXL21g3Ml4rKkWR2yzUSsbZZ5gsH89j/HOur1USMRe+eNpWwNcKxTeRJkXIhdWmykSSXq'
    '0xwJjc5DXEvobrJDze7Yxuro2+hM21Kt/dvpjdX+MNpGjeyeW300oDkJgzP1USdDe4DUyM3rG0ZaujE3Lp+QXY7D4DkMqjlQn8eK'
    'L2lB3018o487Zx3+lyPHlNGehdI31O5Lm5lgAxjxNGQt+i31SR10ySZEIL5Zb+9lsFpEuUB7imfIbEbe2GfW6cO4IM7kYkZUVjIu'
    'CyaYGBeFGpVUJ6T4Qm/oVVXXj7PTTB1ueIXHSbQPlMBA+FmT1JjvHJW0AYm9weM00E30WmeMryYo6rvPBSXfva3eb4O1omyjkLYF'
    'RpmJonaJ41QYmKeJ26Ebatc7T1UVCPY4tZjRuTnnT6AHtakaxlvelTc1M6wnEaWCVPiJAVhJSQAldX4ySS/m6eDxNE2HZGCdEV/F'
    'aQ3MzyAwLC8/yu4hjuC0mpX7RbO9Sy4mNdMiJKSVPyiQE24CvVjmhAwxJyRGj55qCPQR8NywDW4RseXAzGqXIDRIC7mZ8ndEtcdD'
    'cmUHQVFO98HEKFEGJY0OMByKrZaLwGxVeJVmU5BSgrjuRzRGZJxjYwWaQ7XQ4AtTmA/4c12ZT6u5KUS3I9HEUJOrWg6/N8EaXN6R'
    'xE3tXj1mCvsQtn2xumWDplrkmkXPkl9GMqbrv/9F/ibPaaJ/8nXy6tmbhEby1+IrMMQwHAA30l9LvxSOopPNdNZbT7aBtICBAAU+'
    'hec22/XNltzg3CWqgZsMj8jv0nRzG8qTZ+owYfiRPQphuWnMALNoFBa43KpyefTS6xpekG5yUo3Oi37pqMgiTawv0sRENdU/yAEu'
    '1jdKeG6fwu2/+y25lAdeY4Fh5l2N15zTYJg9qeCOJG3w5pG2JzDl6fw9EM7x+up2TP72OCFLk0EoH5yR/9PpNPmOsEUKCcYiXMmN'
    'TwGigFTUITmFoz9dTyQ3bHVBKUvVpFxMHtNi9T2qVmlFcoZarSZH3MbY7dAXyGby0tTipTqEl/lov+MgzBnf04htV79rU765YLxU'
    'W81YZpqNgpsnETE0xiZ6IQ/svQZbJsnQG5ZbBGUQG1Oq1JZ9BTdch9t4/QGV0VHF2CkauogbvQE3v7qVBnTIjTxNrWBr12b+0VyU'
    'AL6GeCxkS3RRJFxSkE3fbOfTC/pfwpyWG0BL6zHrJReLQVInvIrML8lmbG3QU8Ve6smawKhdxZpBtP+fF/4xZk9+m/Pa3ZrJOTXS'
    'K1IsCD+EABbC/9LXFfPQof52dNTC6GjW8LaYdE7BjR8xvK7fg+MsSZ4+e3Z5dfX82+cvnl//jYK/PXv14tXbN8n1D5c/Xl6xh34P'
    'XjS+aYzn/UB2NHlGiGdb1jv+4S/4l8G5Pdmu17u/U4y83W21rL754pYMk5I9DPOLnzhYFzjvnmg2UEA5u+DfcI76RHxTwh/ry5x9'
    'e5IN4I/1ZV98WcEf8aXgzuwfhB0Mio75LO/Eh73Nn4XjqaYi6s9oX/ZEO4ANDn+ML/vyy5L+I76kEoxs96Q8Px+qZhUQzhMxvmx4'
    'TuFhuTKSdsxnb6gYhT7bH6l53/S1XbFWd3wzML40VpfOJXuCr8J2Ph6vV2LLjb1mshf/6iQt4I9qs1xoKzsgSzdJ9S/lCrBpDQfd'
    'PB90s/Oca5UcQ62ZKJkR64ODBajcBDPmUopp7IRNNxG2eLfRyHZ25RjkUn87hr+k5w8WYRbFqD6FMIz2yXbHcKkGeh206JVoyvua'
    '9xuYKZHFGqYp9gtOUmTvTK9NPOvMuA8K7m0Wc+607O825/0dQGJcFeco5YFydaNR/LDWm52o1BTchIegs1PYSdCusDXnbKe5P71w'
    'Q5vV450zOdHqPAfwvMh2tmPtCvugVYCgXD6+FeE1TyIc51n8GnO2C4WL9eG1ORrsXWeGLZsQfn3v6TpkE3XIZ7td0o6BeOnBUrVU'
    'L/gD5k7yepUOhxZmZptBUfxrbb3sfiNbo3rV+5LHCx54SHSuqCjTECWvqs28TL5O/lpul7+8JBmWJ2sYq1+OzCZZkflEyXwAX3tE'
    'yXyS51npESX7g3yUpyFRkmYTkn8HqUqw8omSxrP5yCdKVqPpZDLyiJJjcnJGI48oOayKajDyiJKj8iwNi5L9UTfLcsFwhkFR0ni2'
    'n3pFySobqX2xRMl8mKdq6S1R0lwFS5TMyixPRx5pkvQ5zFKPNFmMy/6oDEiTkAU07Hdhgg3SpCBJ4Qp1jiqjSXUK2YwaWpNipN0a'
    'm3LT20J4tN8epbP0LCg6OpTc1JWQGT84SLSw/AFxsX1PQk60u+oTtjbyi4luR2Iv+Elp6FiKiLawwBgKXvpF77PfieziNv/Qkk4M'
    'uc1DeY3jy5vHJyQ2ewkY24zoQl92zr0i+0QNeoInt10uIbR9aDsYIaehUCf6TCFEqPWolKz2oS1xCiHtkBfxkEtJ2C1noctkH7C6'
    'vBFSkGwsJP0cS3Wm+EP4fvLtYl8lj6v7KqmJ/DVfdZJfXtQh4+qNybgCZrMqK3KfuEMExCqf+CxnZT7sDz3iTp7m1SAk7oCnBgoS'
    '5XnKK+j5xR3z2XzoE3cmo+lolnrEnVFZGsYfQ9wp0iGU3MPFnfPx6Cws7hDRJesXceKO8WxA3MmzST7yWc7IV/2RR9wxV8G2nE2y'
    'Qe4znmVpNspHPnEnPU8no4C4Q0/MoJunaaO4o5Gliv4y9TpGlvLg8UlFNCikHrtBNvGYBrjg42iaZEtGIbnHIumANKL3xvfAvnfZ'
    'VvhFH/f8RHXmEX/SEVlwv/iDdCaz4NnJiehciECuGgo8Bg0zMrrtd1r0oktB8bQTkoQERTaOM48bp0ca4lw1ohu9bClnbi36xSUi'
    'zrYPWbqtLUK0GFNAMDInbQhGbQaHCUctSJcLSIe+65GRBOkfMKEHkZP0BoOWoiNp8vfrKn799OXlC+ow/vbt9fWrl8nV9d9eCIfx'
    '4+W+3iXjCkKEtuS+TJ5dXbGQiW6yWu+S/7gCSXG+uqk7vzcP8zVQWLKZT94RHqNBASbJaZll94wCexDdYddeCsZ9bKtNVe4eFzzk'
    'wxPSywNyPlq9iVAsIr7cVeN3812v3JDmtuVqIpO8nU94hSctlmUgMvPx8KokKhY4HAfEqneFErO9kbKJJ38Gh1wIBAU7YAI60CAL'
    'cnVTj/CY89isxEBUXOHdUi1fEEmdF1F86IdB5EOkK42LH9+VUYnG7kykqxi4KAMjYwWL8OvjGSvsSF5VtE5nNaXlCLfrhTyXj2ET'
    'k68ToC34H0tH6ejnFXDvk/aFOTBMe71JmeQoYu0jCw2pVqD6duKBE+170tC0d49gCo0HOI4P+MJwY4+WE1+J1WtMzEA/lHgKwb9c'
    'OFIcRStxl/KIw+i09SlPm6g1eXOzqJItFJgkVzR0TtZpxUp6ygNJH2KFHzBe1pwIlziXk5kpn+rkEqoS0bFYoBzZEwY3v54xHKkP'
    'RluifI31Gjt6R5093hKAPrl5cEFwRLr8TyeTqq7n4/livrsXuMGyqOf0nsmqtCdo+ZsvyECr1dRyknajn2ayMnK0XtAn9YB5t1Kj'
    'k6mX9qvlRQK1W/RPs4J8yndJjWpbTfeTqrdcwxn65ouMDOp/dRufkFUaI54UJRv1o+pUbSxX82Xp+Q4GzKuPPt5sq1m1rXlXU94X'
    'SF/we4d087+62vAepn9ryVjMKWFiC2BkbJ76tnMknVbvsJKuTmU4F2o8PetYTn73mkWGy+ngmy9YQVXSu+nO/2BF0sLht/fA1ySU'
    'cv65sonfbpLGRcc2uViva1D9wqOkSIT+JlmV3Ol86S63nrUHTmrzIuFfwTd1i0bFHnZjX5BpbCqD8LDpSOr5KsB/QgO5LevHX6FN'
    'dsylKgpnhCdMZNov3MKsF05BTwxMRm4nu3+wit8qNWDEgrWazkg4MVd/OM87jcghzvMWD4W5s1X1LIZMRtBfmyyIDkpovirfoRSK'
    'FEvHigyQM7Lb0kpdvdtFI//oFx08m9zOff3IbsK3z5N6UhJRBAwJOyIsVDtWU31Rgchek1/KXULkoT0Rv+6T+pYII+QduFHZdQni'
    '/RJEs8c8r5e2tFoDLv+K3HqrqpoCmVl3637eo/1+80W9BEaAoD7wEf5Ibob90v/+cmpa2brh58ZM/Gh46kYIKY50kQd5kt2Q8HJw'
    'wy5Dig73XY97q/I9FesaHlxJIAB7kP1Wg+Rm2XBvYJ6OWDlmAt+EHzKVsIhnuVwe8aTUmMPPWibHw9fOCofVGzpr05AdRdxEcuRg'
    'vIDT6j8Xi5u4c8GfazgX/Cn/uYhdNtZQq3PBX2k+F/xB/7kYtBpkw7lgDzWeC/ZYw7lgD8WdC+3ZhnOhPdl4LtizgXPRbu0C5+K8'
    'TUOhc9GK5LhvViSxabU1z4euUI0cjx1ccnw6OlJHMYp6nWbluauBis3kcP/nC//J/nkRd7L5cw0nmz/lP9mxG88aanWy+SvNJ5s/'
    '6D/ZRatBNpxs9lDjyWaPNZxs9lDcydaebTjZ2pONJ5s9GzjZ7dbOf7LzrE1DoZPdiuT8JztLB6GzKc+H72gP4173He281bqKccgW'
    'zcZcjd2KA1vNNxsivL+Yj7fl9p6ZFn89sfDk7M43GqSuXpOFWSK9fqII46CCGtndL8hzc7KS84m0WdK+DzCjjoQV1fDCtSmEjk7A'
    'HlZUCXDx/I4o1jccGK0hpR8zULdwD7i4PhiMBgIZZBk5NRBAvOS2yvg+k55MnBi0ZbjfQD2gqWlXDaJj4pBnqje83IOxCmf+EiRt'
    '9sLwtTSXc0MrRhiLAe1tttX7eXWnm9VxK/qxJdKd86gGQoG6jnZpmWDi/nXxr2nQgZ3jlWl9PincBRXlIjMWRkU9IT4lBkWOfIRY'
    'e8665wX85SFJVjzwNS1D8AbKXEwgt/7Xdg/syMyB3R3i1cpRfozt3gjbPSuiQO6QNqTm0oTSD7WDwqvbLfUq8OLs0pB6elZcmG2X'
    '78mdL7i2KOUy0t3qfZQKAXlJ5xIS3hPDkI5bywCch3+9aESGEaRhLiDI7yvyHgB2fYgpg+Zi72mrNV/N1jojM0FBjEdlYaum4mvD'
    'ELDtkcBONiXV+zEypiwOjljeog88qPfr+aTiq2pGabCH6PcAifoJohIO4ebG/WiiDhn1nqibqJCxBc6K67W00xQVUVCYPecScWAN'
    '9Tn35svyhny33y4efwEC/hP6wdf1+5uvfl4uun/oPyM/JuTHVf3Nl7e73ebJ11/f3d2d3vVP19ubr8nQUnj4S8YdvvkyS7/kvOGb'
    'L4df/qF/SVrYlLvbZPrNlz+mSbookmFS9Ib//BJgaBfffPmHvF+OymGZfvk1exqaIz994YR99VgwG0yE/6hfND3NMQHdUyZryWA6'
    'uXjQGpEYC0GJ0/n7+VTKsIdIbqMIyc0vHphVk3lk3cVBugE2L+WTFiz2yy85tG4m+X1mwdZZVcJEu1xj4pPxoiuaQg21GI80H8pf'
    'SbOJdE8n0z2EfuqigrybP4mfyXA8kk62pEsYgKvDIM6+844TEiEPYtCRN3JfxOET3SHu6lZjzNJDx1jEj9ES83iAavInIpNWRN//'
    'lWS+e4S+zcIfcUs/Ckfd9hXQWoJHOHE3SarOJOlyUm6nB15mkcUskA0bfeJgXEZdDl57MKKWwhl2NcQI+YkDeRgf/ueUYTR5q7sV'
    'Wq2pJHRZ8O9tdAtYR+S5QCStPQAZ13fgCHJzBDS7zjsMPe5PH4jU0+l7Bgy/09LJbDQbznKDzuJMTohugMQbeGnpo4il3y/Hq3K+'
    'SMrtjlwN7xJyuybimGqH++6mxLW5NvHW9H2fdqIF3BvXt7G2ZBgiNiyxrl8mARbFHy74kvetCxiwCUotLZefZ3WJyQ7Y7Y530Fcd'
    '5HYHFHgm1Pp4PGm1ivRRYyXZvhNNc9eg52GrmQu4TH1JyZg+7ZLSDj7ZkhLNkcjhi89CnKMwcfKhyNXE5jpM/XPt9/sXSGt86bDW'
    'Bqo1W9w8mUwmWmvwLpFWVruWSxV5ZC2pWxAaL8eemjcmR+wfqqpInIwMdq4GHFzQIj2OOo1+Akvdz48g0tV6vv0F2WfiYLTYqw0D'
    'DC9zgAlMB+Vo0G9egfD6Fn5SLooi3Hq920/n60/JWumX1f/H3rs3x5Fdd4L/81PcLYZEwI0qVBWeJJr0ggDYTYskMADYlGQ5NrKq'
    'slApVlWWMrMAQr10yBserz3SyNbDksfSjNYzY1sRo52ZnX3N7nh3I3a/SX8B6yPsPec+8j7zUVVkt2YsdTeAzJv3fc89z9+ZDvzE'
    'tS1S0VgTbiK2ZzEHdN4Qa4GukxuCG8C/dJ6CDbDqQeguchBEE9XOQKf6GZAEDTJAfWqDu6vRO7hV3Aq/bj2FnyMHmo9bVFotiB+B'
    'QiyzVNVgBAPbeFsNT8CGmXmL4yQqzJbVOc5SSr0Dj+7he/PeZz//0T2TBTTSQO7aoOJF+NFFLK8ShtvpdJwiktRqF0cQ7bdXpdW2'
    'PNUPvAZGXcx+FU1BWrLC1sCBBK6pdwO0YsElX0DiMvIiuCaDJIB0oc0kxCkl79+MjxP/u9CPK9AfPWxkCQN5kZIqpWQ9aRX0FH+Q'
    'pz5QvurRk69/CT9xzLboKHL3aVIQ24K2UqVYx2SpilxduEJ1kOotv7WTdxY7OQqmg7GgTqjSYNcJT1bMn4GdSTwoT5viyRdKjOlW'
    '9G5ICu38ZkzYk733xUSoljE+A1xwt4ZppkbStuxsHEHewSQMp4Qe3nj+eeN8sx18dxKAMSkBtY/UQJv5TnW1SgnHQJfTK2Dr6Vv4'
    'tGIXajbNIwxKm9CSnltKIWgNw15YehfRnxTXStfKixw5ZnYVQ09dtDHp3qZ0CrbxgVf5UJx/w9U/thk3jKct5YT6LyZHbb4787v/'
    '9t6B/76EG4zHuuxoE82sEPjrGJPO0dcb8J/1qud92xslo08HhIuaLC3TaBaxtP795l0ixfja3W979sPVukOEK4klVQZSkNJallMy'
    'Qi7lw7XrzBqk6Q7Xa2ncnIegYmpp4hihln9X42ZtQxhKW05DsVJvFvQUu64zu1x9g617O68v6iVWnFpOeOnophW23R0KcmXs/XGc'
    'hiuKtdcdk3jrizkhbWvSYVc1QbpS1RneEp4hSu8V57KUebTw2rghTCYDr5YOfKvLUplJ6YBWE48hUbqgHdkookQmf6z1Uers9RSQ'
    'gg1RO6bEUiuW/d19BfUBmCCjf9sgTu6U++qtF/j3afaArlBfaZD1PB290msW7HenTq5kt2xriIt7Dh8RKgc22eFHMy7mrIfktPQH'
    'GnYtC00+X35J2R2wqbGXUNoxbI74dDuDKD+QYDDiN3eTLk1SW2Dc1xxmdnNDs7Px/oie6z4dBIs01BKDbu19qXbjBU0NomAcX83Z'
    'UD9V9mNnx9NOQWXsGIzCLOpjTLfZ9faXCpES3JXmHBfWqMrBqAA4KILxqT0fQZ+3pGGYVZ0AwHdI811T2fHblxJb5wZFHnclr5pC'
    'B1Vf9aUVEDqPXjFXpt+jnYpZj7OpSB/IUnXSVSHYc5EdkIk79Fpopoos5saD8+tvLJXIMd/h5IxOaTrK3UrS966MGIyvmjPsRXM4'
    'Dvy+GoB7utMVBNrnccEPVW52GA7v7+u5D1T6qZgpHLoDo2tUZJauCHb/trdBD7GzzaA7q/dve3tra3fp/mXRrMgTq9QPQNvNPUog'
    'Bs3ZPJmNQ29Qhi3XquRcdSPig1CNknrP+cTmSThwTvhB5sV60vHWgisQrP0Wu2KlQOcU5r66pghyK2CenQm3dTFl1/JL47xqBegf'
    't3K13nJK6i8BGnZYMh2VFfIkfSxwrRX8a75AxQJgXo6no/do4m22wvp8HMrd8B5iFApk/lKQPZ1Z63o83RWn1wrRCNZUFEYllKJm'
    '5bfCs/gKOV2wTaTki+iDNmY9VJ3CVn+GDRcAcTIOTHuT5hwgesbl/vfnFCuW0ujcvqNvCPjhcbM3Mynv+IWJGiKQ1nw/nt0uIcTb'
    'YIDWWa4Yi1WCmafq7Muz0Ptx7+olgbeR8cx5W9UxZ4aodD6hMxqloZKIehpck/dkgJLNKztCM7ZseYwtK9f9uFwzzZPrpv45jVBV'
    'P9WsM359Y+GOcTsWE49uyWH7MebdsP441satj9LM5uYnrd48vTXq9iVH13bm8/k4i5i2haklAEf9CxP8rDiXT8ZcbxL6BYKdzkbn'
    'fmdja5cH+ZligOv8+j3QVeOB2RW65UdxUqkjMlFGvY5wAnIx72VjdW0YI8d8HLhlbsy4Oy2u12TZeQ842y754wq2mBL2XXX9lQKw'
    'dIUiBSps9Vqu4T+t3w9dj/o397fw2YSUxOr3ZXZahZJYdjaFmgiPb7dhwaP23Hez+m/tNWxdR2nUc5mK7+Qn9+zwoxPyydOTV+T5'
    '6fHJxRfj0N5BkNYYNNUE3bUn8UBed7BxZmQt6FHyRr4dxxO6nRKEOLsL2ukmfCClTscGFtt3j3Naie5aI5ezw9Kl6BKRJ0v7He52'
    'xveRfZTbG/DPNs+resfF7Lgzdt7xhTho1pmdvN1BEs+aw2icQe298TxZEw5rVeRGRmUc7gtv77Rm1/LKdzFw2u18xxk6UZBqks2K'
    'yd3eMQ4qpzhuTs6+Sovs2wLSXJ5DxMqhFOOeMlhnRLKj+wiK6B/dHl6ZvM4iHaCqwBGoxUUanrd0z18roovB/typRg39He8yScsm'
    'UDvG4rD0p21xAPwyEJ1bON1H6Nk7j+cpO9sAWziK6C/ATaORKQ1nlCfM4gSRgZleWp7vh42+rADgW66jBDASWQE0uWyUfTKJk7BJ'
    'WZ/ykvDXAIviHGvKIO26ZUO7oMNo9m4xx1I+OEgBwQOrgN9N4qA/cg4MIZxu4b8ahPE0HKsBNPnpBydN/I8IYpF2wje5N8vbyu3w'
    'q18x7lnDlO4pYOUzJsAYP6WIwKQIF6SbKBvh6uIeHcgJWXwe1MGi0XHVQ4X4TVjIcBrPr0ao5++Sw20cRUo+ALLPGCheRT8Y99f2'
    '7gN1/S1a8gNcFpMrU2GOOp3ulqUlNjS0+knTi6pERDHfmqUU2u8YpW65Nda0ZD6B7KZoeAnob4l9Rg5gEtlOxKPApg7ATKf0dg8A'
    'gizlJzd+w4DAyxdR+cS6kXgmHPvOc/JPnZ31DX4fYjC7zlztuK7grkH9OlQEp1R+h/6AXzst+ptyTnA7uNdd9jH6NtYknV7eKIRZ'
    '4YTdKpwX4Q0l6vwvQ5Ojm7Iz+6LkD10ucG6nJFMArr5Y0zmw+QZjJp274N4AHdFWW2PMttvVbzL7/lPvNp1j9lxqlUYj8FMs5pB5'
    'PfEeG5o9NpBK9YOe3t2A373MFy+R70OgdNxAqh16cXNxBvyjJACdAOmPotkXNLLZLTbcvWI9b2LPXey/Iqx1mLBm5B3uQqo/P3ve'
    '2dre6Ozvb+yBSL6942PPc8oAMLRCYC1XEmlSLm5HNUVYL9g/uFNsjNKX3Re/pGbWcQgFFoVk4zRMSYB0r8F7bAl4DwXuP52F4/ER'
    'XY2nU6Y+Y66vbgFDX77WVV86Hcox2x4AqvkNAcJYb5ip31UnxwtUA0VsRXrH/S1m2dC/vc9Mlxopabd2ZZBDzgRbdgB7R+3urOdQ'
    'Fa4O0HmYRGmaO+5LnbVSJSTi7Hbuo4c9SnTqUDvq9uTe6hVGzhs2dIqO5vZZ9ku7hkl6pU+6tsHF/tb7Qo+YuzJ6mq1b355OzFdZ'
    '5SRvrXukSl36vO9EuMlvmLXO7i6div2NTpeld13AsmDZ4v0yLFgcPJPjl1u1cXdZ9lCF9h9TdpMy5hfzK8qjQaMpqjiS8IuhGLqb'
    '5h1jwoCD3cwvPEmSVC9q4SVpBgcwR0tAGpCf+S9bh/FSptTVNhNvw++L7TbW2dzYW8fgW/EsnLqs9nZR1YG7lkpr32Zdt03+V0YL'
    '7itB7NURE2yG0tF/VM/40hZ13FZat8Obo3Lu12DsFDv0ThXDuC5KTmY0Rdq1mJOa06+gJJ2VBzujOF0gqsndcwCOzBuuN2k/mG7c'
    'aeUvmgHPlHunGtBKCcyK0+nFrUF0zrZ/B3tnfIEZUDLy7WgbY6cKOivPHeRrlcfV+NoWr+01KPY6L8QEc7SFSbk/reRzzvaWx9H8'
    'rdrT1MDRKnK97DhcGnZUX/08JtkRQ6q3i9tB15Z13JLZvq22tyNSije6SvRNX0HzhLoSiNo9Z2LiayqvUAkR+Gg6AnQa9loAIaXv'
    'umsS1Ko4u1Bc0xU4qzqrwnukTkLIPYcDDncZ1+pmoNsigG7ft8I2fqJaCwyxGIPX2HAe955Cd2u1wUmYpiwVs9tzr2xvMwbXPtap'
    'PcV+2INcoLMzDr510m1JyfbqU7Kur9pWMJuNrWPu3kr8C7dYoWPwegF7DQo2DubT/qhQvcQ90tuCQeF2bI/lT2V5traN274K67Tn'
    'sNTdV5mjJcx/FUyMQnUwaPfD/n49C6Dj6q2pf2NaD88aOa878bLIQFYE6l3vwhOtuXm/joYO3Nk3eL8dYzcU+AVXZ/ruF/B8alzA'
    'XmerHTi0nQ78Bs+YW6MgZf0khXPiYW7f3rFzymMQAiaW8B1Je8d2Wfr4Lm7a+zvrzkTzUk2vppjf6m/1t7dhfMCxsHR6TbS1Odvf'
    'KC7GBUm/ZY+OWOTIVBReHQS0XcfBOesTRJaJDqpk0c1xBXpBGqXy0VuzLjmFLedCiWhVYye+vSN7PKNXJSyl3cMN32IVTQRXFzxc'
    '2f/AzeWTpxcvD5+Ro9MXF08vLk9eHH2NPDv82sk5vPtKGM5SkSUWEvr1o2HUJ1kcj1N24sIBMyxC5rw+IPAAVh5L5zoIU1qApLcp'
    'QElAdavrOOgj8BzgBmg2OUyJ6ZXQ5Ky1Qb/z8vKKaYs3bJ8mnNYUYh8Kroaeif2d/e7eEHX5zFNm4040nc2zjTtM0bpxB4rKyFI3'
    'OQfvTHA9wAnbII/pqX/9POhf4N9P6CcbpHERXsUhefm0YVJ/y6KCB5R57Xxq56cm4iXDMG5yd6WNO79Lp4WSFPay8XvmaxyV+ZAr'
    'k42nYsRWC5wa0xOSacAoWjlmYbahZE1+nhdpxsNhGma5F5By27JP8oVdx3Vi6Xw2+E+w+oGIN2wqf969ib4dJAP2iMBf/PkwYlDS'
    'Y7rPFVWYcaewdtUdyFuWSZiU9vBPbAF/U5MW0T+HifiiRw9jM+vxvyC+swnnU7zNpk1KdCgnettMJ/zB1SgGZHbx5wCyU9KdMpH3'
    'rnkKnOPQj9i6bctsdZV5bfLt30rHfITDKBwPiDgO5nO2r6Zxtva7InI17L+ms934vXW7tNhasBQJeFxNB/xXvij+5bCG8VbrsUhx'
    '7O63723hp/o5ULqsPeAdF5Did8pQWss3OL0pTmd4vTwgcJWwfYrUmkOApBskCTK4drJRMOURLFN6J4UwJPShCQgOpYUK4JhVx88D'
    'z4f1qWLjjKZr22CA3WCuGJ12+/qGNDHGbN3yw6CXudg7svRIlNacaW5z/xKzD5CqjCdc4w4l0q5KjHCUtsr7K3+UZn839lG7wPOj'
    'pIs8ZzxPeGT0QO0ye7LNuXijwj5MjOJ45lao+BR7Nnixu8sssYdKHrq7ppTLdQmuzyWUhy+ThesjzGr/qY674o4kYKHeGplUXZOK'
    'z47vSBUjGRvNKZjOC7TGzueL4Dq6Aj87MqCHF9IO09KTSTAdgJU2Ra4qBfy9oA+SCwnYo4QeURIP8XfKM+DhbNGN06S1SDdRAw5J'
    'o/NdVRPHd151Wcl7H5RCQXsnKmeqPLOlDk+d+UJ0s25xo1jxXVExnf25VadPE2no/lR1ewUewFQGNMF007VM/9tMlaCm/NCmQqpY'
    'XcoSzQvivvNe3y4iFEY7njl3rrLLqlYktqpru1GlnBy4FMv36f/71VsRKpCKbSmDFy228X/iHL8Kx/Tchsah/dY8CjPCNw+Vl+ip'
    'voop4dcPsxSY2B2rsZyfugGnDPHYy6bCb2PaLN0H/K9peNOEK9VXMxJV5TNuudzQH6avRVbBQjgZoyo672nldrEwPhHsbD8LNiqU'
    'sa/YJY7z29U0WJcKVmpWWKVqdbDwGGt2wWKqWaCDWmADwxECVQOeB3GWOIBiPEXmNfcKh3iab805O+s4M/r+N55rpyF/59zyBUVg'
    'ngsL5CdEm2kn9NO616lYZFbyOLs/nbKgP8o/3PZiCO7GWOUkBJTFlAj5GmJUmVCEa4+ammB6HaSMbxiGTa5gRNoPX8VFenypqd9q'
    'G94dnd227a8g7iNFdye4/S9RZl/Ex2h6+l3dmV71imWoiuCrm42KDINeg9+WT4Wvaf/va8ZxxQfYnRrDwXp0nRLyzsEdKzzxLa4B'
    'y2Tp96qxI19VD5B6Ph/FJNHLD2i9VALcTEgTs6hwH6lhwrGYUbwhm70wuwnZRjCEnr1ioceBMOEKYCwMnTFWKddBGC+kikN/jDoC'
    'rtxgvthgBtZPUPugqlOHk5Or6+ohp4ajtHsMS2X7VVNtFogd27sGa8r/FmeaHnfE+3IcnK0iX32lQ5ZvuMiz5MmyRLtHCRPluDHL'
    'koTJU510VXlXcOBqc9Zyw0P3YmuTk1t+9yxnxx1u5hVVwm4MhEhe2fq/bYrrnmoNibG7p/voib9X5f5jZkp6f/vd59rknhJIWpgv'
    'meZ21PHPZHUtRD05ShGFRaMshrLCyqlQOu92xgtmFhgLudU0ND+m2yvodlu/4jy3fa5DqNr3KvPtvDs846R8K72msibTbNV21HFW'
    'ou/CXW0X7gpDJuNFBBokBgJioB3ZJBejOCPPohR/zzlFsC0FDH+glfaaw4QKrACN8JqDUtxaioXuvpV/dK9ePvgiWbHcg6ft8ODZ'
    '2nHyifXSeqP7l3MK0iyJEVe7HHJrd4f7Q2kVcR1Z6riTKt5I+p/a3aQrhgqZOn/H2O1l8yGVrqquEv1eih+0uBKxMJm8a5to453D'
    'bcWih/W8BPRANLle2uWEVcck4B6M10jgxVKy86c4CI0xskKAI2brMydOPmW1IUJtcxb1X9PNkWYItvpGEeCwJ/lpYr6oZZNk1V3j'
    'DHRhY+0BR2qcBiFg+gmpnnto38SfqkClqvkS3jGH92Ac5Fogs7m2YzqKiYtdfALR+T43XgeWLb0H7lJmekyFxjBUUK1dyP7RFG3n'
    'bSVGb/fA9GsxdoDGyHdFAG8hTP5bq0cO8MNciJyNavd6r6DXuRLBo4J0661FNxxdLdzEnb1ddQMj+eajAsSwT42scBrCYXHgSuFF'
    'anuN520KdxBLENepvaW+KUkyUGBrwNVxwbrXII1dY3+j0dJJGbVhimwZ+tNSEGBngIcMX4HKuEADyD4GTcxXdJ9n90MqJj60IipL'
    '2cJO24WguG1VOeqqiNs6tdqzSs+Uwgy8vn1QNTyAnwfpJ20z8ubocrKMKixguR4QkagBKmPpkSueKp4WGVpqDqNsg5+v7g54HcAZ'
    'W9emjrUgfAJL76yig6Ud14Mqdj6t9dGWBoretgMau05Lt6yGOZN8WjVPoqUBUN0DqiZfUltmDj0kf8AVH8oTqRLDZ0L5LD9jD7wc'
    'p8aI3S8SNmqwmRXkVuecM61YNB2FSZQJ4sIGYKhxcrZrHMzSEFcAfzPms7WTzyirKBtVus8ZvTP9jYujJJQ21LnPBuq9s1uDMZLK'
    'OdGrLJYHWEQY5XLBti+CxD1adVUHAeUO7GVlLVGeKZo1Z3E8NlxTdnEsrqOh0hs3h1i3fUvNWZF0baO4tJ8zBR1JtKj4KO4KNX7B'
    'fTPY17OGnK0yEhwb0G8bqS9r6bnXXJKXmCdmHqS3c5N++7Bx8tXLqhFUcqbdPLJGFgfBbSll75aQdhdEcV69J+qqZJWMHVY00Z57'
    'EZrmMYHqku90TZbroNadsKMPDp3zlTyDubbflzzC9LhtdvMaOX6l7JCqKnYgR4hRdLnRjy+jdxWNNKqwTmxn6ATFQIjg13ASXyUh'
    '4jeIqdzTBVuhPfIu1pb7fjEbeATWqimju8rDSJkXJuQIqAUgIkqjliQI9DuahCyhjkVtjEUVJQ1rARZ2UyaUtO+zNL1tF3k6gDZg'
    'fVzgH2LwYRpO+6GJFwJfbhd+GVxTMpHIWxXvDpGud1vuCTHhgHOqDYn5YGsVW1PJKAsHuwBwKn2DqIo8Dp0Pp4LRL45YJk/Tw0aS'
    'jU0oMxVbdqPKx8yFk8GgETWjYjb2CPN1e8RAsEX6n43Fvhc5fRb8XMviYwoLMgeTEHfZWjE8eFpig7TXPcE/+3nsjy2de25fIJu2'
    'NE4M8RBPriukxyr4qT/huHop5gmaNMnRyAivSoqsKOc0fKOBe59l9hKHtSMPq1HHI/KArgHTTK1NP9heV4aXByy1+mkz46ivur6F'
    'DrL/+pZnf2zuYC9zH5CDetei7ghyv+1IXWZiyO+VxodXkOsqBWbAHEhkQg0+zgUeZ3Z7y4C+hzXd2i5EmbOA84wERLqzCaz2lpF3'
    'TWDkcSM+nYBNsIqQw4SeXN2Oz8Zn8jLFKqxhQjr7bZVFzpkCkSMJdw7HBzFkZJcEoKu4iqobdfSM4t2uPusIe+rIBiFq6TOFqTFU'
    '9b6owKyxbskcO7BEHuwD0aLkWU2NpjoUcV/TjyD7+0I6kG1+3H1Lo8cWKK0ZMmCx6vHu3t6e+rFTz82/0lvpUQ6I/o6jlzukYFL2'
    'S8Rac6Fbe/kkBmMqnuY3TB6C7xb0zKnygBA4FxkXpVvvDA01dakLJ0BMlCrLtHacp0OfUMtxrmz7qpVw8UIXJiy0IV+qRX5YXUoR'
    'a4jVtCT389lQVCRVzqN7y5i7y9pC23aDbNcq+hL7drm7s7NzYIOAO7Q2WtUD3VXYmbMJihuILewEunL9seLgd5pm4czFtqjvC20t'
    'tBzMXj1CpO9tKTZrdWEcEMhCg2EzCREffmFNZnWtpdYFoYLUHiq6Su25dOeyOiw1meYLQ6OpRdl4Ke37N5W7tZr5YFy2392Fbb9K'
    'xW6nPK/xd1vhartSQ9ZhZmgVFq1Y7yJsUdVzWTtMvPooKth4jWGrfoCwBiyVqd/Rwty6rRsIwvzU7blgwgwAfIFl8TUOu+Z5rzL5'
    'QQYURc2QazOnKFiogkIhagMry2Vcr4FRT8VrQmWzenLhE0eKKBIPGzBUHKmJUb5R7RMmg8NSVfvgbu5ob82tc/hQJQtpLqp3vXDR'
    'HBW/xQhjpTPSv6WKe5zLH97t0VMfAK+C/wqp5oIVDpo8ENrhcb+lAzKsu9FC8kPhdcoq274exzjrZGhfilu72+1aC4eeedIhj45p'
    'lgEYO130gR4nlicLgiufLg0LdEnHuS2zNK7GB8A41gR9v1xtodgr5M4VMFUEtL8tQpmV1gVQhvqMowaoj3y3aw2sggLUfuPadI/Z'
    'GR1mFHVZS4yYHXvwORSTMQUSGsCaiEoAAWV9c/aM87+gIMhEn9xMuH+fkLfGd3eI19mtdEOxsBOlvoGnvm61+szqEqCjcK0zDzrG'
    '7BexVM6vkRiLtGaeOjTKyek3JQOAyc/wIhghBwCG/FkaZvOZLFfkKDaWztV1wnQXD8aGWWBZjqBXlHplftQvUfJBTs+r7Fr+LXOA'
    '421Jt+rafC+nvLn7M5J1wmPdXiPKUQSkGBCOAmSEedYUek4ZgcbMMSSLX4dTFjh3l10NrA4Z7lgOMk0HNgwB6mcZIg5O9fGMUoUN'
    '/ns8houh+jn1UzZrGcAnHeMFeWaEqvSTf4u6Iegc6yqdV7D+Mlmjak31esuayJnUlU8JxkzSO4Zj84gW8z9n2Ho9EBr63SyFz7ic'
    'vqFFA0BIp/NFSpmDcahFnRQd/AoXXPkV4ijhil2o3KmSYJf+DGiu4rnnJ/TOhK65v4BcKhAaa3VPc6jwWMaBMjqIgioDJuB5jUIg'
    'AwHw0U0n5F1HgbyTBEAki9RiZayMmKrY7A6sfavX+ggwgjR5l6UTNmIVidTOOHJfKtUpJ4bXJFDiZfZHk7Ezw8R4U/z3gugyV6xs'
    'QXf8Fj/jAw6apHtainKMQkbTYeyvC/IlNmegXGJ/s72CcI9hYk/w1rZjITVJzTXt7r2z59w6bJF1pWSJSMRB08RvLNAeRCUNOI0Q'
    'd0y+GKQdC444UWAttbO5uhCb+Yq6AakUM5Q0v/oRjhzeN+7iKqKRQI5UQ9nBg2JdrLYbIE6g4MqTyA0n8m8luZtcTuRcknk/mye0'
    'K8A4SFFxQk8B6YUcEqFFLkdRCgp6zJOqo4vQYtMwyEbQDEA2UBYonpAsAliFKxJDxqGw/zpMkD+CR4M5QIkhnRqHSQDc7SxgxV1I'
    'JXbCH2Mhhbe+O50d2wL6KyVJxPXIIVwWfKrZa12fF+adU1WghQnbvMANOhNxtQDEgyOhqKOMyOtdpWyeh9ZcGXqX8ZxB7FeWEag+'
    'qsxGBewYBp1RCSzDPzXeoUwiejTH4RS7LVMlWdKursizcYBcyr53s8C8UEmfKw2s9gqDfgvUsxu58o39qrD76gPx+yzPP2FNCE//'
    '90WeDgn4CGwQveqU4TM5msHhr/wEutT11k4kpMperDbx8vo4Cmhn0AdrFswoq8HvjxZkHGKoc6h8piJuAklgb4JbibKD2toD8vIp'
    'XhphCtcHWiGN2yVgmZHgIbaxQaahQJthjVL5OhwPGeaM4irmOnz6e8VZzllYfd1Kb6f818WTWP4G7WW92+OIMjECQVJAY/jnUpks'
    'ezpcJEOF6ecJZ59SBlrNuYsZwzNgQyjXgFuL/hpPx7e4E7KbmNk5ZFJaSmLo5mjVyULr3gY1E8/aq12Qv7XSihcleWXH8Ek0nmxe'
    'fiLUTpMwS6I+ZeKiJInZSaF83yhOogzTfZKz4yeEdofeofT4hG+ouDq+tc4PGzfDn3jYoMRnogyX+aP6i2fXRmEHOvUq85xqbBk+'
    'e1tvMHzJUZZG3WDj92qNz/G9ikfBMr9ts85q7hnbDOxv2c6SD7wlWEzdCsZT3oThKIUrQZYY3NJd93SsbYdmLNtV6RG9RG+VOmww'
    'ky6kYLJnd6WbSbhlLzGGvIpcXuYj6MAIxKMkhy4TuaWW7vS7PAQra6Xili9oZQWrtLJWxGgGc8r3ik+YPn8Vi7FQtRbhXfpG0OIN'
    'lph2ox77hGCOcfOMdJc8IHmy0SW6rlbinmA3SdUH2LYG13ZChzvJGrI6aOzDbC9cnoCU80wlNQbehuveGSu0QUBjRWUN+h9U44YD'
    'rp4ahSBwUJln0EQmUuM1kZmbMW8r5IvMRDOaVxB64nCd/3qJorOwIocfJagEK1dxZUAhWn5ZRvSBX3XlfG1FKhgFcuVoBHmh9+hW'
    'xl9xU5dqtFwykWOwsC1TVM4H9Lek2A3NNVkyD3vhOsFWO6br3w+bwQ0Ir1SWwGMCkWjgRwPayzSNetGYCk8EbT+cgx4ytZP0nbKy'
    'lfOjzgIZpB9zLgBxAGhCFNdj/BVkpa+tNTu77S+psAH3Mb6u0LfKTjTlCWdnfpy77Tbmttykt7Mbu/GtPlBpg3d3WYu3ypUUdI4P'
    '1WncnDLUelACSV8qBjpLgusgGqN/BLguMQRfMKGDohoV3Fwt0AsR45cSWgSyD+i5fwPrCn5QDLkMzgkuFTMuyDGgcYE+CKZTOn99'
    '0C/SB1Lua6JNHIqw44Y2F/msJ/+u4GNHG00Y1XED0GifCF20ftxyFbb/GGpaZKlbbpo1mTY70z6Lsj/4Tgv4eN1o7fC6cxi/TZ02'
    '6Ep5amWWbHTDncoKnfl70jeNn/sHQspHhRFM6yibjGFiAZ9mFt/QjfBbG8Tx8MGDXki3Z+h5GQyFwYz1qtkLR3RPwsHBUCx9CHYV'
    'pv7PUULYs1wv77IcPMy/wFnAniNXGzcM6VqqDt+JztE1NlWT4niv6ohcn8NCg4rP+ZKrlCzHTY5xpAWvdS2HEUeNONngGSWc5dxd'
    'Qv2txEJTCJw/nxynT5zGPaMnD9iJ+Jv0EKXoFAT8R5SQ4Xw8ztG0j0+fbyBNOxpRFiWaTwBNmwB9YvYxRubg8hE6rjh5TSl2wtsD'
    'miOUYymhe2AMEfXI0AB3BEQMusppnxws9I7H3mrMH2NrkLCHg3VuZeRWcZZLC4l2blMk4ngCNEMCaX76PBqIx6Zt5wZWT+vM6X7D'
    'WwCzUrEkDRYtwDlyUATX+AQ9gUW1TjqvWLjq5jPSYmvN3fD5jGiZxHSMD7pVBs3ZPJmNGf61N6eYSxMI5ehgr+CCpjO+dr89CK82'
    '2C7vbN3fuN/d6G7vbrTa99c3NBXj1v6X1h3GeyNxYNG4dFxmnZqXaixZMkEx+1k874+kQ67+1EgIZ75ugUyAnk/Gc5nkzHguPQV4'
    'xm/jtcx0ZjyXe8qucOrOhLJtMsdvneP93SCJAmbc/70HGHpVt8uULnjeAIQf8+Omqzah25gB4KrWa7OXqvMPlW2GdOczd7EgpWOa'
    '0EuRHXKe/ZAIHzUHjH1ra59ydNKb1lViZ4d7LPC1F0FOAtspj5IytkHuhiWwh5mnRR6vTyleP+RyA+VcpeC1QGMbho6aqHU3gwE4'
    'A+Vod6J+I+8gKc5sSGqkJVTISZ5o/GO66zAJhsFXFZgFiEa78MLVbt/8rnWGIR6hVfYScj5UbVKaBE+HwwhcXcnFayS5SAUpcU7p'
    'UgGHfkswYGOItj10VdtgoXxcrEIJGKKGWNIbmBReE6OkLfIqSKaUwd0M0bpBRXoe2ZBfgsgnCEwEWhe2SatuyeyeBRl6XK9G9JU8'
    'LO4iaTiLAs+reJghVAjXnHCh7IHvnlB9BF2FcudB1a/aWVJJKRqji6CzFDI363leT56Nk7sW5gRafZrOe5Mo+9xGJLra4vloNmTy'
    'S+WJmgSzmT/mN4HyhKfHVD5NeuIPjxunNsYq0R0F5RUViKn/0AYpU/MYQ5XPXQOWL41ha3l+XJXlU5AjARdOA99Hpk9z0hN8cyTj'
    'b+nBbXW66YY2VfyRZLHxb15F1S4UgmzelW4FqA1qpjdRJq9r6QR9FyaJSvBUDmI0JX8zGTOvSglHZQbAU5YBXwEyGaU5GzzWgJFh'
    'zl9BWAX/nYUhgPV82qeiSGb9TfsFfwYxve6vmh3662B8RYWTcZQCINNswwoc6QXTaZi02I8msAYkG2j2eU6bZuOHjWkcJXnEIjMS'
    's3SldkCMfwO/rVQ74gqouVCLHa51GkLeLjCCqtWLAEbu08JczcknsFZCDfWA+5tcMe2fpi2+Gt/ORqm4Z4S8hf4sLAAv37IEQ5JJ'
    'kPGr8FU0HYD2mmuM6B0WjHm6Nk3xBIG64EfatRJ6SJiwa5kCwZ3evW4ae5nU3MpyrmYK6OrYNCw5PesLneIweK0jrYgwelEkd6VQ'
    'Eqvvmi3uGoCm912IC011bhQUGGV2iiB6S4mItR/vxrNwCkBY9FZNmWTBHo0jOospe6YEKHfMmeRPvGhPbqQQ1UtSQQpWUZkxezPr'
    'VUJ3l6YlL4qQR1w2E8oK9l3HhCri4ftv85ZAkAZphMffaFBtJgCDir+wZ68aa00DgCnCAzB7YB6Dwi6op4I591NBIWNd0w4bImmx'
    '6H0ZDl0VZ2HPAE/xZpRxI2KKEGfNfUZALai7RCTddU6JgXhpoTews9XpetZVCWhwASMSGxnRUYMVaaNWZRwwG2vPcUKVZoRKx0Qg'
    '0wvYJjYFqUSrSYVVhtjwHZ0IiQAA/avmmKFgKd91tnKAEe+cMQhs1bOp09pxY9TtdnOIOvuYew72MBG4Ce7japwOWp1xANsm2oX3'
    'RIoDg2PPkeecp5SlmOkw4fHDTdTdPbrz4X/VbJLD2Yygu+xn3/kxCIL0Fr0lJ8B0NTHEkVmAmd1X3KJZkL7GQGf4rtmkNaERLgkp'
    'nwDPGoSJLqi52pxNrxoEZj992NjpdN/QfxtklITDh43NYXANH7SgjFZNStmLrE+ZC7u+N032zKiC/odWQQirJBpQOTN8Az6ZuPrw'
    'sMGqpizhOA4GDToq2g5MRYMgn8MqHGXZLH2wuQmfpa2rOL6ie20WpZTzmWz207T724wyPHyG1T+4ocv2X2+12wdgPN+h/+6221/m'
    'm/5hehPMYGCb4ElPfyJck+nniPc3lApIf0zld9orxVwmBnqXh6SBfqXx6AK01VksbG3s3YebAa1lEF3j8FUTW0OtmdnE6GygNgVU'
    'APOUzgYq0eiZpTNE91sW8kcB3YVRn+tSHn24SatXGhmE6WsQkpDppHtC1AOKhocNrlC4wX0jeTy2TFAD75RZSRPQbBsknnKKTD+e'
    'ylKXvNAxLbOGcTLrUHTQG/cpQ/BalmOb9RAP2to9eq6jCd2D99axddp+NLnyts82WJr0jS1Kr7HsYUPUgGTaV8U0mISwTDgBcLbO'
    'kngIJth4CjoblHdu6MVCjzA9kLQmnBQ2uyWzo80jLcvxLI3ibNLh/Ivjw/UL2go9j6Z0XtKQ635gJgunEYuzafzy3Tfddmf74MNN'
    'VvEqeoOrRHuD+iZwmq/cMWV9oWM7h526HSOoAS7q3hEUsDuUhN+a084esxqx0Brvxl5nR+uGOD7sxx11mTWLZkM7XNgxpnAQp5a5'
    'avHu4Rt+QpUOj8NB79asBXdRg5lvoBrlEncg/Jo8M39snWAZOSj2pGP/svb78eyWF6LFRl3HQFkXH10E1xDzBlZkXBp6Un6bEtKu'
    '/Hjm+JZDvDQefS2eJ8IWSEb0AptPU1rhgPALskWw/imlS5SMoq3wFj6B+zxlJr/Wh5sz2ZhJ8HhzjHg+kgdXOcNFs8DTb+QToW9O'
    'rnYy96LccX1wjxmbG+4In+q7vmrV6tDopkAcC34e8oPHnh9OB9gkbx5bxoNxE2UjdBagFBOoWpV+EK75KuoPrJvVGXjo6AkuKmgO'
    'sLxBASR1NU4h8EGf/fmf0X/Iq5NnR6fPT8jF0fnJyQvxFHgcrdjJi+OiovA/tfj508ePT7Uicj8lUa9HBywPVP4MtE2p4zzlb7kW'
    'vyE4iikQqVFMLx425cpsoQLuHL+8DHpr96AU0MqP6U/PjlXaQWMY5xrUtoDtaBS2AyWgnRP6U2nH21KuOKRndzBnjqZam+pzf7t5'
    'KWj9TP61mj6k2XwQxY2SOWaloP0L/K10nsWyaW2BAjPFHhS1JUpBa+f898XaA560fP9AKWgLlHeLtcP0mmVzyEpBS0/xt8XaYq5p'
    'ZW2xUrhb3xht1WptFI5nFU4gLYUnkP60WwIy4FSiCwYARPaZzp68krF8UF7eLTnpxU7KWmkDjP9Uz1GYyVqe00rW7vEy0NNXgl3V'
    'Cbu/fvdRtZrwn1XjBjHot4Nkcj6lgS/pa6DBHwORZroGoLyexWQFvATVuQ2u1DnWXjQjsAoor637L+mRpEe30HiszA2oNV+EN2eM'
    'bXmF4dtwq2miBv0M5ZNHv/7Fj/6Qyw5mAdwRjUcv4HCyAtaiFfaI6f3BAW7AesVtK0pfQYZmOWoLe/jfFffwlNa9WBe1STsPgTNl'
    '3UmfAzNKO4UbA7TfCb7lQ0j9nf3zPyvuLGtlBTOKHI01o/C0fEZ/+H8XdxI4oCVnNO/IYbpsV8hh6u2NRvasI8QreRKNQ50+esny'
    'FWdU4MQ2RxA3iltAuOo1yw+skIuEWlo/weoXPVD6aa/tuQ3RPkzYD7EFlEg/jShe0heUZ4AXlAwSFIKoyJkl4w865hLQGgdxJnur'
    'qHDvDraD/e2tAxBJ8qV5dAHVko/DYJDrG1y7o9YY5r0Rq9A5EPnWHE23xmj62739vcAajax7RUMJHJcUG0Yg7iVtCFs1hjBsh2G4'
    'bw7hkN9w/nOqn42V7r48/NExYvnSHPR2jUHv9O73BjvmoI9E1StaNhk55xiGeGeOYqfGKPaD3vZg2xzFMa95RYPQQ9UcI9EKmMPZ'
    'rTGcXvv+0B7OmVr957QhlZg3xwTkb83R79UijPtb2xYpuZR1r2pPqoGUymgAPCnJjulbsX/sm7U2WYfqyIr34zSmXIprGfCFuQL7'
    'Ncaw1Qu29q0VeAHVLrfvyHCCHswp/pJdO9WbjSUuB+Zi4bkf2Mt7tVbz/s5wZ+i4E8hjqGtFK0lnZtAE7thJ5sXLWh2/39sLbRJy'
    'ROsiJZx8LXIQOFkK+ngFnb0Mrla522aorV/xfvPstNXssVWxfxlYMKUt28kD6kVqdd/NQVxAjZTi8RqrL2QlUeOECwrLiRt0oVDU'
    'KNkU71/+MO6iFyFYz9aW31O0IrLkvjK6djId1O3a/r7FY9NaSvq1yCahNZZtEN497nQhrUNuFZIcjOoGgvY4FbEWH6xE3WRvWk2T'
    '8iSaDs4Z7OVaftfDU/LlYDI7IPwlWcP7/+MC9cCP/2mxesCudBG9Rcl4cnXix3PQyYcZ6DDTe95+f/aX/6y421wNSi7jeJyuQHd1'
    'yoBKYbb5Vsh9F9H9r6Cnf/8f/7RMv4aVL6eCueCT5tv27FdUtm6OWFS40LbmathLaUNCbxWYQYbqQDjmNAmn8fxqhIGWdCiYIpRc'
    'MOc98lGsxFWWqnEL7VUeVS7SbvZhDYXR560f0hQ7q1ETfX7qoVyvsyoV0fvTD/2XoRD6DdUA/eei8tF0NavS/LS++Eqf32wtj1g9'
    'TVuzEt3P+1L5vGcdz7sU1hAfGJA/0ndhvK3KPS/HNK+U6fy8mUvORpdzliwiH9bPyV+enZ8evzy6fHr6oqqxv5av0WIOAKo8D9E2'
    'eaoCzFRQUWKDbtA9e3U15ioGfICIH+BGrh5dVgqEnrV7UOAM3t8rEtJ+WLzGzwDrC2tZSDgr6DoijBV0/Rm893f9bkm/AWfgxRxi'
    'nFfZ8zScsdhRX89pAeSiiyTM7/y4xG4ezlqE1bLCrseTiMe9mrSAvsDWhOOEr98///MSekArImUyRN1u3wSUXZwEyWuj16/E85Je'
    '//oXP/zbEoFe1LQcIcs1DaSQpi1LQxa6mCBnJaSsLJqn7/91ybYUeS9XcP8cUSqLfBAaPCDAo6hnPy3xIpK1rWoFV7V2i0zNJY8q'
    '+4i+CpPbwhX7ZfG8iKqWVVMx18PL+OJ2Gs/SKF3GJ03UwRmiM6h5uWU7gqCJKhxEfp1bHMTiPAL3Bfbtj5JtUXVTmGrM/igczMdh'
    'wSXzk39dsg68Cv/cL9a1vjiLBX373l8sfZ4X61wSggax6G7+ScllcRENwpRskuPT02NP7/iWq0RiCmnLykiKMQsc+6hgFv7kuyU3'
    'PauBn+HHYZAtxqkwRORmds2VtcWq+yQqYqsuPynjquD7BdbsOLwOx/Fsgr6fyy7aoqcqhrxd8yi7LVi1n/6bkmMlK1n1uRpQroDS'
    'zblbXyM7+Ec/Le7gsVLNqrv4niw/RRvpIsz4iVEYRDt0LJdpz08+eXpRXaJtuANH3inrkvtYs9YwVsGSjURICjr8FwgYf1qqc7hM'
    'AiqQHrEgvhUwosdJMMyqyxJlHBdWR44AhWAFnfs4wsRRpb0qc1zn9aygR9Z9yta16FT98R+VBCkEk3BAcOKWVCU5Ap/eK/cOO0j0'
    'Ye1eMBh4Z0XIdAyu4u52PxjutKlk90HxVB0OBuGy2j+9kywatmI/XfghjUe/X3LpYAur7TWoMqrO7XB7e2tr96Ci+iJb9fyOwyAp'
    'urJLGK0j+J48X1o5ATUQ1KhVEZTEsXYqWs9Pzk7PLy8WvJOQ/36P4VSojjrHZgul1u+WSUtgZ2f1rEL9MQqSiyzIY5X8Hfsnpccr'
    'aRGsa/XkfXlBQRp8yWHSX9YNhWGdsEVIP08VzfvWXlXrWU90hoWvVtj0JXtLjq5s41daPllbNQqEi+wkQJ88PXm1EPXB0Ob3s0sY'
    '23vBUi8UcLw/raBuoDUstjMEbw5WXojj1fw7WA8v5asS1vx7vyxnzWVdy3U3TyNjdRezEhX3lPLo/67EhAqVLNdFFbXUXnV4yRB+'
    'Cib0Vz8vWXmoZbleDoCn5hjbHP3a6izy3SivfMJKKHbri1F8A1A8I5HaACskkjuAmucJAdgnrzrtx2Uhtdcl0lIl2vIMUxN8nleC'
    'lmDnDOhNwdr/s/+nhM9XK3uH5vV3rBMYUKbTPMfgWwJo3Wv34O09l9PrznaB0+uvf/G9Ei3NcRGzXKnfCFDu7zi+rt/zz/7iO6Uk'
    '9BlUveSCQycrL7ji9YogEwa22Kp2AgIFs5wK6pQOL8LsKbxiQBD4XvUHZbDRWcychxkWIWCpYa6RhGTwI0s3yDCiImbSHCZROB2M'
    'b8nLp/7t84MSdQQ2tdz+YaOdxHMdscgYLb53jpbjGeXjTTMqcgfJgOA3m69Dlku8cJw/+Z9KdxtvZ7n9hiMiMKQqfB0Cczvdw09P'
    'ny0mU+rOXO+e0teVkSif/b33Yk35Ihhsq3VvGt5cgEISd3EhK/erkr7JWpYULaGeMrcNh0caJM5z7eanz0FHstB25rhI73Q/a2Ak'
    'PCnREPD2g0hlZweUUQarV4tSWe5u+fj26WDtnijLKN299RZ+UMDw/Ow/FK8jA3ciLVHxCjBW+LBmg2GVEdFiTf5FxTHRg/PXlQZ1'
    'dvxkdcO5iZNBlfFAufoD+ueVBvQqTgarG9Fw8KbSlhu8qT2e7/+LSuN5cvzVFS4QCsCDeZhVWiZZuuqoXh2X2yjD5JjWuOS1PrEh'
    '0NxXOhu4kwyefHVhMsgh294fGWQNGvQCch4zbRo9xeW62pKbdDWUgHfUoATsKRzNZU44fE/WWnS/vllf8o5nHXrCCfoSd8OT1d0J'
    'fOp0ksM7evzVZUjJkwhgnVGZsty5c0EPvj9NBmYtZHr20+m40PfwJ+UKwTPMgciqW8HqYeeajg4fjscr6SmtZ1kH0mhaiWayPeek'
    'mR+fPDtbiGIi7OR7NKxxhP4yE9Zn3/tlqVsxq2g5obs/jueDZno77ZvGGnhBhZh+Of3+gxJ7SNB/PZ+RJ/F4sKyOm+VbNnuKD0u7'
    '+YO/LnPzgmriJMjCFZy6JMSUT7dNwD5MQht4Ed8e4cuiXv/sr0pPoaiMsNpW0nl2qSdxj7JdtiAPTyvYyf5VWb/xNAeE17gcEQFA'
    'WC5r1wq8h88MugEvLj4+vSTPnl4sxoZRBiiD3CWfZ/yTsmwXz1rBYACBCIqZAvBHMO0rgd76lvHv/+67pWCpBGpeku+hXWQc8ZMk'
    'nkg4T9HXj0I6LZCaDLqaItYBy1DGAnOWlTWXuWuNSX6Mie3An3tCe6zoKQ8HA8IekjTMKD1kKfAWV+IcscouoLKVdh2S8pkdB6yJ'
    '6S3BfH1lHf/LvywjtKyy5/HSkKtGx0Mt7Bs6Do8Iy/RW1u1/+n8Vd/s5VFUMNFYNCWcweFcxTovFSaZjnsgvm0okZ4Tb5c+RkGlz'
    'TjcwIJiDTSfNlBmHKCfC3AV8xpx/X2bJWSxOSh2E3ntUc3q6j++U/j9G88AmSaV+tHg0P/mbEs6nUMW60HBECItnREqES451wh4V'
    'DoWSyn+8ZOBL5ROrmPsvgyuBOA2JSNE9gKXZ4H1XE1kC7SdZcHXlQDqRS/Jv/pcSO1Vwxa0uy5xhA7//8z/E+gxzrhiSq0lUb9U5'
    'YZP5JvD8a965/O6/pf+UMs1QxfKbAjHcMe6Yrq6j0xmZirdswhYMcJZtrKbLzyH/3bOolwQYcig6jI/JmD0vELH/ruzKodUsGeU3'
    'TyET2bfDL/B2ZWL90cUnygwyhQ4785gFMEgJLbG4Vx6vkNax/MqHQrdZ0mFaYnG1J6+wSPu5AtWYKgsJqUVXsGj+hVq+CJaSx3pt'
    '5/25PHx8QR4fnjtT+WRBD12h1LwUkMMHWwkixrPJHBZ8gaDQlF6HtKABhehJBqFKPdwjlkHxXa5zIUdMriu/0fPDpy/Is8Ovnb68'
    'dI4h7SE4Cmbyq5gjDM7PPj0/IiHlDiRw3aX/gV+6e5C/syAna7Vslyxl7IiSu9cP2gcyOS5UHb+B1J7QsKzqzYGSBV3kvAUYRdJu'
    'dXdSBZFRjnuMDmQsbwjO1zMonjLvS5mLDrIDgT8Gd6YjiGZ3MwqnsmSUElTtzCCTJhO11ZXmxZq8QpZChm90lthUe+N1JxWb4Jx3'
    '7EVwHV0F9FdMO/fkZKtzIH7m+0EbGq9L9FGuP3uspp1S+w2Yaoq+8MPR1iPZ9Ieb9C8j2Zf6rUB2KB3UEZ9AIjuDbrLOVF6OPqb9'
    'JAY6Z2xfTE/szk7cyLE58aj8+Dv0H3J2cv788MXJi0tycYK4Mhf8zTv9J9cGC/0NO+NCbaMTRzlmNiDC0J75Qeb5TsRLz31oVCGW'
    'OF8mlKSCjGcEkcut4FUa+ZPlQgIkNPiPihMhxsIBVLT7Sr06zC45ogOrfipyCap6kbJvqXxwnTCglv/T/KTgojKbhlyvNj4krg2M'
    'vzkNrpuaas1RpSyI+i3K9MV88shtmNngbAUwWgYGLewsGZuRLrK7ABZw6b2lkYCLkCfzNGu/V77V8jgTDBA1bRrlu+vXv/j+/7jY'
    '3sqn8Yuyv2Dymhmbh0W2WD/fGBW2mV4ftj0Mg2xOLzFASS/GB5TFHcyPFSQlgfQ4hh6gc4BKbz7NUkz6OAsTYEoArQp+zwfC+GoR'
    'JlUBLa+oX14HQNE/FqMsGydB0k9JNEUXeti3V6ABHhD+IUZR8fCoetB4jjON2ZERr2uhMw3ml2XPNPM9PET9G9PlYLX3Kt4X+Qjq'
    'H2EZxVfzCOdtfh5HuGxNET2R9m6wyJIihOOyS4qiCFREO1H13pe9XmAZ//liyyib/MJc9GL+ZxAzg0rLeseZ84SHx8fN49Ojl881'
    'bnRtFA0GdKYp+YvGJIDY8A0COlcqLcc3+QKsEx9rKTx7F2Eu+bdyaznFRXPDuXhyh0g5i7nwloTjAOiIPxFCRXKkuUJ79i/H68/D'
    'OdrGlpbzBSCUcWLebJW29h/ae7MiC8sbr/x90e52XeL6BQhLzDuQhGAtMy7C8Br8Gan0OaPX4SygIgGwbusHae8ong6jZHIcjsMs'
    'RGbO3Cv3VAEWLXFyZodJPFGkWbFS9ob4djOaDuh6dduGcmASJFd0BVkehX2Mx/n/flpL4+Q837InXMuxPXtD9tm/js0pMkDEkHYy'
    '+nb4oANA/iqKQha+yZpb61Jr0qV1QZ2g0wCuoMmVHJ0WgGg/i6/g4Qad/xAxP4mYU+R7soRyKuBVyndmq2x1fexNwWFhR6LTbn9J'
    'TDFde56kRDsdJXPtoHJqcP1igi7wsNzX44tOj2xQgoXJkTJtC9Gi7y5Mi2w0hN8oeuTYLw6apO7Kf6BLTrqEc4R2TZwsiUDwgDx9'
    'cbl58tXLDTKO+7gWG6QfpNkGQeqFMtvCVMp/hIqI1Pk8xzGoS6EgJotcjMJwIfrUgyH8JtAlv2S7AIkSQW0soI3FbdKjQAVftlmy'
    'aBIy+XcB0vW9RUmXP9buN4mCqTvKplzm1P8D8SogXnxPwoymG+A2RP+LbjOIT47sla7JWYpslZ4whYJxvoqvZgUrb1HDvJajIBk8'
    '5lGXxURzO+fs4CPCXYDq83ao8s+hZBahn+Lj3wgi6gQHWoCAKnjiskrcjrLeRSinBCOqTTnzTnDameP5/ObRT3NH2UQ0H+4/kE8n'
    '+QQHNDr5VCjNwAKehPM05Dye4PkoKZ3RteBUNAlvKH1N4jQlChI3BlEvRVMLD5xNTxW4raUoaklrFimF+RJ2yNpUNPfjXEQ+ll9/'
    '4Qmo1yBoj2ExtjSfyXQR8vn9f+G0QVcUm020gt8oodm5AIbInG/TLyzRLJ6ugJfUpsmCqyhYNzvchKCnlvxeWz4HAVJsB2y2mQG3'
    'puFA5upYiF5w97l61KKeQv4cPewuA0Dm5s1VtRDKsS1g4//Vgv4jRuqTO8sd23d4So2lc5xRuTOMI/o5sCTmfkO1UGMJToXdtG0W'
    'XbWcErx4g2psBewrom/Neld8Zft8MB6noIV6NyeTMVPjMSq6qtp54QOmGqvv0fUX31/Q5SZv84t0IFlhOYMpRABq/nKmhCFH8cU5'
    'i/kWW9lh7GMcEF+tlalO1AAhL6+fx/rU5bi5yfwDsL0TaXvnvV0LxjfBLRVrMsIcl9dJNcdOm7m2GSKiSA7BPIsPiJhYvnjEyAJm'
    'zCEt3BzEfWMGGWN9OBgcx/3n4XS+hptYjzEMiACqARS6bBShoAbe5/bJVhkc+PaYf3nHz9zIbSZ6SMvPvaKCKASihhHVDa+Yc2tT'
    'dFgZ6TgOBiLu9qA/jlN11GaUdzCIpHupMwYOCrhibNPPviPLF/nD6cMoRwSylLst3CgtTuAf3rt3UKRHrDFgHy6dMuIiYLr6Y7aN'
    'ywdF02B7DdhTUWu0f1gy2kKguxUvsa1/cq+zS7dRa9Ru8HFl1GVqvRpDtw+plHpUf/LBIJeGBNkoHIM7gFxdORsGcIlOUx7ODBUu'
    '3KcWy20vZQFLWWs1y2fCytG4+ETAvd3Ee7viTFjsaaUje6CxnQw1gd3aRdRaso7+fS24K/dUVIoj00JKdOgMI5yHckbNUTAdQIQL'
    'LRwCYPAsSJjyI0iioBkDOm2GvOLDxnWY8Ozv+A77jOE8tB5VbZIFPVSPPGy086glZydllJsU/08gVTL6TltRPmO2yyfwUgYgpUPx'
    'wClUKFnOh4x7aDEA3ocPHwKvsH7xrIWLKwFsLJwR0QLEaBlc2+4+sJWU93nDdXb3d65vDpywI7IWIxpJsP58hKwMlxhQRMNZOQ6z'
    'IBpbcoMpAog2cER60KQ+SEwr48oBdsdkrsdy8MCc21OisOxi5q+SaHBA4L/0ZLJcnk0e7PygM0wI/Ze+DmYPOtti9riOfnfnenRA'
    'wPF6OI5vmreMlWz4c9fJjgzjOHOmrFPnYIAqh6N5ktB9IPBYrCFldjae9j79/wHhsXrsaXLVC9a67fbGLv7TblFhgmjqP955ep39'
    'gDBthz8vnHepnP2jdGLaD8fVqkuD68LaiPpHc5ZEE4yavgi43qVgo+SBofkhxyAdttrec0xn8B0dY9ryQid5a7etyic1Ti4P1Cc8'
    'EwHRY/IXPqrqQCqdVufRdAve8SxzONfbS8T4CZdBhbhjEvFUM8elihfXMsfZnKcam/s4tn0TKuxrCV/g3dnT+eQd7Wza9mI7e3/h'
    'nX2XXT4maMPCe1odwnvb0yqnxUKFTCwKcgHz5VCwGdUn8U2ePiFXd1iaKWiUkvt+pm4KhpohFVPM2Ed8MeZwl7DbxhNd3pUFmgnl'
    'H+fpA7B3E1PDtZ7rYfYgwh3ZFUUr1pV/D4NJNL59EE1HdE6yAxHnZelm+QDpfICi9zoYz3FLX0WgSWVTmpK1zgbpbpCtz77zN+sf'
    'brKyJVXQ6xFi9xqPnrFfyNrhBnm8QY5q1MHhyNBFqoVbd63Tol3ptLo1aukjZofA7iBnSTiM3tDutNu0qsf0v/666B7ChS8PPOQ7'
    'Y4aV+3YWWx6flrx4d2u9d1puF97d9FvEfVa3NxtIQ8zhYQPYunE4vcpGDxvbDUJH0A9HiEEJb436iE6y9nCbft5nY8s8G/eO4jkV'
    'hxI6qdEkvLcxiacxplk3Tgthe7kJ76D2jnMKceVsPXXH1VVQVDceha2rFmHbkP63m+vyjD1YP8B6JTexQt1Xw7RKAl3vbj+czca3'
    'C1zuDDWIowl5L/gJlHpXMqgOZ/Q5iaKIjKTPxtJypzGwxS9/0zzU9vn/iAJwrEmXEZRKqC1EZ3QFUAxx+BAVkSiny4Y6MfMZ6Pxx'
    'Zurt7w/IS/yUPJ1g7K/DHaM+bTkPhyGVivshiSYYiQ4gnwzuE9zgcp2oy3bJbgNI2Eebi8Y5gCE7LOxR0O+HswxSDtD6N3/LeVZw'
    '62DqXZwipprCKWJDXsPj0ii2LmptgxbC2jSdXfVeLVJXJOEsDLI1kORhGOONSTSlR2yts0V31EZnmKyvc1VG21Bl7FRSZRRQJUGW'
    'TjA4jhwmYWCSIxY31wzoq4YCnnvyJgunmOvuMWjYYBlvpiTogfkWovmZFYpBAAWKnzhaTSCcEVINhgNbcwi7JcfZMbgPeCkxr3gH'
    '9L1iUA2sTTP3RdM0TDL59dq9tU9ap611xR3kkziiW/T0GqgWvLOoSP0mTlsXWhOnwyFheRAbj+DdSpo4sppg+LHQxNEqmjg6fXH5'
    'jXvHaitH9OBH03k4oDcvfXvveAXNnJ2fNJ8dnqnNUA6z+SyY0ePELDKNR7xQteYI/MSE00bj+Cxv23JECMUrk2sFzCwk2Qp1lsq6'
    'ffyn3WrvSxQvQ50nSlAu0k0q6eVFMMO1E91JPzETyDcEyHwzFYAqQEBNpFPzqyswXsTTVABZq6p1yIuCkIt5MV6ARdE/bGTJPGy4'
    'CKBZsX3Zi/PrqC83K1ul3ZULj7P8Rb3vmdvGo7bfy8X9XdoPNCco+ifD8BAmOqVHa59O4ywa3j6AMb5VEVrhskSaqM+++uLRZ3/0'
    'n4pcrz3DMvgh7iicl2M5N4fBOA2VgwtfOdacd8t+7eKnCu5Gq5tuLAjBkSjFFUAndaWL5Avc65ZZAc6FS62P/UMcWvpXNAgTH0st'
    'QHWS4ArcPpgtq7hGGKvzqOBb1/HACX90fvLk5PzkxdHJh5vswR2PogfrAUjENByrnAy+OA+ntH4wo34ATEwLBWUwFbpUBuqmwlpx'
    'I1kEkj7T0/YaOwje1d0cIkcw+KkwxsJ4x/fABRt4ILgJZC+4ha+MxVHbyx20eWuOQrlNt6BQHp3RHM17rKBEKRw5PvSc3HEwpyvn'
    '8u83j+267lN44yXW/OCWlArf0B06CGl3kB4YXFYVKq07ETrGJA3uPjrtptHycxeZNm5BsRzMH6hkzaTXQkGZ3OukoB7hdaOwwro4'
    'yGRiyr2v7e0j695uf2n9oCxI5JvzFG4Mgbj6ALU9zV6Y3dDzhhiiqKJjjMeDNmmTTtdwc3Mp/2zJDL7CP2+Y9LDXbh/Y+iqft0+1'
    'NnwekApQh5jHDQWcA8Q/AeABMgIIEfFVSAUJC7HDRVRc1iMhUxvgxeZs42tKNgtRjbN45gocnYYAjJWgY4aSTpSj+tLXTXxfIZrK'
    'bsDGCmM0ELKpQrYduJDqxEw57tzbKc63zyf6VrpgSeR+toTmCsAaw5kQp6Q5ZuXA3eOG1rRlamZxqVPY/aALSOcT0DmQeEhuIWk6'
    'UmsMipdS4wahyzWkE5NtcE1B8DoEP0OYMFQMYMPPg+T1cZRktxACcDt9ORtQMftVn05d3ql7G+pfzZs+pqfdFGPwz8VNv2EOEJ49'
    'KvI9tqcwh4IpmUNxSpxzx3BuXPMGM3XNDE7g5ZON6KWNodv1Jku0zmdLkr7Fpkv5vO58XQoSUTphkphYM5bqUBw51YmmZEaZOvTq'
    'pWJeCD69KcsrHaRkHMMkpjC5ZBqGg3ozKFvhUyj/XnAO1e8rKHiUtGkczDrPdnR2+OLkGX/8ef3j8BgbC+HUxYwTYcz0+AQIHdgD'
    'xr1oWtO7HfjftglmfMFZ6SvCIK4fCC4TZPsNBeUdHW1MJ3U1n4XHfUHEBIPXvdXBvDM6HABK7WtMm4Yg2oCOSfsIGc/XlU4Y3WC8'
    'NHxcMn+mslCapzT1NfMtyrXXTHGxs7Mh/mXKDa9jB++PAPfTGIVyQ5fCT6Dzlh5hvSvUy3f7/b7XCcSYXLmYOL++aWTOquokeqet'
    'iqeKusYChZRByMPNSFcWO6MnH7M75UOdZy27LAbSnKCGRzA7r8884VrgvXU+MBl4qp+qffr//oEHxdYfMzaKJxCaYllnFQutpVSz'
    'O2YZZx0FO7aRdodOgrNl/j9lZ1kuDGq0EFPFG+Ff5GZEFwJNsmClRX6zqLFqK7kze2Oug3vypOoymyeAHiDomROTkZDP/ujPONEx'
    'TLtOEGBLzEE7Dz+UXdOW7loMazc1bB9s0+o/jMZgGNZv9Cf4kBmO9EsZcoWBYZaVWFN1IHf8u02c8dys2a0yoFrbsGAb2BtU7MKw'
    'Df8v3oh4zov8aAw3IcYMiXnVLGE4dejXUnH+3sFxLTou73iiLB+dxqNDcJRHVPnqrjiGr7U3VlCxkzrmYmsnd/RFWwO37MkAXh9K'
    'grw0MnTxnoSLtQ0tTYD1gHq88Arm7YbB0yCtFlxneMfqXIHvjpUP3ojh6wPOAvCFFSOGP1wBj4pHNeZaeCB+MRxvngLJvbeRBlMI'
    'rEqiobWf7A2TgUZX9gD+QM4efrHLggZclhUA1/iLuatwLA4CzD9m2lE3n4cKF7xK5CUiTsFu7qXgXfvuzrpjmE5dz1aXWaNxjwqG'
    'gk0TC8exaLtXa7Rt18RcwsAIgP4BLrT9ElUXC/lJCdjFKMcFO2gSYGgJ5aq5XEdnRqSNQCAelm9TMnJpi3yNlgITTTBOYyweMMlg'
    'EkznUFPLdYd5vKPM48JyEZacF6a31g5MTc4ePREa/u3EWtCcGJZxW+i2TbcFp7O2d1ZkMsOSiRFhzu90bmQjOD3lY9DCjxSBQhUf'
    '9SIoQebisP5SlQ1y5w2Ju8lFA7ImYqUhdwIdKjEU4+umUwe+F4IFb9ny5+Fq4l2pJnbQC0ouHI6IhkK48ejxyeElufj45ORS0+or'
    '+g7WIzBrzZwWFKOYriyFp5DH3JlY+DxssrTD4qQjokDuo4JmV8Bo7rM3Lq1qpZ56HKJylbjrrgVyewSjAC0d5TgHV5A8i5IcShko'
    'C9+/7Y/DB+SQvutQjv2HpHvIfjzGH1vWdOp3av2phKyRsLdMpIsYlje7fdCm8rdwT4hTzTNM36A5morYpaafo7TLvMeNKLVg72Qf'
    'wpBgyEV78UrNc810ErjtamzGOl05HAyQg10zAQ1642D6WiTX/vu/+y5jdBfY9nV6w0wjl5RHsdMq0iuZUm7gOelrmIcfEf6mlb1x'
    'ncdVbPUL3rGFdrqkxRLC07PVc/Pi+6S55yeHXzk+ffXi3ZBcMaSivZ7mzi3IXyGvMItnc2AkEBGRfJmELFY6XRkdrtV9tsUY1oy9'
    'J2cwyTqAN8drge0K+5LBxStbQIDv1D6xRpdyBG+9S306dVdgIWMo7YC4MmZYkgJHPMz6rXWe1+lIlHbhe6/uwnAAPta+MM5RzY4c'
    'zwOCmQ6p4Aax3jxfi3GmUIrrFdkMzFSN6hdWvkZnIZx5DFpR9MWjrUesd6xfanJHVQjnFUGWmyZe6408hMZ64+6+5alm9hIM5c1B'
    'nOVuZmGKPrkix7u73hL7cEVwS5EduOHvH7Ou9UPVRyZ/prqtMEM3y4fIlz21VfsGJBJrhGXqNf2W8B07MrhMjvuGnhvMQUR356/+'
    'eyJy6PoCR6zN4fa7Y1vD9N1hvlLYGtvhkLnzl1XiR3xbU2jwlOPrStFsTtlsiP6wYn8gsgWr6mEDcyDj/4xpZOpANo33aCmwXx6O'
    'xyW+t7ythtR2q20x8LaytqAUNAZOTcu0RrdcPL4OB43C1kQpaPGc/16tVQI/KWE2JnQ2hqNZOkoodg8J9o//V3I2dgTD12lUukgX'
    'NyqKsYZ/8S+JSB24VON5WsHCxmUx3vq/woybS7XMGNnSucZivNW/crG8NZvNYtFqYbNQjLf6P5BLKy684LSzLGlaqkotqSSngdJn'
    'ltGY2zBrfdhLHl3QaQ2Ze0g0vabkGxNNgGB5FVK5IwwHoLtvVQhcY7ezSoKq5H7WriPyAbd18uxsdhJoXv1iOaDdlFfkgVav7MJU'
    '0KoGhjkGOJKdf3x+ctI8PLokF5fnL48uX56fkNNPTs6fHX7NmTucjr8JehlaX54EXQDzxCwhKXP1kH/Z/C59lYZXhP1oduiu4x+k'
    '8Du/B9BW0D7gZqwdgPuDbnbMHeassxvITqTwu1on1KXW2j2sVmVPqbKnV7nTNqp8XKnKLWXkW8bI94xewti3/LUy+63sofhTm8sv'
    'qQxT/oteEXIxqayI/+lsE9/BQPLSvTFdzkeo4/H31f0dXSb8sGg5PF/2+JeP6365xT4smFfwT2tG02Esv8ufPJq1SJtskt9vm7Mq'
    'g9I0t6XLw8uXF+Tx4bnzZKVZkM1TIVFrDlT4hiF4OYJc2VvKOxOIAh5wR6uA89O2Xk++Zl8y6BoFrdy5M7Q+cEywB2qF7D0ENQL+'
    '6o9NPC5fXUqubLQv5p1CDecD0q5WBWQJNmp4RR9VrwCXVa8AXF5pBb9fsQZ25vjWeAbBgfkZUK8GiE5VyaiF39nPTtkrhfhfgvtj'
    'EzbrRZbM+5B5mZwKOrwFL3LCL3afuvnOTz55evH09AW5PD88+srTFx+Ry9PTZ669yIeXhNe5vw50W32AQ1I1Pi5HaQ3ciYlX4GfI'
    '4iaD9IGy43Q+BVpC1n4waGjsCK3x9XkIlzNE19HXwIh8ANCkOnvrqY85CDR89bHXUOXvAxNHf69S6SAcF3WSYWjdY0HcHNaqUl8h'
    'Yq7hq3Y6H4+xyh/ZoXXaukhX+13Dm11CPzQe/bdlC2HtUNGP5/EgVCGknd7yJ2+ijIgv0uJdenFy9PL86eXXyPPT48NnbjIZ0nMW'
    'ZbcrxhRg0UG8bhU4qBRPIPe12d0GdSWHE+he3xwo8c37+9cjPX7C62hXFX9AoA/8jHL/nDsVAzCiVGqqQvYLoYedyG+GR4awSW4J'
    '/zJVgR72z8MhZX9HCG3wR/+J8D/9Cosy3AT34hWjJqi/opGH+6DnOm/VwBP2m9xJveEN0WgfVENMMF3HXAEN0F4GIppsnf7VDDIw'
    'XWsY7K6vmtdwDvDLVPkGb2W/x7r4mPJFjUeX4CxDDufZiBzyCiqGYrh7PgQ4xjrdZh+4KEsSDjCsuMZontDKgOrWGkCNzgrdW40u'
    'cYXru+rROO6/hkj2Ol16ht+Qp2fvsF/0RomhYyta2MfBdFrcZfOYXwa9VD/f7+o4G7SL9hu0C5q6kj4AKPMrU+1CC18wHG3wMqYF'
    'UE3Z71MqT57FVyVqHt6Urj/EpqJZWtwULQBNPT0jz4Mp5X5ZuMqCraVhBqGbacPXmigATV7w3/3aJAaUiaFuzgXkZh/TPwYSRPE7'
    'WF0dqC2fUVT8uMIi2OCauEb6gEXYnTNEmhahn7iy+uh/QC+0yS7rCK6gpyNOzsfnHeTxNut4gh6dvnH02JFsFGRkBNin/KIJ0dkj'
    'YFOL6QW46qxFHoPz2RQGTEvMwmQSTGm/x/TOBXJFIu4+AE5QEPUVJ7Q0Ja0BbIyWNwKbzkI0qzbVYpOVzXK+c1c91RU4QIn02ygC'
    'V3RhN1YOl911hsu6vBYFY3nyZhYBrpXtIFhEQnednqYea4dYgME8aXa3Rw2TSoXZ8TxZu0dfAb3obpNRTAVut49/tVb2DPFSaWUP'
    'Rcs9Ss1ul2piqz3wDYS+gja22ks3AuDhw4azEXyFJB1+iaZRFnqiIoqXtkJctAKCiOsuuxji3kEmqfGICdboygoRYROEncpCl/dp'
    'Iaz9ezkD2/wMMMGCPIsmkSO9TW1iqgeB7dlH5LPv/Et6J7whO2SInCuZ0TGDhksQ2ZT0wiHYAjo7TfBtB/oZzzOwk3iq6raFzTZM'
    'gAJTWkVlrtTzBXCn6LxE+uBzDO2S/XY7D2P2fcivVHr5kddhOKO/gWdMl35KyWYShWkt7EX/kst4DRuTqLO3cX8H/kFMotVsDmRN'
    'XfTxGHZzQr4eW7HkVSVnq5niIWFEg6bN6LP8cGv3LujRYzdu7nsAtJvfv799b32dvYCCVoZDun5/+n8QrEMQfQaacI4sO4EAEra6'
    'pTFWtZIw3KkKpVkwmW7kvzL9wLHfeGmo8VUV1dHps2eHj0/PDy9PCrRU3Pz3DnRUzPq3oIZqx9RQLaBu+sFfE2aLZdsjd28KC+Hr'
    'ipU3xqgs1U3ZXnGCXXY5kreeZJd29AGlhcKSKwy7DnawPwFOcD5TebmZh3pYdL67ruGc7FvplQ26fwRR8SHEZMA+DY0zDLbuluZK'
    'lpLJnJJW1NrRrz5MsySeXj0C5pk+EBcGXRL2XGPKhb94CzhiYMlZRFgwltVAoKWjEkC5zBLaLr0SWCxm2lLO+UwNH1ic6zXDKD7R'
    'x4QRx45gCjuEzwQZLYRBlpSXR+XtK3pMWGJiM+X1VKvF6Diu28XkBdGIWYPRwJ9ZEkxTunCTB3OA1esHaWg63bZbO9gen+gzMdFe'
    'E08ASMOorPmLf0wviG/N6XLmaZks2C/L+WzSBNn8KjST8PYnh/T5R+H07EaxKxjMp7XA2JtmGg8zxxLzG7S70dnd39jdY4EKjrHo'
    'i7+tLD6s/X2YYSMBdXHEHZ2bX/zPoEGNpZ/8Qpy3EwnIsbuKQMfpfANdaM5uGhx2Fh3T9VjkVxG94Xsh82wWXUaokDvF0ca+A9ct'
    'OXBdc9J3XRHtjqUyQMctaIBq2AxWS1pErQuT3P5CRGv3J3B0zm642dDBXFlgAv3JUTy7ZZ+p7pX0ITGIeMNB2rCT9afXRSWMfS1j'
    'LIXtxrjpkJ6wdJbgdwrBzimX9mCfzW4ogZvdMgjzz/72T96DuLkjxU3egVEEernD6S2dJHITZSO889Bf7MNw8iiYUlpFf/Lsl4La'
    'gYc/zDzHIGI3ZNVQvxP1wvTcUMZ461JzQQlQW2bcFzAFdak9drmc1ovmVflouw261DXBNqwXkf53QMyA9VCIWX5ONIL2LAS1JAsO'
    'AsaFMliDJnr0MUZoCdK2tXLSxtQPxlErpmz2nVOCCWCToEs051MCdA+mVMmy66E0+HsFGmIEROdO/aP4ZhPCLMB/9Ad/8B5oA+PZ'
    'dMaZUwTz7CPPqwB+Mx61QDNl0oDjOefW/cwpX1HsWnc5dlIcH50Q7DkZR9tMIsQQFz8l+GEnqkmV6NDluNBnQKdRaQh6wmEGsIM2'
    'RsRqR/UONdvS5MeJl0u/3Z+sSL3N/6c0ZSq586aW0XHb7Zia7ryd5RTddkumujtvaXFtdxnylrIXFOLSbVtmmtpKKhvlQ03FYfK6'
    'VjACUxtYDOevf/Hjn5KPRHzuBVMpwMG6U6S6K8uXzpUnhi+8W3NSHLdlgJo9VTz6LUQzfd51E+TiMK71qJLNbcEmw07DrBZiyjqZ'
    'nlJxX+d4YGaa+ESX4ICnAZbmzufFxRSLZ53FxbNCIKgivbohYcHygHzFJzKXTeBlBe21xAAAlWeAOivwEYO4TiqpgVZ8k5xMggh+'
    '/qPzgqvfeYf4gt3qj5P2xK0yUddgR6yBLm+qATUQ3CzZIoFcbF11GCmM3+Jt/YGUI6oAsFUcFc4qO2SLjOwipCPhI+vdkhBqc43j'
    'b/nysZZW2H/GXP+j84U6Txll2E79eBCi8DKJe9E45JKL3M3fYllALEvOr34GHx/Rj5cy1vC9L/qxxqOd5tOMzhdzBR44kDzFFc76'
    'B4YIpbv0T615ynlfB6lSgj1oELwRHzY6u+0GB+djf1D2jRUpAco0tcYSibTPcHGBEggzKtgg6EJ4UElpv2Y34LoWKrYbCylOVTEC'
    'UFwFTWS3ms7ZuPm2i26+VSqhXYBCBbx/ESA7vxrqigKUjfkBMbXS5uKllDQ7sq0WaN3OcSnDwX8GWmZlg8KcdFHnRqrfbSbTVHov'
    'K9MEa2QsnGkK48NW0QvbeacTvg6gy3H4fS6tE3yEd4Au6Wcx0++p8fkkAIRsBLcSisIWeZqRm3h6LwOdOE8JdhVE01YVkN7zELHL'
    'b8nr8JasPY4y9K1NWFZbP5VJ+Gea9dYmNLk3QHvHvxc1N4j/QsgMOlDUJzI/+6t8xb4SMsR+iJAT/osgPY1vaxEYVhutrBKFsZas'
    'U2ldd9YPfO4jq6cwyWukMKsmMC/CGw95advkpeOxtGP0H6LOPMD/NoPx+MDE2vYSIX7o6Fl9N1ToEnYRUILeLZAh0GoB0A2nSJT3'
    'wbQHGMfO/PbBFNUCXxx6u0UZXf5JeEO5cEqHgiFjXqIliJNw72EBjJatoq4OEufBQTuKRBuV6OXIL5oqBGiUiJ2Cw6Ij5ra/ZF/Q'
    'V5DVaf0gmEYTVMM+mM3HaUi6dIKnTBl0UIra7CM8PheP3EOW6Tt8adxylpjZ9gSYrmKdzR8KcDOmXmHvUo7dP41vCiGCSprlEcHM'
    'WpMD/Mj30/kkB+sRntja+fanqaO1IBBQIU5wwYHRwYGnLEDGl9+uRPhifm70YEgQhWIJTAKhy8ic0kQ3nqYB6MV0NavceL70wo1y'
    'A5w1JzI+oCHi/UScn0eFp5/4szCZRLhNU5lrpdKRx/O96+QWSpVKKrNRh7WwYX8loFcVm5DdnADyBXtTZcsS8gbqZuXUxfQSZU4z'
    '5ANiB3QVNXDfql9JL8U0KsIJ4Kail6wFaV/HAlJtAXT7K91Uyy3JZz//07//j3+6zKKoGkdtUdC2LWD3VrAmhnk//Fbri7MqSx6L'
    'n/3VMiuAPKc9/yo7vZIFeKywTstYb5zK+EZlMm9ADKp8/3konKa4yhm0F38I/C03EdS8UfSm6rqJr9umIuH2bfp517ADVXGQfnF6'
    'eUIOXxx9fHpOzk7PXp6RNcqfQpaLMOQRYYiohH3D7F4MEQKt8njrrztdqpG3CKb9UZwg8OasgA/KPwqs0DBj0ofJTJtvxRCnMPL7'
    'hu0NfJaB4h9if86gOzC1Bi5kDgMjI8wQ6YThXb4TBAOoX+Jt1sUv2F/eO/xHHH2XXIznmFkulXidCzuHG4NajXO4GXmPq5MUpygq'
    '8MLQGaTdXGKpEj3slJJ8ooiPi9Yu6ZSDvcoUpBwx3ILh9ByGPJYs0YCOi7GMK9Z4RuWvjBHIn/yS4F9V6yH8pyPIQ/T07PiJ0VH6'
    'pAAIQl9/JBbmXoH1ZOkmFESP3fb1yIo21uGW3nOAi35MLIzaauT7+PzwySV5dXh5cv788PwrBTEugyQY0mt/8i7o2DHU/YrepQng'
    '3iwY7bK9Anr2/V8S7AvEXsRJHhKFaDYE8IyWIGyeUS5G4GQPFg1R2bVCVHZVevR0OpinGWXp0iyYDgDUHzcAegDMkzw5Cf2NPwsH'
    'hM0qgqrQSQmRJcSUn8gCzODoQ3A3eQXpxkjEglPiJKKdCsasgQMqsvbS8FtzCI9PBI4QGVKeJr5h/nqiQ0hTW3eUcBQ/A4j5QNzp'
    'QDrDhNB/Pb4azOlHOQE4r66sGmbwYqLobgyJ2HAk0rQ38CnPISo33l2LkOfuIoMbtKyALqcH8KWqvwjPB9VJLXVbu4pMX9VRxMXH'
    'e71bd3hKKyX7GR3CGUu4qHk2WdPCYoovuGGX7Sy25YxT6ST3MFE8r2NTvfNFKjiH3jHfDYIrLGMQJL/B1CbGRW5KTpZzPfjWv5s7'
    'RSFGdCIQRoxdG3CK2dGeIHkrhv+ocUvRZg4h7BuawV/q304fP724PD0vwgejVwhkD34Xl9LHrOoFb6P7u/QG4tIFJhY6ePfQYH8u'
    '8iIS3veKwGDVXPPrcqgNuUDNlApmmDWFoSWWsKXFt6i5LNVxv4pCFBUoGSXRrWpG4UPIk7Gq0GEKmRmJzEkqjeHQrrgPdKuEJ2+t'
    'LjaYfGcB5fYgkahepopf3iqdJqtJQBx/lNARcYRAN9ALTmM1mBc615gkGwz6g2g4NFdFV61oS+9dc14322yQek102KtJd1XvPtlm'
    'o5W2gBceBicKQKZNqmAabLBgPB7IjO4svWYgRlZk8PaKd1ApR6rmLokSvhqjcyDTbAKsHI+yyIMxeKsQOPkfiAC7Vt9UNzhro4Op'
    'aFiT48u2rK32Ee/ru1vqpVbxkdG/6gtWIEdDw2DeZ7sBgxnz+ZTus5r/aMqLMsgQyPU1jmaYi8+noxM+BPzTxRZ3CiGtCyxufXZK'
    'jKLYrUW/futcjPSq/iFY9dj5m96yiYQEUlS8GeUkB8a2AQ+5+pQ09ElsILJWkGboN0CFK+HspJ25VjWRtarewbx/q+Nq3FEzqCVZ'
    'f56l70QpKipfkHPb311Wj/DZ934JlhA8EkR2ZxmVqDWkVWlFK2I1mFh6okOMG3Jhq/VZhjxQc/oVbMSM61gOp87hQtRubbGQQJap'
    'kIidBycnCekUUY6XHh5+yiDFT8rOEKU26MTTjye9aIoeJn5Qun41TkXuCSrWzymz/e0w8czda16SzV/p/LQrzc++iBrW7IpOXs7L'
    '+TUeyUGAYxKbQHoVyBNN6dfVaAysjAHB6h5gaU4nXr4fzAAEncV6l3nEKDj1+ZcsOd8ZrnBgLu1n3/kbn1CSa5z7R8G0H46PWIWK'
    'o4fq0WLy1k58ZNtrr1Th4uf4XYo+w+mP7n/sul/vroyS8mJhxlkNzyB3v5BjxI7DwR6Ew2A+zmqIhSvRq/CpY3ww7w2odfIepStU'
    'r3guhsVgrh4fHn3l5Rl5cvrs+OS8COhqHM8HzfR22n8nYFdQO+RRXBTvqr0Ci+YfkMd0H85n5AkCCyyDcmUN54up6r94jaIZJgvX'
    'co3DgSR0JhSEjBSRpSjLOsTZATUs96+fzOb0yGxQNrQ/ngMp4EVS7s82gLAsATh1Og2PE+ZAyR5syFfHSUyFiTfKmziRLz+K46tx'
    'SPRvW+RJNAZfESpATqIkicEUEaTkQwhjetRKuV8Q/oVjms9SbpzIoglmmUL/b82UoN7bJ1NIa89DoMwbu5rGf7uaxv9QzD/vp3Up'
    'MRQR/iHrUDNFjGVdtGT2AWYL6I/C/us8MCtthjieQZN9j9sWkWzgJQtjYyMerMHZbOH34UAPOtZGIDpCiTocKavXJlCIW7Nvdo+p'
    '+0+fPHFq99UFYkeVikLZaKHlMZWfTEVHKVRWwBPvVlpSXQPIrcacwgwdFKaCmlbxWSkDU1HDitMmzI8rrFjDUQlbVy1y9OAbL1N6'
    'dr/xtXj+DXFYv8GUy6kOo/IOg48r25T2NPCiqogpd3Rwp/wMXITZGZ0qtvvRhrauWKvc712OXvl1kD6mmy8N2T5VtGTsMYZ8ss3g'
    'nNt3i0tTGtZtgRnarswGL+Zqo2RpnDhThgO/sWCTeJ6GoGGj+xhWAmerlU/Ww3tWKN89dx2wrIVVyAm/13j0QYkHnRrvkDYHYYbK'
    'Mjx8acOPkZh7BQniYuHaVAFssEI8KlBBaKGqTZq1YdGsPCwgbYrkYEhb6qjFXsTgXzAdRlfzRE1R5hnu82BKpWh+U3qU/rZ/e1uf'
    '2U6d9DfKgQa+7kWsRZQKB13JRJKXM0LLVM90YzbC7omvRzNPM38jfJ74hfL1p2ceoUedt2O+JXPGTL2OUs9MmnOmYht1cvGO/V1u'
    'xKipyainpXBiN4tR66MtOLpM2OHl/IqK9+z3ZUsVi4l8T06PXl6AqHdCTr769JJ8/PTFpVPmG8Z9eppZvm9wkfp3lN2iTwikAxP1'
    '62XDN1HGUfmYvuXD173Bo6MsGX/wjQ834Xfk6eGXk7TPn1C5Ar5zVK5AiSr1uzKV4bc8TRlmYDsxa5S+unqPvx3Hk6ZMdWfYUJQS'
    'urwfZowj+jp9t5bKX0kTrq/8ksdn9I6hXfrjH9q524xecLbR00pHSxAbZgS+aTwCZtCb163+AD5wDCCaaleftqXyGSaX4FEbv0Ht'
    'IIthQ7tsyHJIEiarcL2nsQgZ+5StAVYbjaEvl5+Iz1Mj9a4YYNbD4xNyCsqS0iCDy7Mrq0O+pC/yfMoSggPdmD8OAxRd13CzdgRb'
    'p12G0JoawKhwZ3cH28H+9taBLgIx1QJP2Zyn3fQmBSwYTsDtPvZ42BtlQIcMvIaNpFt7JP12b9DbdY7kkFvwlhuKK+O2HI2aZ1va'
    'HsUzPqat2mPa6d3vDXacY5KVLzusPIu5PSoldbkYlEhezse0XXtM+0Fve7DtHFOeGH25IeWsuWtQ+VtlWJfyIR/YzgJHaX9rO3AO'
    'LK992aGxVG6OUeELZUAY78fHslt7LFu9YGvfPZYXeuCrks9bpDD7hKGYckAb9KQFdifIHmbXAlxCZTygI2lIGRz6M7suCIXRpkUU'
    'N6gNC7P3EBz2Uqc55DF+UHex7+8Md4Y+asPqXGCtXYPqg5MIhO066Y54qdId+oycwgc1B3W/txd6jqasc0WDyoIr59kMrtRDSQut'
    'bgi0tqJte0alLu/GBZGsbOvOMNdxjc2LHxjb17Nx9S272s266Ipa3adi9FWYqx6dTIxeRGVn4A05lh+v7qaUNbdcIzUFgn4wo3xd'
    'AMbxw4Dh49NHURaMozRkNmSQXdGzBkQA2nrsklbODs9PXlx+fHL59OjwGbl4+dFHJxeXkOD6+Pz07Pj01Qun6DILknDaHCTxbEC3'
    'oGVOmg2kFegMSmajEE0fuVDI4CpBvUr5329y+fGW/M4Fa8cVUPP08NnpRy9PMP/7U9rHowuPPY13ggl8Mjs4ThplRlCLIv1jqpnP'
    '6GegnvE6vti2s9wRxOOpZn/OZ2w10EAej5DlUnGOumY+bBPGyo5g/vUvfvRPiGTGYBYj2u8+3Qmjrkdyz2LTGdK9CuZcK+ATpfZA'
    'r+NMu0peYdBhxGLFUp9yT5QyY2KZfeOuW9Xn+xbyb/Lvt9gYHZx1lYqkmguhOBftxI7h84ISKa30FSDxLFopZlVyVPoscoVcVqx0'
    'a9dd6Ze8oS0evRMoYPtJPB5Le5ozyLHN9pGlWHZtO162a3uv+7ZdBgmlU6Zr5r1gj9zRLUUJuD4+PD88ujw5J79z+vL8xcnXyPPD'
    's9oU9ZvxPJmGt80JvY7qkNTfYd89D2b/QFNr09TP/uS7JBfaD5N+Cv8Zoem+LlW1F2IZsmpuCXFgCsitHT6uVhBNp8zwXXY6vzlp'
    'jgE5YtBwRmaw5dotOGcKlpNZZTO9CcARoBJm6c56zt2RQwzmBB6HBY4bNGeZNnd2NsS/HgBDGxeFdQqsQeCQiUmpFS7URzSkMjGi'
    '3UpY+AG6h4+rQEeAh7zmEqQoZ+krZKsbj57QumVUMLagdU3VVNOPnF5BUAX/Vk0EBK/I2knat92E8hGrnVVcgzQRir4CsisXT/MY'
    'gbfckAf9MBwzzHrQ4G25oOYuBVAGZrvAm+CC7qv+CB3cIQELOhiBr9A4zOgH8XBI12YWjsfoY0JrpFdE6PTkxPkEdANhiah7L1ae'
    'GLmw+tzow+b7q2DkIgAGIl7qDr14CBjNEc+ytGQ8/dFrOk1+TyAsE0Cj5Ij+IPSkgVbt2hr6QjXf0ImAql/BT8ISCyrVFgyRqbJT'
    'n8XMDkKiTyB+WDlOGE4cz8H3DF2jPvvpdwg8K/G/dFb9gmFhSE0gxGrwavH3z37yvy1SrU0DzJAp3ojcj1XaKIj0ydt0R2qB2wU2'
    'GaayUUC8r29aPDv86IR88vTkFTMvPj4852/e5z+mJuAqbMrQb934NrsWRx/A3bxmNFrMzO/CHiEfFk3ndL/pSpoz2ihUCXpFUUJT'
    'LIqHhDEgqA6ZxiywHXWrKeRc/PcFiiTWA603Do1t3hFTY3smm8LGr4IZ4Xwk9oIOKEiigM2PVhrmknbuVz+v1zkMjL2F//p6mJdQ'
    '1VlgQ+zdMlsidDS7YdOUQq5qAHnXO6qVl13VemvxDcz+mZuCc8sgusfCc2YAIB9sfvbHP1zXbMULG4V5laxCr31Y7dsM1Jp8hsWD'
    'RazGZA3Lrvusx4uaicUkrfvtxfyEYnD/49PD82Py9dPT50go1piAwqJhNyBSJgLfW+BMIexMxM+EN27YsLTnWMD8Q3sRC1hD1zz0'
    '2BzIGuXSUtZ20bXt1VzX3orW1DmWD1xjqbOohy8vTy8OPzkhl6eHF26PEuCEwOFaaIY/+/mP6O0cfxPDIUFFDC8Hrsrryv1M1nfK'
    '7ILVopKtLCnYfEDxE3CSQlL9cKaUG4Rpv/HoIwDsVZzjScBmDRTZAO+MHsThoCWxaTjLpPWX++PmdZc56F4cnT89uySXTy+fnTTI'
    'pk+nQKmtl4XyCNlSx+GOFnJXQhx+SixHfV4dZq2qz0ecnoGKv77+nCWqFMpz9+rryk6GHZVviUenrApl+f25qTRHcI/XZarZYWzF'
    'IPRfDQIggJLg9Aw3XDm9PvlGVIGzwuoBBYUhBdCUcqbNoAL25JAXMGIKCP+tAM+6JLrAEV9QGGGg9ZbHGLywQxZst0DTiVZUhj7P'
    '13QTJj607gI/W/+qPeXVOsZbM1ehcXBlf1V2Fg2Pk2hK3+/o941YONGfNfDl2CG0bKWESWprWjOddkk7nTbeYytoqWxEHRhSxzum'
    'iugCy5165oD2IriOrjBJyTFb2Co0QLWZGH7k+7q3824J/K0+hcidTIeTrDmcjy3uknaX9vYJWvTX7kEJzMX44nLz5KuX5P/93+lY'
    'JiH8vIwmYQU8XF/bTN9T2DgWgdYfwy8E3A6WaFAgqRW1yMpAk3fJC/y9Gq7u8vvkVRIBiB45TNMIoPCyVd0SpRWv8rYQbXivC94b'
    '2ZkvxrUhu13n3rC/HlJ+aJ6EaaPauTaRiaus5gWoFtksvcN1RAWmdw2xD0fw0Rdi9Vhnl7nxl1iPj5IAMjFw4wFW9A7X5Yq15l0Z'
    '3psvztqIDlddnXdCWg97VGhfFTk9wgkvz2li30Lgf9hk65U60o3wiqV0hRkp+qK1KqFpC4wGfBVJSkXdPiRMo5dhf/Gh4fepc2zP'
    '+Ct9cHmDVa9Yj3VBkYyrYTwVxdcW4gm6Q4a7rhi76kFQnKkNZrMmhwB79AmHKuu0Oq12q+32PqnRApfVmZdb8Dokz/svwmhchK9a'
    'WSsAKgYuVy8etgT5Bi7I2eGxQyuAeUBPzi/AL/Do48MXH51cWOqCHKiCe9rhKVsBdoV+KkkSj2U0ANdNYyPgTj/XtNXjcNC7Nboi'
    'FFFV8C84mr8ELFfwLxT88v3uu4EdtadR9J3DSjjpYD0cDWNqVUU/s5vz9huPvgyADunBEtBYJtSmDQrv9nkS5BoDulX4vg+ngVWK'
    'n17umaUZLtikCXTMIlnNrMyS5o0CVA5mREKVbEbxDZ9eTknW7vFSINsI2I2curC/eXwJPQzjeIZxXb15NBYRuy4yTSdBv4T0S4ft'
    'QXNk6LzhHhO+ykdkMCujLXH9gupa9p4+1svNnC02x3SfQx6/kAyjJM3IwBwowJ4AVl8SB5hilK8aNKTgkJcwJGJyn8/HWTQbh0KJ'
    'HE0gpDfNJ9uogDFONisqcqAiqmAK+CbBGEIqU5TqeBeHiJQSgSWAyskzSGCD6eymA/hLYLbTOzsaSKU24GWl4SyAZDdkEPfnMBEc'
    'DM2X7adowCDahcnxPAT/Hqb1Z2NecMhP8WMCSF7XIVFqb90Mvs3YWQQmEK2lONzfuaC3RIjh06mKWiMLZaMAw9GzgE7XRFkkyhgA'
    'FZVTkS4xF7j4TT7TYjaG4D8V8PimhWZkSr8azPshQ9jn9YLvKUeO5IEYZA5O+GCtSOL5TBsk9EcOENzyEewnzFdsQF9E2e0SY78I'
    'hpgsgEo3hJ6/wZildV5kwIeUOkwwlj1OIAs87l/Y62BOh2y/gA6T4OWdkhhy3JO8TCqgN1NQWEl0TTJMwIxHTwXkLFh8mDI5Fsvm'
    'HvWiMebyW2igXwnDGWYXZfZMDJyl3ZfJjGVjR3SoCU+8AOCgKY4EJoi+FnkUkoyuusiICks7mS1zsNUL4RpQPaL+Mrv4cDwWIgce'
    'YpbWeYNhCHfaW4RftuBc9BrubFYAk0z1kzhNKeFOX0PqKzjv4HoFMWtZPKf7jZ7feM4pwX2AToXdHEMWCkgOAacD1AV9GAJJX0cz'
    '7xmnY2PTsDL02UdLIwQYAqLGaBfy2KdnJy/IxenL86MT8uzp0cmLo1IOWgpzy7PQpvBXn4fWO7MAE73zOTLR7s6j4H3BTsEzp+Bd'
    'i5e25thmpoW0/b656ZnpYU7sJBpdHzyIhm4HgWuc32H3Or8HWRIZoA+xos4AwkB3Kdzj5CSgtEE+oKRxQi9/SiWug2iMGHDsIozg'
    'FrmZiqlqmclniogkvVTfkPut3VZnQbL4/Okl4ctIvjyJBoM4O0B0bQa30G13dslxPA6mnGIFouogag6jN03Id98goyQcPmyMsmyW'
    'PtjcvKIkdd5r0ZFvDuDTSTTfhI5u9sZxb3MCENPJJlKEi5MG4We38d/0aFFaVwKbZxrjBZPQG5dWHSYJbHJU34BpSEzVh5vBo2r6'
    'OjFfv3Px9Wi2yql6mTL1BuyIHl1PSjsIxANJdoeEU1pNuNj0XWTz15vfTL8dzcTcRVMxcy3IsIKRiO93Cs+On7S+uahAcUhvzVEo'
    'p7Hbart23fP429F4HJAnCuu6yPRNWD2bs8GQdvkLsP0uKcsWQggL7Q7Z06Xglc3j6XCISTFPj84RCy7tB1Pg1ejC5eLgItM5DWZU'
    'jNnMlEG45rQ1GXxe00pOplfjKB2RLKEnhY4ZxPxVHvfH/IiPYwQ1PZCTy91HE5ARqCQ0G1NhXnidLTHP0P86kykd3ygnyqcTMtij'
    'fIbHqPZpv81GC/Pc7GPKcAyzG5ia/DzLmRUq526NqaKkNW3NsO5WnFxtbm1ybqc1yibj900Ob59OqfDz/7P3bsttZEmC4OtYfsWR'
    'KrsAtAAQAC+iyJRoFAml2EWJbIJKdbZSJQWBIIESiEAjQFJMiWb1sNaPazbTvbYvM9Zvu7Zm+75m+zj7J/UF8wnrl3OPEwGASUnV'
    'baOskhAR5+rHjx93P34BphGkT+C5aeEntwTYj4f7KqlJLMIti/hjNx4vSBPH1wPVFEEsHsH4kAX5lpA77g6Xjj/cElJcufg8ljqc'
    'NEbBFHcEyfAsASxCAq+ururT7hAYWxDdEXypROgleDv98MVg+LVEvMw92XwyXq4UR+FuasCd34EYRxFtDqPevPG7pejVmCF6Nb5Y'
    '2rR/+W+Cw/vAoH+DaGXP+7el5/ASkmWEp9acwlNrPuEJz6DBJSp30+6EtHGEDuRnofW+pAyzbJ0zMo+LRpl8GLMiG+g5zRFGsjir'
    '+w84L9jqkTckaVft2FJjGBUR0Xz/8uf/Q8Z3auM9L8U57/VIC3EFK7V8/5tFOl62Ih2vKy/nSUwfAUUoZIkT+Xgw6seTwZR8aRUw'
    '7iD8JAwBcdzyvebr8TQennLI7HjUQ06316MNtdgOuOMwmfZuvGVuZPRk2Dl4cbjfPm7n+jEoj878KDNRN+BYbMJipJkQO5mKMpbm'
    'X/75P2Oa6xGbiJJppUZV1lrbEXl8n+HIS1ITdq/Y3/9ZHG6/bDsX69+FSu083z7O3sHn+fd02sevFg/bkGI4KGAFFrDk5xwQlnNH'
    '0Gaf7WD/x7/9r/+3IF8P7QPj+HsEq0rCu6PiFEuiaHyMTuJTTGVH6nW+ORgH0P6kxmZPycXY0wW6JaT9DXneJZMBnLnRNJP7LdBy'
    'tz8Y59kXQhH87N6spidQDfg404f8cIkKV5RBQUCb+q5IB+NpuWTVKVWJEYABywoF9kdyGHP1D4xZDwS3cTz3APZVjUXV8QuuzLNJ'
    'dA6H5Rj24SS5uot1cQECR0NqQ6IVhACW0lNvmdHMAn4QB/wul2d3uRzs8u6hjcmXUPgEBjKjB7+7TdDlXhwgXPuBIhUYZFkNitco'
    'DXbNOBfdAaHOR8l8fb9MVM/pF16IjiRvwBgi/n+xpeDmbVisBUHB5TQg1vS4FgN+trtma57+mq2763B9rg7XQx3eygQyz5x5ptOg'
    'tgUBEbDNEZqfXu/1yiX33C5V6tTEPrAf9Ul8Dkc8kGwOsvmbXQ3JXNGc38bd0DnU50tPaUdHP9p+0Rbt3T1gYUT58PnB8UHn+cFh'
    'rXP88367shgLgwqKBTiY88GoTNZ8VZSBK3PyMvvQicr+jRZJC3A0MjnRTj/B67+r/gAkQGkBQtGAUmBp0IaCrZ4GqcXs1JHR7yMZ'
    'gNcgH8Q9cTGaDoacU4lNkbR1AKkoVM4mlyuaM/CV59HkxPefgbRsKc8fPW+w4dBAi/x80jLeLwMmHVPSyOGc6LloJxTxhcSTOJoE'
    'u7F9xAmLtHEKx8IJJucjXcFc+TaCYZXsvIuqVxyvNFY0tIzfjmGGAWl/borjZsZaELAf4nhswPoUtXdIANBIRpAub1G6ktNPNB4P'
    'r731ww23qB3zjLCfgAK1tB/H09rV4FdKjjknuXi4RuRiBcmFpTN7hDozHYRO5p661aazs6YEU5q5Jp2BcHGiIWQmVowz08FZig6e'
    'EXYsOO1l300RBLX04oTNIDLB5+jepHfR1daLKVCvKZyi17Zeyjka7RQ12Ph4kpxhdor8TVScFqnJ9pZTwLWmSE7FyqztJPvlwF23'
    '2yxr82wWq68una65eM3mQrAgtB6vCekW9f93+kOlWH5vbkcY97dc4WRoi+5Tq8sRRUiYr0sZyoniNt3Jlh33TmsYaiq+UltWrdqv'
    'tcGoF3/caLUajc1/bxtZBcXgu2c1wz4nx7ifu7WPqJzYk8a8sK/ldrbAVLSldYoeyX1II1Xc3hxXA69scX/nbGyrm7ve3MuzNrfV'
    '9xff4LnIjrv2cPcZr8PtNrI9j6LNDOW4m9+6ja0OC7ey7vCWm5jj0oHEVIt7AzjKi266xolMRXc6+Bj3Ngcj4OAAQ/WebsCe9iNd'
    'Nqr0X329VfFDS8bosnV/AV8xK8OjMmrD33aE9mYE/2EQek7txakiDg4phpJK4GWPAGBPMZHuNMSszC0rx7hCWcDsMeKftdzIs79r'
    'Ra1ouVUYUngR0jand13LC1b7EBaTicHv4gb8t+4nGyNaoOEoA4GSfNiUEuLibne/W1tbc7NV7iQXk0E8EYewOeJS9TwZJQR00zXs'
    '78soRduQguiXtxOo8hPgQb8DQAIvfGH8atRLrBiC+Chvz/7RzxN7eUbxup4mHx/fx7Oihf+DGVC2VpjZi4diZb8lHg1XxeoL+Lff'
    'bERrYg1KNpp4ifl8BbF2knxAT2cOjbiDMFRv+cIYfYHW76O9AKnLRrH+jJZV3Wj8+D5hpfP6T8lgpN4vIUwvzzLOsE9eUUoC3x15'
    'Rkq/INi6KOi1ifrs0Fo6AWBRCOTXiwIQADdEUDVeNOHn/qrAgCdzgywMJgAHEiXxkTTO1/S3qrV2X/CW59+Tj/J6dJ4OV901SnCP'
    'TaH5Rn0lfwkIOHOsgR1IFPNiXCoHdVc6mQvDKThao/7Ij4V2cDGdc326gwmsuOjC60cgOF/TPxNSYN4Gn5esFV+DbbL2orkimivD'
    'ZbF8F6sdhjxOmSLXzYS9idQbW/HsitJ//i6Kok0rAr4Xq1+SqPmIpH80tlr6kELLgjVjWCBv3U3GysCJ5IfPWxhvmtkYenujvxa0'
    'eSTWLr8a8jz4ytsWY/Qgl1euNQPhgOmTKOsgg6kKtlvRpyy6iRE7vCARbrbEyrD2EA4u+P+3PbE40vFCO5Y5Y1IqWokI5tm2K62/'
    'pm0rlkTzdvtWI07Ti/U8B86g4HIbnFkHlAFsqX1zjGFZ6ktvVMFMbNeJaDqJ/+kiTqdko0OgZgbJZo24ytdiiloL0zklZd+aR0TA'
    'UDhCLz8rvAqDBIM5MmIuCpYVsdJ/hGT/8lHUBAEGuewa/Hi+Yj3Wmj+t6kd4+vXWR4/iIR8SD9lc1kykxUOuMAvZqK/ejonMdLOi'
    'e1k1vSz/9l7Cq2/WYhYGZG9njez+YnvvpXh9cPSHzuH2TtsV4fMUB5aNqJVixk71vd9+drwhjg8O9sXh9n77+LjtZ/fW6oFkiMEP'
    'MnFRC0X6CesmMoR4DhVHQBhVlH+NEq6QSJ9JhOLbxN7PpU7G3zcZkubD9nRkms6KIIElPJkr3JRrHJG3p1Vp9PxyosWfxmeTca03'
    'ia48JZfToOCB9qN0nIwvgPicx6MLOfr4I6xRL+6pbBGav4lHG6LL97fYPl7I4qz8lq3j7phieGG25mdDdIUul7AimxdUyba74s3U'
    'Tx8YMzyIhmWKzscyrYhlJEW1R+JRDdhR0YS/H9Ue/XpLYTL/1LO5tNVFmN7V0L6Xft9e8KsQhBQudKNJrCK98E6VPsxPQu3kRDsN'
    'I+UpLZ9mRfhRYhk7UFsIJNF/18KRNLvMuSjNgZU1UruaWk5dCS0+vu9mVz2N2bRgh1tBnCuX0PxD49lhnBPhdfZgikfRHQznGAiU'
    'csbSHQy/wHBOJhdpf9ZoqJAZzFN8/AJjQUdUJ8RpcDBcyozmBT1/geGQB0/xWKCIGche9mb/DkbR7UfDmeOgQmYkO/j4BcZyFcGJ'
    '2GWaVDwgU9KM6rV+9wWGlk4H4/EwnjUuWcwMqsMvcohbNq6GYZBmDRlDfgz1IavexpMII3F5E5EnZps/fpdzOnZiOQtupFTNNXU7'
    'jceqq1LFPzLn4seba/1mC8/ClWFLtGrrYr22Aufgem291qq1vtxRuIb6nxp02V8bQofYWW1NrPyqGnL7sxS1reCh6KSAnnFmSa+i'
    'xMiOX4L5srmutE+243fLdh0BSxsh6mnmi7pZnPWial+F91KC0jIJSqtGp79i6fQbLCo1by31/TtkmCSC5HFMHb2wi/NLBbQU9+cs'
    'QoplDBXdH4ziL0DUES9mDQTLmIFo5P9Co0GMmmdEWM6M6tkAYwGJLzk41s/P5BOolBlYezgcjNMvMp55INUNgunLDSqaUMDs4kFR'
    'ITOo7Qn5j9yWPfgSx4bkwO722EDg6xMDe7iYLH5kSI7va4rrayCt10B2Fqvw33JtubZaW/31xbJYQ4H6Bepam8jBdFFx2IRiDbGS'
    'QnkU6hvDL8LLWFdleBGNd2Wo5Z2QEncGF/Pw3+lBJVEy76DaMfh0pyfVPEQmS2PE04vuh3j6BQhMfB2jx+2sIcliFh3mF+M8OfYL'
    'CCLTgFmbJAXH+GmmEIINzBJBqMztBJBVkj8aYvWy2XzxEOWRtS9yJzw7I8tMUKLvUA4oX8AnsSQ4/u1smGJLs2BKZW4DUwBm65JJ'
    '4ir82xLNRn8Z76H4X/jKgtcKkcVfqeA6/e6zSPYr1RnCi0tdZh3f1PgVvrlzajp7wfy94BEu3Jl8yEgnwd2j7dczLwfHKdbzNOUA'
    'fV+JqJeOVIfsBmcpwEX5cGHLs3+fCuh5LhYZqC40fWWoDVBSgWZgCm9vA1bUaQyXa02lwyCdBnAEvyLAV5FH+HLwpb5btXll1zuC'
    'bla3q4ErNboubEmvK8pPF8dYQJ1uC1krAdCBv5fh7wZyY2K1tibWEMxAQFbqq7UV/F5f7QAHBuyaaLbqq90GfIdPLaxca932KjSf'
    '5lsM2arkx5aJH7OayOXI1u5oMZTir0if5y4HawNFuX0rVP8PoL6baetB/GQ8ztp6zDgBnh696jyf8wiwljBwP2FObnkr4S4h301Q'
    'zKLTYTRFvRbGETsf1KaTaAScOKVU70KdeAh1xnMutNKXrXs2sJZhATqIL6QuW821z1unNW2Klf5D+Kc2t+FzK88e4pFnD7Fshr1u'
    '2UPMwJjlO9qY/jWPXlK63HHXc2/EGcnH6MVzMYlraTxCpwxg8tCpa3A2icb9a4FMwi22rPh72D4tAce++PsmCrTwat4jeU5SmO1v'
    'GXoDTg87XFugw+W5LL4W3+Cz1yt7IaZXTF6DuWtGl2G0ar3JNUioF2d9gXIJLF9Pjju91b4zZkO2mrrJGDw3jV3xdwnFXP3Y5G3S'
    'pG4+tvipxSrxeRpGVULGjl03jaO02qbH39q4Sy9acLi3asu3phV3gCg5t5UaW+w7ShdlzE0lh5tLTqfiZBij2ixLva+itD83Btm6'
    'oYbkRRqLGVIv+6AqbHMGEYVjwm1hnRtYp/rLs+s7K/8Qycnfk4CJv5q3I15W83dFM0K3wxoP9J2wiwTyZpgpRzJFD1BO2CKJx+Ir'
    'vmrD1sJ5BzZLIVv7Na4ycznWfXxY5voPZZfLc3T5UKJQi+o06o/mU1ravTZlE03ZbXOObpurTr+Lz9VVtTbM/V8xa28PYcVpIm+F'
    'ZuhrvxjX2nm+fdhenGvN3OZpxOc7PBfr8SZPlPfnFTn0ibLCBwoqvOlEWeMTZeWurZtvtf0z94gaBHx76IJAX9OJ8lFlQc7ga95g'
    '3xoUGa25Aw7Wl7sgsS4wvyVAvp60HrhONVymvET12EymI+Wdym9mBR5+SwTp5mNHtwA1ePpfb+pfDxWyl8YaIPKq2AUIXRjfQvxr'
    'kMamJdaGKwJ1Nd/IwfiLHV+vjvf2Fz+9+Joq//7JhT3eXIny8S0UZl/luulW+Je/H/O2o7zfXBQI/+Fv0m+ntw1c6RrFrbrI9TS3'
    '+jpXlPdupU0nGoBaWwD481VUuzUvay28YUMd7pe8CWqK1eECxOeuJDS+Q82/E/X0qva1qij/tDiM/wPcheY4ctmeVjvtl8ftow2x'
    's/3yp+1OjpcVR/CoXU2isR9OPjdSB/s/YbTVTFAW65Pto9XqtrrLK168KB3SZhIPKcmGcbSl+E+AEFf9GC1ITuPX+IP82DOWRYHZ'
    'yBSplttwti/S4lBWxWQywHBPmJURYzFtniTo3RX1YJxA5cYfxTI6/joRddYqzvRO6Y/nFyajSNFUAz5xFsaSW1x0DQSDxx9jPEto'
    'HjirfjyJN4UM8IVvr1OKeYkZJKHU4AQzlFpL6wNkiM3WVLNZcEQnaTK8mAI4kjGMmWJRNTZJ1QH1ODspByDSU7gcYLfx5v1A5knK'
    '2MiD3aCwvxcTTGgEp9J5cpHGS5zpkpvdhPdX1ny8SfCY3YWdd/yw49JkskEZN/vRYGKFSbLXzVLk0Wy4k5ysmWpT8bC4B8qK5Azc'
    'QUYqU6PoOPkDVzGIMBAPDX+18TcGOXmMgLLxP5Rr8KWSG+RpdbVie8N7IX7m831X+29ZpXRwPd3pVQg3PFQI0KKjvR+fHwMpOtg/'
    'eHUkDvd2/tA+Eg/E/vbP7aOOKB/2k2mS9pMxQCsdDyZxr5JDr8i/M+AW2uJMHT7NaagpEGgtt1AKVhXP4xaaiQXlIoSMu6tm5icq'
    'CCIGLhMn9nZoruklNz6VHPZ91/qLIm1FJ+IkmoRoQchZ14HUKvy3Pk+nWfNDNaVxbRqdKEtAy3aK3mtLGtsyDovCoJXdKHousXtQ'
    'wEYx0FV6hXlhkKb5veV0oypgTx35O9tZwLaOtj0s75E43n5aQGuhd4yzp4DgpZNRaVLEmhvcSnfx7Melpz+K9J8uIqSZD8QZ7jq6'
    'IWaS80D0LzCHw2Tg08qCZVbRtHKO76w5pjUSeQQpuGU69dLmZE5YGUNnxYRjo9+hU5IiDbaygNFD0pAJjCK7CmcSO2aT3cYmO4w3'
    'NhUZMaOl34FjXgX7qK+aLbK+vq5OHUkgN41ljW5C8LVSGbP7oac3Jk+r+IwvYeyrvXKBIaAzyVKljkaoaTytU/OfP5fkSBHTA0mz'
    'rXVWQC3zBq3MA93TOaDrnMZ5kA2Asdvt5oLxWTKJXTDKQRdP8igGyAhS1qQCs9bkz3EWstTQ+Z/xhX6aM3bdjaIXPiP/8s//b3Cg'
    'WZKjB/+jogEY0xpO7CIaMIMKrI51hIbQJvPYrXENyY+luG3Yt9yreukznFY2Eo530p4Mk+6HILuVP5Y+pta2lchFYxmlNc5ENe9Y'
    '/AM+b2Sh/POBpaOFe97+B0w9Mj+hzomEuGpi4+KeehgikTmhHR+5OOlFkGzUV72gk2sUFfh3Ob4GlKpMLUkfACZzl51HH4fx6AwX'
    '5uH9zFLm5if7XTNuxq1WYImWI/gvViPvreN/c7KvXmwom5vNhm3C+MDJxRQFbblBM6O/jIYXMHpCmgjJNM3ZJtPPJsn58/hjufS7'
    '0gNUUtSpSiV8rB6wfkqkQ4xRFNq/DGS2JQe+/0zbHtekbqvGdQHsqBpoEvhRfQ67Uw0Wfuctg0xHhYdw1EUkq0kor548Oumt+hvB'
    'm7AcftmZqCLO8mMObnqTuLSC3AbxFU/T+ZbcBP0inYEV9IvodE7YvLzdTJwG2cHiiL7EBl794hu4A1UL93AIvbC/MG6tGtRanrW/'
    'g0jloxGOL4xDBvLFaESD/ao4BLRiLhTKER46r7ePd563O3PKD0ayCQaC9tMu3p+NoGeTQW8T/6oBeo5Rm1Bj4TYFbn0cR9PyerV5'
    'OqkQxi4HUdS93/EYQJuwN+jPpsvVUvFDeAJKyQVyedP5e1qmPwU9cYE76GmN/hT0xAXuoKdH9KegJy5wBz116U9BT1zgDnqSYlN+'
    'TzOklfl76j1aPV0t6okL3MmcZqwTF7iDnuL1R6vLUUFPXOBO5tRdfxgVzgkL3MU6rUTrK0U7lwvcxZxW47WVVtGcqMAd9LTSjU4L'
    'occF7qCnaD1e6xZRWC5wBz1ZR3i4Jy5wF3Pq9dZPHxbNiQrcBYXtrj7qNYsoLBW4Cwp7erJ8WrROXOAu9lNz9dGjIlrOBe5iPzVw'
    'IYr2ExW4C9zrddfjIuhxgTvoaf1kZbVZRI24wF3MaXXtpFV0PnGBO+ipdbpyunZS0BMXyOkpj7HNdbqlCwg0v8Gb10kyTEU0HmP2'
    'gKt+PBIRWU2L5ORPeGGP2fro6j7u1XOvSIgJlzckllmR9daOMOB0XRQ20zSgsmZk7xmeHAciD2eEEGrJ5L5TVrpyYoLuXXNvF6wX'
    'TmZ41a68Tffi/Zh8zlM1XyzkjNFJJe/V8D3QtVT2atzDjJVy7Dh928BK6zSymdvzIOzbwCHs2FrDniVKZ14MVHgjWF4jzO2jkJo3'
    'QqzujdDfLjI4pJRf91Aor4o0GqWwcpPBKUbtm+IycbkZ1bdhoEO3Or2as7ovfwotgOLFl/VpzvZ+jJPJ2SCCAfFY5PO8ozkeYIpo'
    'zDR+lJxHo5Jux/swZ3s/xZNeNIpc8MiX4SZgc9Byem8dPSNvMlQISK3F6ALTYkkVxbpUUbRQOZ1O4zFpLeSAWivBqDg2wZANW8aD'
    '9CYT8qZwnyAWokojHxOze36+HZOFBOoqZf61IEDI7YFAsqwA0qg3Vo1uEP3wCqBC5v9Sv+T6BKiXi8EGx/uchlu0T0MTdVRdwbnW'
    'VuVUzeKT36icaqNwntR8dqbu6wXnSpU7XPc3IgMnmQvhhDSls2F1AsT+fk4LgdRsStdGtWyg0JtZ4Z7cOWPXxEHIDLpPdS7dnEA2'
    'geEPphF0sfgE9mQ9ewry3WKT4AHQNOLzJ3s/LMHf8w+ftb540bn4FLaxruC69jSs9/lTQU2qNQ+qg1h4OuUVyRhBrsD/QqaGs3xz'
    'HEPptX5zTZqrN/DfFfm8Ds/aRnFR6LG2/Lbww9qTOARB+WVRGPJwvjgUH3pQfPgboTjhY+F2QJSVszDkD4uCkGp9cQhSKg0bhGSn'
    'OwcMswdOxm7Jfstwkw/yfPmdvBScxWNwLD2Xy5DvFjtfLFflnGM0Y2ZNc0Azk8IUnaeUysPpzLJlh09SeBtJO6T7T/BlMHLWHEKi'
    'tIyTdn/F1nIF1shhSz28yJEWJo2Qidxhp0ZtsnQmMHks/HM1ALSSV5MF1nO3MJhTVzVo4LKesXy6f/uLxeJUmG4u3UVuHI2paDYR'
    'ZUR/sreQa+rKzNisXqDzQzdK0eiF7JrTnAvJBe9SV3IMxOa6Pr3/RN5Rh8dSeD3KVtTBO/jGvHfw/i18K3MLvxI9PO2tZC5Mt8nK'
    'ieAYvILPA0hw7F/m2pTzdebdtBdZzmSu3zlTs1DH3Ih8jDOX8PKzJmIX42ES9Tgn0d55dBZbNEy2SK+hwWkiRiDcElj8VXJWKJPf'
    'dnl9eX2lETBZWVlZUeA7OTnxTa9nm6F4Fm+L7n5vh9A+ZAM2M3rRqDfTzeyZQ2b5aNr/+D7hFEGgbuo9LuHsSvd1UUTLvJIMoFKA'
    '2vhcQBOjzRjrspYbumhR5gCdaIzTcdOLzxJ0OmbXJeMRhO5ty+T/hrH3VtALLieuwVp9tTh8mBpxUeRxGydnRmPNsSpgj5HhIJ2K'
    'ctqdJMNhWpnpCYLFfT8fP4FRwIg+GBTfOVL5tBEytdHMcegUSDNPV8pBnnu0rshN9dtOzOKDmYCNpqySb4hPTwHVUrEk0DttMVvs'
    'oI1zlnUbjmvsImexabTe6Pv2aox2wB/Lp3E9MmcDvLFNadAtiDHkWTK5iia9uQIse/vSis3VXL7NvlzL8451IgYtXz56sYqeprwB'
    '86MgzxuytxB8u8nVaCYAOzHQTIYfmm//lQOwufzTygt0Xxwy/fpCIGT1icWP/DSw80XzZ/ET+ocNhiFrwG8MsZhjy/uhjjh8zISi'
    '0hXEQ2rdntzPGddZWawT601cygPRA8Fs+vWIzHavRytr57qcxCCN0o0Affomq7o+JyFpNl4sC0cH8Ft3gOCfvA4OrHbplbUdLKDx'
    't28IsHkIxzIGPmi8WBOrPy33Vy5b8Gv9chXVKPgPxsWtrwMw1+or+xgj+Ddid1g9kGVx+DfthCVKWHiVTD7QeS13gV0AFicasy+E'
    '85pyB3Myxdp50ouGVOQ7W9uenvKX+5aPaTceIotwOpich60vtSNp07VxHJyyY3J9CsJ3PH38+DH5rJ/Gf4jjMcolcB6XWVYLjQGE'
    '9Y8qgH40jCfT3iAaJmdSI0dFZAx/S8U0jHsn1/bI+UpbjRvEUp0P2bITDXbPqhAfEvKKfHeQdvEOOTXXyXwzm27Z6UPD0+pdh1I3'
    'I4WybrM2AF+lBHUZTco1Vl21KjDmn5ML0cd0pogF5CrcRwMCMxRa6rrYnsTiGspiYE76cRVhtLZE8FxEBOc55vMVg+nMUZ8mydTa'
    'th5pMJPz0jV7S42PQj5nvPXzmxT2Q62HcHZDGMrl2OElwJ7UAslXbmd6svKH2mqwGSyF3OHuM9H+h8ODo2Px4mB321HK2TDikUl/'
    'dMaXce8U84qAPKP206xd0cWFgB5fYHEkmqGdNr/gm9lV1pZyU8c2bHm8ZamTfui3zLYht32kyeuOj1eTHTf/x7/9y/8i2jRfRC+Y'
    'xg9L/ZZsZhxopdVwm1nWyhYL15cR12Wr15QtA/eeGKPOAlEXBLzBWHVY/2FpPEcu3qyClBLYNoxHglQRthzF2g9EXBQscXW7/WQA'
    '0hLdRzpasm4/7n4gOCtEGIy6igzRx7j3RBzTVA5hKj8sUdt31hNDxeqqQy+cbvzNXuQlG4xmAZLAZh4tAOHUIwM+butM3IUEQLYj'
    'xpMBLM21SisSw3B6ePVAJ5LaZTB7q8NewmgDfWJ3EocILechAzYReL193D56sX30h4VpAEVTxSjYC5GA16rWVycErcUIwVqYEPyX'
    '/1PoKcwgAk2PlrRyiYBuEQ3lktHwWsiAG2xLBxgywhNFJBPB+MBZc387XVjJ0gXHvWRRbb3vnJJ35xAEBZz9Rr+8zi21R+gv3cuk'
    'NHeoyJSE0Fp6NUDTSIf/zKcnV7C3uHHb7OyCruH0epT9OENW9iXVK98MPMlmXXfonq2hh67TaTS9SGujZBqHeKVmLqocPHvm9uTy'
    '1C67vSD0XRdZFy8Y/0NmktbVKkzMzjLEv+UFye7R9rPj+66xYlw/q4udg5fP9nbbL4/3tvergopV4eXhz7bmulBLz7MALvAU2oZ5'
    'ZLT1XIBftyqZuVecnO+BICir2dPcHpy+u8nHnq+0SkzV0DZtw8M35T/3ZG1FO7YVr6Rtgyevxuj2C6/y+fprzVx/ra3cD6yRda2V'
    'G9nAGlypUsdJ7jCFf2wuvB6Uxh9Lm38l0JUXch6A7cu2Jy19KVYMYlkpBGVl6rZuYNxq/AYYW+MrAPPfzA9l0pBjHoTxJEathh+7'
    'JzdEiLVxr/qDaVy8XSveVrQii9AR4UfZuuVFWii2GEBNzq0g6sVglMZoenDLfs0F+iSBIyEu15ZXe/FZJRhOwr6lf9RozHlnK28p'
    '2XhlU+LBRqPeskgaEoVNWg265UfveIwOt3mR4r0/2YmoiBZEoH29ToFpgewePeeyuHD/ySFDOPdM+xasfIZHfbKDrxfl52c1uj0e'
    'D68X59gPXuwdi85O+2V7YZY9OR/A0gDqxQvx7AdQ7Wuz68vrdyC3/+W//m8CBw8yYoz5iovZ9bV5ZXYZhTISBEqyKZIMOfHwUUpr'
    'dNzerYvjfixLsSUzMviYSyaeXMY9tHgQ036s3DrwI5MxMUA8SnoXxLJLpj/1eH1vRZ1rXlQE6sA7Np1UF77uyUaiypxCAy/Ft9iX'
    'Nh6GtuRi8u7BT+2j/e2fRVmRJVgQhBIpYKosdNVQGKtkdpgr/uotFnTdVzTvdPAx7unjIkTelZ6ZvIzn31LBOJOBYTI3LseYe+7c'
    '7oxZ/OgIrQ0Tteft7d29lz+KTnu/vXN8cCTK7FeWCmAZ0Faf1WKkJiO109KYrXxOE2elnKaP2hgZFXo42js87ixMOGEboNEWd50u'
    'RDyPqCorqVKJvZtfjYyutlj1p6nBw8Zlf56dHrg5cK8N7sRsUdF3pL2kNBVNEyYsa2TpMoY5FhyB88E/GbIRVP7HvyGS0FIBdifo'
    'tJia82JeAhVa60xQwBUTxOP3v/vYethc3RRFxMzazBINeSEceu+Td2nmo+GL0WybaxnVjrqLoANkFF3W4vPx1FAyKyyKXE5t2IYN'
    'IuBeJiKN8CwbS6iJa0y0PIt/yw4saPpTtODBo+b+wswZGhHyillrpYOmwQo1n63stDbFUwwmFwugmVLj/Ps+2RZszscWzoUqQcVx'
    'zqlmU7fne7u77Zfi2d5+W+y9PHx17JA2Wwd2OtDZjOGXCuilTdm73XgMgmSdCV21np6eVet/StF4/PxiOB1geqQA5bI1aPBPbxg/'
    'g9b3AbImdHPeMEAQxLjN9lD0MNRHGMj4vFetT60TbEb/siYb3c0cBV0uUFEzDj0K0r3nGPYWj+Jw99mcA7gCFPdHoAcAcn0V//pY'
    'hZMQcChCQr10nmIl59XlqFdPxvHo4/mQnUDSWnJ6OujGWjOAVWCnduMUM1ufD+vqy5xwfQ3155zSae9jPkzhozNyGHEVqQ3+mHeJ'
    'd/9hXuBO4Eia9C7i0Eiuer8yijvjybz4dTCeF0TU2y705g8PWBLeWPBzaUnu0a/8P+xYdI6BC/52QxjGsEbRSSoeizdvN2kc//pn'
    '+J94DQxwcmUCCvDrv7b/WQMms60a0fUNAWhB9wkY63xyfYVh3EFyQzQT6RjOCpFenJ3h9V4yKpzad3q3wiHZRuTZh6MeTugJugSN'
    'cJvA14tSVZxejIhpK8cV8QlOCBjY9hC4ALSZoC5r3f5gTJfJAziZ4WHYm8QjKDk4FeVYsqt1OpDSabn0O1OpVKmISTy9mIw2vYZj'
    '1iymKJXCxIEDvya5FyYOku/EQKSWfMjt6Q1ddkbYZs2a01u327iOCjjobDc+jeD8Ac75uxv4P2EQm3EeRyd7PUCk0cVwuKkwawep'
    'P4gKj4FFoXenANE07pFfs12WOKkdGAYqJZ0vFyNmax6L02iYxpvfwSjTqbg676C4BK8/CXl9tMElquQztSFKJOWgbz1p4ddWqsrR'
    'aAOzUtyolnqD6AzEp+mga7U4mSSTdAN2BbnmAxpt0JCqgkI3x71taSO4iyJbpT5N9joHnemErE+waYOaiJ3be2K709mD3Y6iD+55'
    '81GOIhpgxwhqdzLwphefABi7MQYHUOOA19IEDUGpXmY7PjyU/ZVB3MXbyrQqhiDDjeBnVeCtV1rJjmU81qCQOLena8GLaLAvHzYE'
    '2kXhaFDK/CnpRicMl04MOKLeH/YxnzaDE+czSM8HKWBBx2xDrxZg2ymsQdz7KZ6cwMdPN1U5EOCpER9wFPKnGYN6Q4ElLqPhhli1'
    'X3vwg9Ze4vzhJ8FBDQ/eH8O5xWcVIiZ2NtVvgEWMrcWB0s8Qp1VBQvBsGZArLnoivR51ceXwoQO/DyOQDEWpVLVftjMIoD9lZ4Bn'
    'HKq8gMMF0oSTpR/RaKqbUdAhkpJ5ezaJzoFoeO8dRBJ/iKW5V9qHY7QLB/skPoNeJtfir+gkeEaMFuAKsBqA5HjnW4W9Q/QKZlAV'
    '3ekEN3B/cDqtimiIf7FW70bi/W772far/eN3necHR8c7r447eC4CjLDFjRKiEFAT/kPNb5Q69jv5B7vZIDAK7mxDkiXoUv38EF9D'
    'gyU1gg1Rrjx+gh0oAUgQwpuOt1PZjdWx0C/zOpYP83e8nbpdw6YEuu52jbbIXNr0Pvecp17XyCRDg1LSfz34FdDMHQKW8MF+YL9b'
    'dAiJNwRb7rQ7PgUeyO/4GbwTvxdHMd2e89e5O+4H5o4Nytbc3g3BKVVV7xZZQgpD3c/d+wevd7aaOHbomgcAJGUKAgoAROt074tB'
    '/pdfgmN4pkim2308bJo+FNqTBv856/nl17m7b/poH09x+uUSaV1KXuetbOcXJ32n50U6b+V2blr1RrCcGcE2NeBi/twjWM4bAb/0'
    'e1/J9L7TjyZQljBy4d5X8nrv6la9AaxmBrBLdtkXDsWdewCreQPoqVa9/tcy/R9StqJ+DKxiNFwU+9by+h87rXqDeJgZxLH2ML0F'
    'Fj7MG4TxW/VHsJ4ZAXFNHvmdewTreSMgHow7fys5f2AdO5LjkCIq8TyoYp0MenEqkHTHaIWenMNvAB8GXUOvTiWPCZB1dBNlLZu9'
    'iEEIUrxBykEIsDfTNJRj6SfLFNTPo3EZ6orHT6g9IZh7SC5hjM6Y63iElC+w4EV9ACLM48fYKfysbFJF2QXU3AJ41+t1+FrFf+HN'
    'jdjQ71CiEAIFrhszNZz8K7s7OT9ky+xxIehs4KBRyt40PgfSc1pTHB1AnoeEUiKIBD7s/65z8LIOmJrG8JUGI7oY0JAE3ht7WMhM'
    '5A7LHUgaHEiVO0tJmhqcXpedsVQqm5m+PZnn1fHBzsGLw/02iD05wlZXijaYK7KXXI0MT43KfPMkrT8tXpzvVKSooEIp7vU+boha'
    'k/lm7uL458P2u52fd/bbiLnyiKna1L6qCG/VooFVQ46qHmWo2pu0KvfL2027v/3tp+39jpwbdQnShbzM2/0RRWHdPX549VRe8Vl7'
    'srS9c7x38BLe6EHBy53n20fwoX1UYgGOh4gy9t72/sGPr9pQ3nJ9F6Xjo+2XnT3ZkhSvSi8PjtsdagGnXjuZxNGHEncpnh61t/8A'
    'ZTHWSq9GTB/2e7C/Kw4O29jKNMJBH2//SC1AA1wT64DAcxabqzOsCQv/Y1vs7h3VuUPgZGtQBz+9bL8WsmI86qm37Ze7/BZL9y6i'
    'YU2vBM7z1fZ+yV7fzrN3u+2f9nZwecuA4pIYIN1SRAS+lEqbGvWt17nbcRxPSF8M0j5eLuGZ9PkztuLhvNrb3QTTVT0WL8mmoTyK'
    'LgdnEbRbh7XrXQH67CQj1hN0r7GlFdq7XPc8Pk9gYIHKvfhy0I1f8Heo1bBq4fbejaYR1Lt3z1SBjyMG/lZdFTGVUAIH2WzQ3U+u'
    'oKJuA9rmGfzwWKzgU1kO6oloiN//Xg0Rv1YCrT0fnPVxHE7zUI3bfPJYrONT+d65nolqHj5ZDU4HpKIyCwR0ujRMrkpYxX3bhy4D'
    'r1Hi7gHIS0RDt/RXeoSDzhnhlmx8w5vJlmp+w2rQGuYkSaYwTK2UVD+khSEWxCJ1uu9CTWV9EqOTPGEW6vfGyRUxb0RvZQfOS+xe'
    'vqgEmot6vTLDSgNoS7iNw9hNCZ7Nlt80zS8zAtOhSqhlbYZjXiFsetMczQcU07Z+OonjX+PyJ/oMwlJydYgt2iPBsVYFjiHziQZZ'
    'ZZypSgSpahStmoWm47eCmk9DAg7bR88Ojl5svyQ6QAQA9assTlqnRtSLxuSpmlxZb9EJjzSkG6JRVRTbeQHj7kTn4yGST3oDJDMl'
    'AiuJkTl2T9sUGYE7oVnKg1cCSxOsugIQorE7h7o1TuQ17ObJSO7QLAmI7HixIzuZG0O5YKzGKhc2PHqzUczgNQp8cUz3xliE8oGi'
    't8R9MwSWjXlGiFPS5gXG762ZhXHz7CFnrEXljwjVoIbXH6MgUesATsGM+figqfLPWjcaRxyVoFTx8eoohv2b9nclqlgYVp7KKwXr'
    'gsHGNp1oGCkDyBDJKbL7qA9Pd8wnXAzVHS5Ipgh3UxEb8tJBNa93JzSvu9qq/9NFPLlmw8Nksj0clkvykp58vUuVOmfkonPTOjb1'
    '1l6kNb6c4VtUauH+27wOLCzA/WS6g7Ou2WpgaTMhfmfVxnuy/YIWWivZFuAdteCjowU2/TtQzoGIeQi16AzMetqUt1r3DB4qal2R'
    'IlA+fYOm/Fln6aFFgHHKyyT5ZEc4ydkqVneSMSj7fcJ+wVfuHsetcw5tXkzinnKkH0ZnpYriJ4ZuC5nKwX0niqi4dax+MutWtVam'
    'aoPePmbDxPuGNjryw+npoU1VaLvTTQZfC1q0oNPtx72LYRwgBrJeAU3ACypsNrmYlnO7lGDIHxDqI2QjzNUXUij76hOwhylJVSyv'
    'NgJ0DlgMGSXtdTL5sHsxIYOGck/+eJHyRBCjzTveaZUixHwsXkTTfv18MCqvVYsKPhBNmn88RFd8t5sfgCLM1Uv0sdwo7KUme5mx'
    'MyVd7CcXw9427pPs9gnSoFxyI0nSnLtYajqs7u89Ltq/atgzSIrV4Ga4vKYVdt9b4f2OW72AGC6w88lSqnj3M2W78dD2dT8e7fWg'
    'TFdezoMgzvvj8WqjYTA2TARA/JIn8ySGoy6dYlPmmt85mxWEJRUKVLDG8EmNgthyHrqsaO1gUz6PwQSc2hBys35TS6C9l3vH33QE'
    'nQFuEDFNItiWo2Q6OJUWVxY29JOrY/xePk/PqkJRD8Dl5YbCBSkIRFcv4jRFc3DYVGwXAXXEFqCsLdIO0jZaWkChpV9OymR18fk0'
    'ApTs0T+wHz5fjKJL+InX05+7uGNwcPj2hEZb+eVkaVBHZ/2y6VTTH9k+mrIg9d3Vph702q8hSZK2SoBhqQFuqddxjy9hniWTTBu4'
    '/0qmIWmdFvcMKKy2YWvcW9KNKv1bYC6Sc3j//Sfz8kZ0/Jri+0+m9Zv3klMwVTaldioe2hKa76AI0gZhQMmQ8HiodqZbtUuhqWRt'
    'vEa5VKQmHpK2W5jW9HvYnNtTwIeTiynINhhzR+rvphepVd0txlF3BnTVXhonQNXi4rLRNDkfdLE0XknYZSluZjdNKRb0Y2zN8Qqx'
    'Y3Jwrmn66QRIXIb/tDMf5tbTJtRkNr+ecVpez7oz2R4mj6A4WlNHveRqoyFWpB22mJydRHDU0n/11bAjoqVzVUGUG/XldFMCXK8V'
    'hgKqo/fGqLeDtmdlWFRFNgEslhcqrrCHt5bmbTQiS6TJDBTS5Qwa6VcV08oc/eo1U9ODNWvyHrP5PSj2bqr5O/0U4uc+BdtsoIq1'
    'am13zewoKlcVD4nIbWi6x6dGgY3g7sELObt9uqgChFSaYtJg19X1QxE4UUfYTZA2T+OaqsBwhRYoAmlR7S65J2B5bYgEzJ/uGOP4'
    'XkxT1G+RqaAyMUwTIS3+lJmhjAqc8m0bTDEaouERGQnwuym52BFnwjzMdxYGZqFDIW1pMgCWuGKu04jqWNCpS3k51eaLlQq658Xb'
    'FmgUDwOjP5QDB5JwkoyWVFTU4nlItxgcOJ0sNC89nKzdZD2mGFFVAQwd/SoRt2PZNxqOMWQ9qfktb2XYw1CgDWZocYosUrGID0to'
    'd5TUkrHsqbABMsmGBhh6znLYTlUKBlt1gEIX2foaOg6jwShan75ie02eo5kdsZ7qylWwUTyZcVM4lZE4HUxQiwH7RBIMyTdyLBG2'
    '7cowjPbHcglY2XNDcGT9wWgwfa1i2KGRSaaRTIlyqI0OrAJg0REltw+24ZTgNnBVOYAj7g0sNIiG4mQYjT6grChgl+EH3i3odDpC'
    'i2VBvj9olkjWV+XSq5fHe8f77V3pNYf2xnyjTv+onvagefFrAkiN2I5HKl4/vOMwAv8I759GExMetKxXRl2bwmaqIZuE6ogNtnNF'
    'j9rJ9ARmALIjRW0ht5vxZAB/dydR2l/AABBpNjaxg/WOZEdoOwsSRpkaQytfJNBEAOSbCo9ElX+uBlTGe2A1dWUVylF7xIlBtL/8'
    '+V/lVBDQfCgMzs8B4gCU4bU6nKTBa12ZispeVbsZYHVA1BgLNlcjG28sDW/+WswhhQgb1pH2YzQARmCa1nGz8auo2by2Hs089yTK'
    '7hy8PC7tLr04OGqLcZT+NTkE0DW8PuMZ2/HU7b1IJrBFVhoNe4PAZHD/prxX+WZaBc5wNz23JDc1mbzICAmZzZ9bUlvJf1vR8nj7'
    'aefbjUBLj5KakadwVUTph5fROcpEbDWE+LpDXt/S0N9ypLiKrlPB4oa9edluJ9J7fYTt4YYfJYKixuDRQo4FdW4JzVIwJCVIg1T2'
    'chBJsqDD/fHP00E87GEl7lQPmy7js9RYj91T+vVQ6IT6chNCM0pamuLPKvcmzWPwTY54BN/4XONCqGVE6YHVp+GqJlApNPAe7WWV'
    'XyjIidZcRvS7V7p5b0nAdMDjylDDzhUFHPnwtkYlzFlLj1qxhw85M2HeSwlkXNKfTrgFd0LMK80zI1ef5a1nLtpJ7QQKsQ8eGD8W'
    'S3HBtOQnogdWK1towHKpLvpYLWcZGsCZ/1gaqMsBoP5SOZog36SdWHqDCXqq8O5AarLhdHojVz6tjy9YLe6fUTBLzfPSTiHixdeK'
    'whzJamDtuYR7Rgm6pZTbl7DTfFIXiQS7Qc98GIyAyXx+/GIf3rN2wg3iBlglQ97K5byxQ9FkyhKO+L68uLDEqla//zTo3VTuP/n/'
    '/nfZyntifufbkGbQsnm08clIKJZMoO5staBSsjYJaXoCAgQWwSWp8ZIg/0zXCRJBpZHgjcO0++IdIkBNXyeWKo6MT1PIYIWhdR4O'
    'dOU2mIkDVNDFAUsMMCUUKtDTnsEH7u4a+7JcqGBqzy6Gw5+BwStb3QTQxvKX535xNkF3ev5Mi1r7FX1E/UhJTjmZRpgglBMuLNCu'
    'dGSVocEU7nrx9fioEHRw3GdPHOKFH9+n3Z5JWKQjiSVMV2hMHGG4TKhdFXYWIrFUPNITWIdeDZ3HnVE9xdckZU4GZ4MR8HnnGKQE'
    'Gb4loT/iCTmCZkBwua7X625nGWCjMwHIk7WT6/tPXvNvqOeHqQqMEVjvfjJR4HTG+TPG5EXkEIhvMwbQm0Sn2fSd2XJ0xodSUAeR'
    'YhdbDealDkyFhxCayTOScqkxZxozcpPeasSwlL99wN9/crwc99FwEQ2jYqnUL8FS//gUjuRP50CF+hulYULuEdewjTdKIyAkk0G3'
    'dFO5+dLTPYrRVjcZ/fYpAwdZPNhQ8Py8SRBt7k4z1Ce3YHbW+XPe4TqBTOeBCasOQlMmMg6c9hnaifqTX7Ct7V5vEqfpb2ylfR4N'
    'hr+xjcM+hQVYylm5u1oFcj1Pf/si/Pf/CxjZ68kNajOAEmZp3eJNvv5xWxyxqybf1P0uHxyZUDHvCzkPTA7h8RtdKQK5mhIVJGoE'
    'B0gZJDNm1Uk+I2EN73VIa8PVfa6EK87BlVBBhyt5Ly2p6Mv3nxwmnfhzaUQCooJpQDEtys6EWRb+5vAibtge2RFGDSWbLVZwIv2M'
    '0+7z6flQmopIRSZKKqyuvLn/xG6JxAHD0alY5NGJ3RSwhjcq8Nst14om5Os5e1fnpKY9TnYPXmSVrUbL4hSs0v05L3onVnwkTxdb'
    'R7jLqHz0SfZphGabodTWlyW5Ntx0gDGGQqhlL6MspTz49J2l1Thp5PejdCpLU6GMolprqKVXvdJQT1lDi4egFe7MBZuzsmhFUsL4'
    'aKfQXU8bNei1yTf4w4ZhlaDjdtTtl8dnRt4ABDzTmClH9tjpV14oBEReD3S2eJtKOahDanTXqIomYvPrpCRLLtJjkmFJ8iT3Jrop'
    'mCr3JtssS62GXRNkIesRa3E/FUuyUpr/fkKXE+QpkAGr3co7VbQzisb4G20sgRFRct5PyCWX7faAX7mRSgh2zrD67ez7veGoO/u4'
    'rbCu3/f0ojdIOtkRmBpl47Mkyu+kA4cz15PeHLM86RXOj9uwZma3DzRznh5kseJ+ZCGrJ7uRIHoiwQsU0mRQ3UW7oURs9NNfCpBP'
    'bm6MsiA3N2n1zX2ObmRLjQBWVr9U7+499gZvrJgKb6MYg507Kb/tKulz9NW7tUIYinRqBcSABrbNlL2eigpn7iqadbH3kkKPbJAC'
    'Cq3Rh8iziAfydE2vojGdxecXdOIO8JY0hhFj+pNrEDSBepPNoD6bi8gZaSs1GZv6bpLKZw5Va1NHXaQJDmzKgCG8PBCqugW1gUOa'
    'QlUGzeVZUtG17IvJucgygMimy/6EBinDHic09vkHmpODZVt10sPRRmRVodxDRVNWfaj9Jg0YpMUE2SnJQQBvQ7wVMThoI1La1He/'
    'iDQ0KbwNLKf6p3sxHACFfcurAdEtAkQ3q/3JBcVjHxTdBUDBVl7ylT4uuxkASahsegUu9YUolpHunplSGeMT+6O0y6HLdDSTJYuN'
    'QCm208ECKup2phAFpc1t4lelJrc/3/DOLJi4RgLH4MAhh+oO62V0yZBkummoF60TUmup0ibgy3svst16ylo7OyAOyNcUwxeg4/fn'
    'kl2DBKp1RUoztjtqltaRcOgLCO59xXtnH8uUo28UV13DqHSkULv/9r02lIUp7CZ4N8jmIdLGhTLAIDNInuL9CGY4BFmkd61iQtE9'
    'PnG6/di0BKwjsJXIkJrYnIq6Ujq1ngx1JDBqHYYJFJOLUVqXLRi40US3jI7ZWHLQZ8nxO2G78E+Q/xVo7LTckAeRc1y06ujy3j46'
    'au9u4P3/5bW+LX2APr7dDzB7XvqUDg0Yrb3W5pCQFrzbo8E5SZ/PMFmcs5LZ61bk4wELlYSac9UqS5WzjI5MmpBMemwUXtSMLlXY'
    'DqbOUm3lt6NLWXZIGC9DQ4zyiJnEeRGsPpqlwxeEId7hCEqO/nHKSfWkKfQsCAYGjd0ey16L4WiVLGvkt9qjyDh6zM8mybn0Wc60'
    'l1sy2K53SW9p6nLGqUpqwynPuEii7nJdHMUI5FiMUT8PhIZ8zMnSjRYAeVoymUMCIMqnsC3QPV2AGGtpHjK0ypOUNH2yJRRL9gkI'
    'JEA7P91YAkcWKLliR6rEjk9acWPelu1Ow5IIdk1DldeMdH+uQttxTDgMsCZu9FLdyJMlI7FIMUWulT1hSzbhP9aET3p8qPwhvsZa'
    '0mv3Q3ydSpml8qbxVtdSTnhzyi8KKE6rsrThVeA17hmZz1d9fwOv3+pZyxYwgNrZyJJyshKQPW9PYiKhKN+dgtAH72/LGKYQWUS+'
    '2+V5xHB4J2PoahydsW9Qxb87zhN9po7EfQ+vg61zYKpPWepNbRuZM3p6OaWQzFJloyzHcm6G/eMVCvBxykcpDUSfplQ76OUoO7X4'
    'SRyCpmvwUMQE4mfFYGr2gQDpEgbYDFdLaCrKkg4fWCpcpnBZJbRsA85sIP1mLNdN5B8WYjN8/sIFinXdyq0WNWtYb26Un0PNkheO'
    'GasmUuZVEUSzTNhmprrPWmbq5EkfykxET9k4gak3842NpQTruM58snhE3fQsWcAvOUMo8IuHpQO/1AwxIVu8SF7wS+cIDn6xuSSI'
    'Arj5ooSmI2xhbeDG78tsgQ27im4lUiFNsSuZ3dlWoWxlDXS2GEtbLow2OYwvMaOwuiVYMhZbJqQANHF0VmQLr+Ll1iZnRlXM1Sqy'
    'embKAQTbknCQ3j62hiotHgCW0J3D/OWzBTc0YD2PRjCvHlqx2rqkTc5HOZEMDkkjg5HSSlv2i9ldydJWitPUVuGOJutqMBxCy5jN'
    'G1XgyQQD6bjLadTAdBAqFZh9IOEB9YTOGudQUrq2zax6zG0MDn9fZ6gNc32FoaNIk9h0PerKywdGj7/883+hU5OfylrOQrTqAXs5'
    'lbdQJLZU8qBn3BJn8+IWZSeLjT26rnts7amtjDldxpak5LDMXmMVEbAIkYyEV1Qah4TlQMMvCMuDsshY3OZjoPbzKOV7yrgnfVzI'
    'Bi0nPEMw6MKWCoRmn7PSMatsxUigazd6T7GQKnVJT8pLv5R/qSydVenldDI4L/vn6284WXF0oSNbDnB7Momu6+hDwksUYnJoOSma'
    'Poh7EcdyevOWHfrqaQLoQ/fMiEFSScmGp7RwarI8L5IFZpUhD2YuRBMwVpG6jO3n/xSocRyNyhbgKSDTpYE2NYMuwhip2EMCY3FX'
    '1Rc4hRwsVoCxZXT4Gbox6DmWpVxnq04WkaSMD6KfKVpxfcwZDI+t/utZe1FF2EqGt7h3RVHw6zIDdPn9X/78X5V911/+/N9IBaSi'
    'k3PmgbQuvXgGbHKJ/snwHTrdeu8oZrTyH6Eg43ngzJtq5PgBpCJyb1fh+e33DAsdE93+pMKlI4FUYQb50py2YFmV06qg8H2J8IYr'
    '8wTIdRtOcQ9rEeSeWbV5BQW5u7ZU6J7iykXc9WItFW37YEuONkArsl1jTYKpvZg10dQQJvYqBGR7NwGF3DZqPjd0062gYg2ZJgXY'
    'bixJFmvxzhvMNieVmO+zUPHODfcK21hpGO6BmtycA3qerYUzOlu0sgdEB88OkPPp9rSMDVRFcnoKzLeJhHBvSM5/Zvcol/gRuYB7'
    'hixHdILbxyCJmZL0YPhSGrBHSkcJxxGEnurkOUdWHSpEjxUVKEYBAkvX8S+MtEr4+xLfHLf/4fjdy4PdNrC0VMRyx1V4vMF9ZL8Q'
    'gHHsqInqoAK8jG1UnSghOi4JwwhTD4wq8gyiut1kOIzGKfAjipuD6cvdB0coASct6w9Rr8fwotoFS9OGc2WofTCDq8KwQ6aI2w+s'
    'bM7UvX5DjNUibNCezQQNOTFGXoQoNzzUBojM01pyShGijEjDMw2C49vHudjfw3Sp2y+3f2y/aL88/ra5b94xMHFNXpHDQtMKRxSP'
    'MB5LR5fY60m00MkpiPSUSjlIJmNBSAsYVaPCWKWUV0NqGJqximzarXklFX8QbuQ9/qp9/wkNdGHDX5HNruQIl9cqN/Cp7M75wQOv'
    'yHsvmkqgo7CTkwHUdpeyWknRYcY2lHScCJPbGb1DFk2GydWbNsdJCvbpSfKRt0GgHJkFUO40itMGNYh3Ki6vHY6+/2QF2H2DQ3tL'
    '/DH8uEHJJY5HpDGQOgb/2FDGalJSw2pVvjRDr5NkzKmIHqPy+Bakg/1l1QeNf6xJ90nLTENKgoXj3WHHt9MlnGXiAHzB1dK4g6CE'
    'gkE48lbJ2XHWqJgOt5WTvmFyeQG1X4X1ZS78JDBRG1m3eJUGgUX9ZIRN0A03VzWjy/eoV5EnuDJJ57JfzxJRyuI5zX2Ir914Cdze'
    'H/h1WZ5YhSPSQQJyJ8PKlENjRiz6eKs7pZvJRDqns9uasQ00pVMZB9XEn957eVxfAlajLvYPdrYxJDRpYHa3f/YDUqOX8d7LV+1d'
    'KtDZftHmTLROeGr6Ua/X8yJUi5dQj6I4u4Gq5U+u6UTWhq9lHTtaLMm+Kn5I651Xx+L4YEM2rWNaw7/cZn7k6txo199xkkUZyVrs'
    '5cWyxldCv5LdwcuSDIit/MScDWctCp4v1hK59MuYgzA9InUh/6wznF6qsAkWjeE1VuXoX7NZHZWyruQYIJuy3xmjXSKDdVLUwZF0'
    '0QUypo16BqPLaDhA9RTH0HsRA6nupjIgoMv9SwHWthagGNeFpRcIPxio7x2ZGfLPKQjj3u5FNFS4qI6Dnr7evUO6rxrDHNDzkH0s'
    '55J9Jwh6Db+XdEGFZFjmNfcgLz+cz5ozwRfqiWxBVUp14EGAxPY+1rAlayThQ57uBXJLOUd2CSEtTHIPW42HiZVTxup53B118SL4'
    'QLHUAMD1i9ANWKPwaaYhZhla5pGrUtlQKE3hHAJ3Q3u6TECXvUvdYz2FAyBG2axlbl7lCOV1N/2mi6KKb+HH3+YLAsZlAxCDDyWn'
    'yMylzinpLLc1bLyh6cCpjwYfYyC60hubfe/UG9nwGyf3gp9wQWPPW2PPSuyOr/JPk4tJN2a9tQKlgjgpOZn5eiJFSiWG4w/SCn9i'
    'jpASF5ZKN5tO4/MyblouKGTeMtKDxcAFv8/BuGXqzDp73OFmuDoO2+YUCvJ2dMbPx9/JSEx5Mh0voEWhSu41jPyOCyQlOHMr8VhY'
    'XwOVgLpVxDv4u8O0HE6uCAHldo2lApU5cS9WgTZSlco2vxmrvAO/2/G1BdVvy9sWNGn4Wx2CyuNwybdfuOOTtCHIXAjdqU3Fs8S5'
    'Yoykw+wKEnX77gSf3TM+A0AVv2QHA9UJtFmasDYfdVXSF2J4rSKG8S6nW93z5JJSOl5FKj6RnTXVDTJGmvehFW1s6W/Fi2RIF8Wo'
    'ROuJv11S7AmZteK1J4XO4zziRBekRT3OAnq7ikuTWJwPeugje6bYjHeYohqez3BoMAZ8Zh7Ivr+grB1UFpimfjKxRjVCTmoo8AZG'
    'hVdTwVpM99IE6W+XrDuSuSZvvQ1kBZBfeUu7KWiVvnTo1iQXNKcaM5PS1IFV9eUMHc2zi+b4Q6fcNy2uEV545af9aKoNivFmCYkJ'
    'SiCDszM0H7VC3VlqPo+Ik5mCPs8QWhkVprwGVNdM3LwTSC/MxYfj7d0E86VuiA9xPHYx+zKe0KmK9gUwjknc82NvuSlWK1bKVaDX'
    'gNJmYAzg9sephO6NysgR25LBDhzXsYwx8SIaY0E7rrE2/mWabrhvvlk1N6nWxbO5Y5ZkgMtu8b9wRsGJU176JX2wVDEK9IaTtatY'
    'jAnENc/Oqc5mjGWZt4flATc3WHrappNuzj544mQkKZxWN+eUSaBqkUTySUyTKQgKAHNKZEIoIZ9weV4DT0ZLJMVYTAjNY8aEFVkA'
    'wACcLmVh3Z98Jk9P3c6CgzDnwMyMD4o3VEyeyzLLDAcWxvmbUh5Rcqh1PS7kd+XpTs145cx0xIPHXMIcYwGopQy1qmrARmQNMQeJ'
    'Xo1zELUqL7yJiqY2Ehl4F+CgpMMTMvNQHG5y6jQq2Wc74g4W26oPEO9G7MtFqzQYKW7Q9VSFMWRBeiZBWtH5M/RKSc/fudaKbBNk'
    'BTyFVJ/G/jBnlWSdmq6x6ZUPrj7XcuyKQ0vnkEGVo5syG6SSEGokt4mhVHtQBbTdJ1W1YSrcSLuBtg1QnaRaeQF4ORhzqB1J2Cz2'
    'TR103rIPs0Ml1M8L9B7IG+DE0X/YwDjwy62GtXe8sZnVUIGGPXi/GmAUUSY0nKe7IdNn7HOML5Ph3NZcynBfNupbRZEWZRaqbfVn'
    'r5N/lbKVvUsp2S7/ys6Ns9/as6ibcRMrpCHsFDIszOfP8gbAY0HcK0m/sp6w20cA32QdK8Rz5nU+qkkRXTppPRZWjiO+JNu0MNJr'
    'smFrEl1Hn9zZhNqz4KlOC3pFuUEdpybCaPpWsfZAGO4Fjjx5vRNwg4XMajpmRfmL5jRVkOAkA2+gfnI1inftllhZb8zMgdGiMs21'
    'RqUSksgsiVSmxczbRJvW1/0wgZmP75ZmGIFCvNcKCjh5eNU9Cg/p1ky6G1VBTRAjOW3vZaN8uN9tPb10alNRgM8HKSllYE9dwcKT'
    'a+R5QuEGI35zghHzowlZNWP3GZYffW0wFdq0Tekc2DtYfaTG5YcKhw7eG+FwOvgBWXM9NhjXj5Po/Jx8FLsY2YnLp2j1e0LB5nuV'
    'hTo/4+Z09580YGRHBAel6FDfdrDrTjcakbrDxCbGdCwDYAMGaawCXcdT3GkyekgyWlKqxiWDAeaSDfvCdnZ0My5KFrqQ6Y91vbbo'
    '4YvW0v7iB8pkgmGTyc7J31/EF/Ehei36bXjfy8bmxIozbcHjryeS8OxQw1LUJV9gDI4gp4JoMxzA6zJ6KxjtPao3lEgPOwaQEOg1'
    'UMMubHo079/pdCqShcCkxe92tg/foZa1I5k15ADe6CzBwkoNLHxVtUM5dECctyZZZcToI29n/3SRTndQv9XbQNNwZkEIXVG1Stsb'
    'tzN6000nyYdYUDIM6eZ7FQuzfj3KecnGTxvEyFLuZOllgI0Qc68DkTp1gUS7WSxzMV0p0w7QB4LdFKaJcQxhFQoujRJCXYDW+1Ea'
    '0NYYQxTDPrFG12f79SaAV0q0v8cGu7IJ48SKKcpxmLDTpUaP9zyeEDYplGIHBt7BZt803moReulNVPv17RLngun2KwW9kBMxYRTT'
    'FAwijwbJACSgkSq3gNlvg1GN9PEU/Tj+GHd3EqBneFeSiMG0hCbNvYT08BQ0dmc6GT74Rz1awl80UOuDYPMKH3aga8/k1mq1XGLl'
    'HojNJTtefbgsujFNyBLdxLinHrVdwosIWGzSlQEmIRbrTQgwZX96XDoMJcNYVDeobl0cqI8Kc8mdlVWBxjVJpOfRcOjkQgLYRrw1'
    'QCRLYZcsCU4ZI+hoRTOg78gv+Apa51RJxu7OyaPkfte5ozn9UoEPEcw0k6GHnh1cRgsO5UDGUDpJLjkLgVSxSij5yeInCveh36d4'
    'fAMO7QBtG2EEfu3cTh1KX6lhfEoOGxP+9UCsVOCv0vhjKVt2mowFl8VfNRC47LJ2iuu8bkqrjb/Jb7i03gj3i7QReVChWKwhHPL/'
    'UK5Ba5WStkLgKgH1MSdsZ49WrwwpipWLYFZ84eJWbhr7Rb7IEuzFHkYgOEbe6NXgyOKNW1AZCon3bjUafrZC5CM1gjrC5S3QU2Kn'
    'Cg5eBByxyCR0zKjQRtcCTHCns4WEPeNhju6Dc9FolnGglAIBE8bwwWHpjP3z4wexbDcDe5ZaF5fAep9cgJBjfJCvSH/E50T9nHbJ'
    '0n/CM2K79o9vPy1Xb/7T0pl0LyITBNIfKUHzyheFh+gIfkXhXK9sAi4M/4sxTn7CcbBofmWiWpCcier8E3GRsgMmT23pj+XJxejz'
    'VTT88BkX7fMwST58xtl9RqOoz+Qv9JkyH38G0vQZs+1MPscf4Wd3kqTpZ+h8ksCAP9Md/ec0uv48BU7/c5R++HwFlB3Ogc+YNBHL'
    'X38eRhdnUPR8MIw/j5LeZ/Kv/QzMFjQA3PvJ5zEs8mcMrPF52p8kV5+JuHzGpEKfx4Puh890Cn7Ga+nPw8EpVI3gePwMiDP8PMFf'
    'KZyf0FN0NfwMmIcZ6ZAH+gyy50VcSbe+l6czwMYo/TT8tDnvTwCo9M3w6i3SvaLPqI5Eath0Q/VYeDHuT2CpUlH2RAbiA5R4kyee'
    'Si6yQPQ0pjIkNViI+gRohLb4sjHkkEckQ9DjPYqRN4MFrQahxWCRtA+L4dwubfd6yOyRPAj81ACQYkA2FxSJBziWAe00mF40lDsF'
    'mePSVJwOo7Mz4rUCO+L1wdHuu/29zvG7TvuY0NzbEr4+YZBKc3pydzg49dWkVngzdtzOdeIgqmJKwpqYJ1J0sldEz/vCd6pkt4Qf'
    'tPEEhQMKFdN8o6GHPEoZf6jIG4WL1LlZbEwStNSInhw6URckN4PQMKrCf3vAPjMsJFthRtzh2lpu2Yu2Va84185BryENdO4tvau1'
    'MpMhNxSZwxqHkWOCp1x/TEXohkC9PS03Kq69v15Q6V2DuLZjbtSyC8/l0FJBl8ozAWcgEvrOsfZUrhAB7FZh8edoE0rNRimOAOKM'
    'gXArBJGqsN4qtLIa4A6t6jagVGV4Z1V1At/YKWnVqt7YubKp4w1nuBkkrQroYcMaURaNb1wUBo7oLGb15TQ5lFdFIV8KTdBNYomA'
    '3WaAEKC0Yd2UURvqWbJ0HWC5YJDEUfQH6EOvK6CZh3ow7JoVncyxO6tU7K50vfzuaHrmTs0dezYkLbNeul1Pbneu947z5XtFFMbR'
    'JJpSUlqnA5iy3Qblb/0lVWyAXZRTfiz98ZdUSfCmHsWPECUvVeyfgHlhDPR6VejxwIzLcsALzdgftlUTlaNmJNrqxXZ2dY1j7DtK'
    '3Veez5wqULVmY5lreNHWArbZvkl10I4mE7k5P4bcPMHjCqOnzRk17atoYOUWYAUGUArcvlHvTxEa08j9IxdN0nxDSqLrkxiWI55s'
    'u+VfII1Rd5pkiWpf48M3aY25sCqSfCNCvgxv3bNuKyAo0QGneye9naeqC1zzzyBeDjXZCubrcaiVHa3YZZTvPTaeTvdCu0/bV5nR'
    'hlfJ9dMdsbFuro9ZYXh31UFNKllr2BpaKzlEAV8u1oyMewAtZQIBnQ5j1LPYJxaafHkIlnaY8sRSh1CEr3c0MBmhKHOU+iNztBrS'
    'wDowPBxX8cTsW0HPSKHgDA9dVPpuXDr/3ejaUsTDXPHiDYMpYbpdkom6/cFYlCks6SAFhgSj+QDWoJ3hEnzEgBQgPw3ORsB9KDmR'
    'au5AxbpUrSChijF+HlMwIMMl71UbBfYSp97tqOqZcNNPgTJSKlUnVR/fHOgLEwzNg3pmVqUq5TSrWJ0wjNw9UUndMAc0ymp9rLda'
    '2/PYM4+dqeTPqmkoLgc2vvQGtS3ySJca+8rsLL+LKcbzy4eU43IUntyq2nHVeOqtHR72xpKyAc0SWI4J2QGSni5Vy1NDQ2hEJxUb'
    '0CzNPXdpKplOM0lm1eU02W5NkmEqynSRQdc/tk1syjcQOle1RNRMoE4bg7/e7bxtmWZh6fZkklztUoruOTAj6gInMjhDStIEadhf'
    'mnDrr8aLtl2bq3Ha8jB5+x3veY4gVlch1Pd6H8UTFHfnGYZKpfiRDE8zbQA77L3dUEY3en0H0/g8fQNNoDkgFEcHj7GyxnK/62mq'
    'IKahibZTwOnYAmLAbiKwTWaRJJ+c8N4ocQDZPNWRjUYFB8Y8kM6z/hBzzcWs9FzipLTiyxlM3lCi3iWaATlOkJa1nxVxiM1agmO8'
    'bedz0P6sXqhQl7TpRL8/BBJzBuDpd9AO3Nb3IFSN8gdoqfjBVrDazWAEaA7Tkm1xK0CXNnCEL2WlHIcE0/bVvmJ1OB6BJXJVddeS'
    '/zCnoarHkZCdMRm8zGC/vK3QDocGAKQyscO4pQ++X6raLleyx/z2HGhaTf0Rje+tpm78SZgBqz4seZZyK9gyrSzDKY74e07s8Lkk'
    'WquYK9WSAbAv2RZHSJ8vNPrdSLhzhaq+CylXkqfg5neJbTmLb0xt8QDLOb5dQbXAPYaLlytA6H4bscE6s+VTe++r0vg7VDKjsfF1'
    'NlrlO5/nRhZF2VPJ1EJnJHTSMhIyChzDHsBS4K18FamJiAQ5yLPBs7Iu0ArwGFOQIQNpxRAAcraAj4XtTqMdAkxbsOpWJ6yL/2SS'
    'MGwP00R6xGFKG4EJ8a5F9mQD8eoyZfuS8+haNmkYmWBMJh5t6JR075uu9LJ5vBEDLoco26nN1Lypgh0PPmtFwI1q2paJBsVNbOL9'
    'f8OL+14cBjQQMRjNZT6ABEoBN0EAr9mokjLyprgpUXwNg7yiDhE0gaFEyVL7qIYm9c/yG6pX/eTLBbpn3aKsU7QTdQB1LGnDWDcy'
    'srx873hgeZveLA0HjZRjU9VyV1mWdJnhnANsruPrqxwCYfKvFBL3jMA3izZjKhqyvMNbpXQ0GI8B2PHHMQpxyUhPSH5Jgfhft/Fr'
    'T/HcNt+MxocoHl+hEV33GgRkbdSIk7Y5TDIRldq8nZ939tsOn0iSEJWpDzBcwcHpTLaNjgWq8qaM9R+g3eHfyEaYMr7VVkFIQzQz'
    'yFydEyd5dwCnKN5vAdKg5RpAmHOSpP1kMu1eTGGv6ojdwAn0ukkv7rEhYLO2VuVfHRFPu3Xctz3ZXkdWL8fZII6aQVWeTJb27XSY'
    'XJHXjAoYpLXMTnAg/VaHAtJv7DhAlmLaiv6ji/qBf6ziTrAfprpVHeZHmU/cWLp4HPgbOaG3buwre/rvkObhojyP6EYm67Fjjv08'
    'jTjfFcl+792bygso+vee5FW8XuUStjFckyNvIdG1Ff5oHkqXtXCGSydtotzSRoAOLZnVSLv04pSkZ0hdvNDfdVhztDCUYR1iFdaB'
    'YlYOpsC5A3cR4b0EnAcYBVnEQG56iGOv4xNMjoEWHajrEhE3eDJJruC5doZhAiJ04hkrIcRkZcJpoW0qoCP+iCaUQknxHwSLcxYj'
    'wuesRhFkoMw9hVXVsbCkKC/y4+vBtF+2C2Zv0pSS296fVg25HrzI+m3eVRtdZnvdBam6J1I4+AGQQZ9sRI3j5Cg+Q4MzD0e0ldKx'
    'dzuk8sU/c+ZozdjcbMiXOypyjFVoy1cyYGSYbJweN9g2wT3Lf22k3QTY/Ceino3Ko99S+1YHp4BEEic8uwUVAeqZLGHHXv0Qj6dP'
    'r/WELPdyowpQgNzpJ4NubId3PM5RSQYKaNqk86oNoylsKYE2bmKcjC+GtBlkSBs0g0rMHjZuCEsywGA0lJbB20ftl8fP28d7O9v7'
    '8HV3b3v/4MdXbUBOACx6aYnXuKuiEeuD7WMOLxjoRmFU5cYAIYG1oR0Yf4TpmPyOzP6hUTlt9xOiCIhy8G0gw7XWTXwlk1cwGWYM'
    'FmUUbCfo+rAQDVxOyz5OQZ4hPRKA2hDelOOx+7TaqYgXQR05O4ny9zJLjVYCOIHHj13Ut6QWbwDI0/hNO6TGRjw9XBmCW7qcS+6w'
    'nBmilHFpPIFdawVxLmeHFZCj7wXkaMDe8BlXYbZeAtHeN+RNC3Cq0lurQMaXXu3RbHwXO9WP9HEZDv/AMLIQxemW4jQARQXRDPYO'
    '71lH5lB0mhYqtLiyD2DdusOLHrQVgqqJ4i6bDRSyw8BrcUNXcEaN7tUOMmFOjUxUqYy+wyXfm7l9qSndfZPk0qIOS+YnympBTRC3'
    'fPsTrctwxB6zk/wFqjjnK1eoBgYtfMnpO1/zZ0tPcqG+rBkL+oTwnVkG67ZEaUdTTvJ6osPaxLZDYyKKdqcqGkpb8l1PYubDDftH'
    'gDy1SYJvaGHF+HPD7BTdECjcUJUrXqpY4kuRglpbVZWdqQ2qFFJrTglLHRgBPp8fVr1aPFj2zkSJgG0Aq47yiychLpDJb9RnDYdi'
    'RutCUlS9Vnh+kjeYavCUz3ReWYv9TvHo5GQ5yFxz/hv07bpkHrcboZ0zM76UdZQThhazdcGpumke7A1krbZVY4Y9UbiSjTgFXK2N'
    'hxnEzQi2V4Yv1ZzpUDJQWQKmHaPs08sNw4hZOVmqAWE0Oj2F1wBZkgLRtIDSjfAtBDd1xBpFaOxciUvkIU/iEA4D1pDj5arcU9SF'
    'xBeXDUKs1aMPa6vljEOH8Fz2DZYvijFzMLruoquckpssjP09fim/+WO58vZvf6l8b1lFVOa9E2pWRa1ZcQZ1k81HS/7CpChUM05j'
    'mYxX4jpC+/jAFe1dGwEFuBy4KrDfLVylDWi5ng8fmCUR1vjjIOXMwVgRsQIHkeZD8X35+0/45qbyPnhvJY36HANStAGADtn5U7ov'
    'KqTlzDjcrb/O90yALEUEdQjoDSWplyuUYNVpHD4NenEBTpUrpYLRN32cCEWtlCtryV46/iF8fTcIR0vUp5OdNdSKnKiA5uGGR3EK'
    'wzEqcNXrVkjGqj5bMP8MOl+jPWdVX0jGvfSIPqmwMF557H1DDcP/uD3luDG7ZJdWnyZ7nQNlZV71En3NDPAp+7BifM4dZzMUKE9B'
    'bk6WKUMLjWWOs5VV6Jo8y16nDVfedtoxn3KvQOeKDj0X6/cVdOhufga8liSF17wMn7y1tM/s8JUJAtIuFb6/sEs4iZVyQuH5UAxr'
    '0mRejUu8B8F/829BqNTmXfDwDoLdJaIUWbV/QST5pplgjIIKYzXsHLw43G8ft7/dmJwLix1FETCMclqOP5K0v+9p7he7Ws8Jjsgu'
    'u8ryKB5ZFveVRQIRyvxVgBeP72uCdv+tHZ/Q6NXIZJkwxZmaLfQ4lunDAL+TjQAhuS2oUqGpkFclPZrAhGrWcDBikbcgyk2mBh+P'
    '6HOKGgRxMRrAlKVJgbwJwrsBO44BZg+Uy6MuKVSMPTqRnFWlDfxcNvTvblEJDr95QRUPu8CCer7A1tpqn9+F1taY+SJupIKulOSy'
    '7rw6Qu20XPTySTy9iuUND8beiClRqIUPMrIFMp9c5iOmCcbbq2FyFVh9vbG/3vojKnu663nNXux8AUnKijV9a2yPX5+IWAqQoKYD'
    '08ygZvpuYYAhYAiyMmzXgILpoHY0lQ6jDR22E98O8FoDuquJ5iY8oDEv/Fur2Ro6GO6bwdtcU+uK8p9Ea0fyfReUJmVTG6ZjRzF5'
    'luLMjblkZhQPeBQ/2OXE4MGDBUfDfQ28cVg5alUgPTkiaY2IcyAnz0rxtg+EAVxsD1ORQvv2ipeaYEECXkzCTVwCHdJ6lGBIIcYc'
    'HEVKzglDcYJhIvBCihxU1KZT3ifYcjr4Nfb8pufD1U6CHre6V9KnVXH7jyg9tpEFRx2OsRigSNbmfEfD5t1e2Lu5Tk6lkpurqsuY'
    'Li7lPZob+q11Kz5RlAOqolSIjbz10irnReP2w3uG1VuqCBGVfDWFv+pyl3WBhBIzbtLN4msks/FkX4qIJUM+S26J55gkCkv85Z//'
    '81/++V8A7dj3QPz3/0ccbz+lAA5E5/Rt5rEJdBeIbl4YEpHneXy0/bKzhwmlMGDaG5OgSZSebe+2xcGrY0qUtLvX6Rzs/9R2Pu69'
    'pN+dF9ud58Kq+WL7eMd58XrvkGtKCxsHTgRquW+27AF5KXKJQKRkJ0BVOMQG8fX8LNvYsNuwDR11pyoHJdCqAq8FaerlLZ6BeCoV'
    'L4uvHXuWsMsFWnPqgelPti8HHkTafOooxhwIQgbAl14caEDX7RsV+ukFOq8B0qrmMNYHJ9t4fvxi3+myfh6Ny+VudVAxV6DvfxgO'
    'hEwz/JFy+t7cF2SL9/h+1K3huO8Dg3CeINORXI3wrfQnyUkUW3rjWbK83eDUGZXq95/+rnPwElYXtSyD02vY8jeV+0++/9S9+WFp'
    'OHjynu8/6+gQXdY26XZwLuXc5BjLdqdzReEC4KjqfnwtVGrJwGQPVGiLlKLo/5yN0JVtRwbbomZkVK+i4pb/5ckw6X4wBZVnlpuN'
    'GtFgu+vF2XAvIjJUIHvAIRgngwRvP9LYOmIE8liOIEDHRHbzBlhCy/GhmPBZ+tEAG5HflxY+8nvCyKv2HkXmjC4kbCmoysH/0gs4'
    'MPCkO6VYOJw4AsMLCpN1D68/Bx8FNIGWz60HfEpr2kLIbkJSteahLLOCzvpLKX3K0UrQI5tb9naWNHOENHMUppkjn2ZuhJHEbVj7'
    'oKxXoMKbtxV9qSzH5ASTmQ2B7xwaKNvY/C5A/hrqtONQ+nKtBalcNWD4ZXvIHnJ6c/mZf4F8yerpOBqZK1ZVvaIb8hTtFoJlogNq'
    '70pKUKMDdn63IDXKpSHvv/+kycjN+OP7cGFJuFRhTbpa+VXOB6PXgx6uGVbTWadbLVhmauQKv1a4ge/sA4jW7bvw4cK6boUVOkEa'
    'MsBVNN3NhBXHxuZLzoUl3dRc8jwqwUTJrJcz6GB8EIVEHCfEbkCxfGxGDH87JkI08EMWqHDMBvPtbe5YNSEfSjXcKoHy1L8NrPc/'
    'ICI+ob+tM5YGgadgnHafT8+HZT2qChyLVMV8U93rTyanvPPH7wQT3WNi0vtPgEORVd9b48xml9JHvsmfOo8TreNsagtCldm9oa7b'
    'pMjSTXo0ghZR3eXknI035swnnLWtoXAEtjGUvVe8EJKUnVRtWP9wllFF3tnc+LGJg59JQ5Anp9ghHrONUe/BPnJiYeaNJzc9BJ4T'
    'ej+yvkbuRyscQHHmo6pimt51nr3bP3hN4edhZzZXMNb8Qz9epuVq3RvIpFeZZdYkCnYj/wamUB0j6gCqiWbVr/oAU78qWTKAH/ZI'
    'AgXUaAhvAgonRYWsfJDxEIidnaxjaCHSNDk7G8YqfgHQqCoqYR773t2WWhBFdmI+jXEo2arivaUXjC3m/ESBwZqR6l4Yk9XTluRw'
    '0XkarcjLnwRxo0BBpeawRONxFy67vTkWb/a6WgVQ8a+XNNaEXQEXNczOtqIWUG3qrUB81JyNbcKghuUyi4t5w8oIM5C87Ll3l6lW'
    'aRBGakPfjVY8NYhrwvekch7MLjx4MLqpv3eS/sFs3qWUuCg3EA21UaNES7WULnUB5DC3MlasUHXfToPAl26I7z+Nbt4rSKDBpEwj'
    'LFNyPfaScpkLPkVsD3XGXMwtGrznc9NFZCto9zPO4qEi6H7re8BXe+LV4e72cbvz7cbhIb1rvGBsJcMaAkbPeFg7mY4sNDzxWUV5'
    'Y/VYnGQVuCb76kmA1HJN6ft0qTiQk1A+XGBk0pSIsrT9kFUqPrKjLeDTC+CznXy+PsnlWdn7zTH2xH1nW3pyg56t58g2t0STz3tF'
    'TiABO1JhDRaVDZyu47HXcqZkADqqsgGP20Yl2990MCVS6hbUOr/Ss8FokPYdfUPPzjytbKyA/yK9FztVlLTCr0Thba8SkQ4wI2c0'
    'ijGmWTqOYxKW0YQKc0XgvyVlvqPI1bQwFjeTKFo2Taem0wrV8+hUOLfvX/78r55XWcagJRtFy/MC0sHesmYmd3HRtvldoY+IOk6U'
    'w7rtpEPHIDtT2H6YOgazBHJ3UBjvnEzdaoPRaaJg3AXOCf7yTwIyX/n+E3SLB0EWqBaHwGY6c1rHhFJTZR0wJbMB1VToMxVQEN5o'
    'ZXVENAv+gV02mV77Jrhwhsh2KGyzs/pUAZvnxXT6s25bFAmU3ZKVve50kD0JaYbcFi6D6sTcRjc2Z9BlaNgiyvFwBlfbj9Ka7BCI'
    'xFM4COJoVC4arkyYGQ8t2bxS2ZIgtOhu/kaF3mq9ZFqqbAVGZEYjf9l3jLQTC4kAtq2ZFXX9Rs8VWd3DVAa/HD9SOLmWqIsoq7WA'
    '19vSPWw8SdCIEi3bL0zJUod+eSjk8L0W9twKLzg6FJ1uFBaKkhHzqKVIq14q/LHCSmeR2U7/hbnM0NK/k2RFLJxD5yvMQA7WmwLP'
    'K38GluFYH7CoM4rGaT+ZIr77/KL9PSfNE2ZwkonWwnmeTIFyJqjhMZ6cO8RrqqyhQNKcy0yEkA0xvi2T0HLFB3iqECzVgQxtbdot'
    'kf40h5F5j2TgjbwWwlshavvm/luBH2rU5Hu7K9Sm0j/e5oBO6Wh8NaI6vdIMaS4Z7SAi/U9Q8N0+wgLFkZAkeUmMQO6oqUANVQY8'
    'eH52p/De5hQu7QTEN9bBjwkB6e4SiwSODM5sb9/dS28+nOaGNJKgRt403m6xTyHbSbOZNXuKbNjlmqFyJ3BY9A5GG1a5VqhcD7PK'
    'uf0uB8sBEZDFVLmVUDlii7rT5oYpt1pQrmWVWysot2yVexgqRznE0qY93/X8ci273KNsuZuMf5CHXVXRswyeeyH+8wui3O3wTWcg'
    'J41Mjzc4TKTOOIW/JNbgT0IM+gErX80oznt1tdJV87tl/V7G33JVzM8WpyGjURuVIDxrnSBNFwf5ZvCW7uO0aXIF69VVBnVZZFOp'
    '3b6pmqGz/VNbLIn9g+3dvwI9Q3q6PR68mgzL42jaN2i69Mf+dDpOtzZ+WfplaWkgQ8tjEU3K8MkONfAcKqAgI2+N68COofKQ7chK'
    '2NwGhzTNL5BulOwWO/HkctCND8hnmeIQUh+//72tFD88ODomjIPXUpQ2PSSTKcdhK+wTmciVlWXiFtcbGA8Jv8rGvK70LvOHh92Y'
    'Ad7zq2XAJh+9cjCU9wSqpaVm62G9Af81N77/5JW6+f4TNnPzHkbM7ekU0J0/HO0dHr87PDr4u/bO8bvOzvP2i2284+sm5/X0AzJI'
    'dckoA6yDdX5qH3X2Dl5CpbWcEjsH+/vwLxQq7ADjXEjtf2l2S6bbpld4f+9lO5uPEmCoo+OUTISekh1CxbqIL44Vj425iSt17HiY'
    'RK9Gam1uuUYWmfIhFFyeG4toJDDamiwWj3rqp6NfKn1HZgB6R0KVQ4bfHrmMoM0EugPKRTN79GyYnETDY+Ce693J9XiabGEemF5y'
    '/urV3q7Gt/eAK9TITe37T1zOKlausDY4VBj9tzhPskkTsrxWwU90bcSteF/lrS1Q92aj4isYusNkFMvJ/YS0uUwUmg010U7TTE6S'
    'bpum4xYzryk6jpWQg+q7mVs8IKUgsnSheNzbwXHoyt577toxBRJkXQUok8Zlz9CKCxena7FHd+MARC7qM2gsnoyhTcxeQa9clnR8'
    'TYGp6nW1tTj+E7tU0fc65p46mwym15lMcL5pGJTW8Sb6EUX8a3xcbza7j3rd1YxNc4Otme0osbY5MzXwR+lOi7ttJ+lhNqGBsini'
    'DghhUK+I0T36Veiw0Ww0Gs1HyxUvkQ0VEE+ePBENC7OagFnjqEdRi8vrsIUavkQfTYGT6Kudo4DhglM+GFgRVKPhGRpv9c+B/J+O'
    'LpvRcgs2KQ5jo3CB7BBc8qU7JPaiH6RxBwRbVKUQT8gYY2d/Si4mXcmmXMTWlYtB9lJC/qF4UvHLDSlJkBKF6sPinEXda8oLxS/S'
    '6UVvkHi4qC7/gQNMKcJYq6pDHmL9jcAmdTqoQs8VVYe7KKjDBapoXg8wSNHmqSooGj//BG4Z/Y1TnI9Q7d7YIUlYjTpI6V/dLDZW'
    '8admT0pP5xNmdZ8xTJqT6dYBlQ+oWWCy4KO6nW/yAVnifHCGnq6yF8IeYoctcYKeVXYOwBl+vmfjDHx0gcht6NgwmJSQjtX2ZIJ3'
    'LUgsxSlGk+wlcUoxB6QCW0SiQye83kkm+6WNyz8xzITSSULPeDsxjctSR0kjqEvQVjAVUfADoHnTxXLV8pMcpiVvUu9pUop4XqDn'
    'PnwEqYvjWahVFt9/cvq5qSt7OTlveYeC7ABeogym9fcVz7rwihNzGuv17OiJvQwzXRjammCgadQW2vD3K/4NHl7tPA7RJ15dK/8h'
    'l0WU8FqWDasBc/ZEWP7YqFI1oaSE2KI36BE+kCFVXWBRzCpOYfWkcTI0h4COU+CO455GEMcbhULLUx5R3xdNo9C+c4viYG6d7koQ'
    'aaxHMqfMXsJYjbGR9iS6AvERr1kqoeBeaGwcXVk0GJ88CoyvcFPjkbdBTzeuHRtI1inZN8hgmdAMmXEMadrSRJfOtZIKpc6fVKDF'
    'DR3mwoyMWrPbRinDAiZ5eljfET528Q2XsXyPbQInR6DAm6ab9zqfr2mTcq7Sbzd0Pcc8yLDnJrs5X1XLycn48CYqpWUnyBSuRwfx'
    'lGK+M1iVKKfMX8TWFhogVhUsbly7qzo5YKvW6uw3brdBrtduldPeR2uh9St7ta0m6VOA6qt6RPe9HqwYEF5HdnSIcH9O/Iicbq2A'
    'Dm7vVjJVR9TAYbg7SqZwpMh3VkAQPQwT+9Auacw5WxXp/EAfqjKI3p7aYFoX5J3jXKxCobcpfiFZQ8um8I60yrG997ydajuUUYHj'
    'IlSkElsaGelRY6MV1TDYMm04iUKyIYl7HLXB2ksEZLmXSMwyQKBHPRPYZJVsd0pN9QmHtqGnJbeCO4TAXtiQw72xW0YskFVcPGcg'
    'ZBGdBpGL5bqWhWiZjoLozjVz8Z27nYHsfhuZQUiOjRoz72+UN5OTg0GWVRieCd6n7jK0XQaeMfwSFp4fSYO6Zd6au4eKHSzXuZFw'
    'db0kzJWt1iyQ2W+9s8f+tGG4VtboeiO3XyKDiD88JbFS4hq2I7044YLCLeDBQxezZkYG571t8qHlYeo3GnB0IcMv8kLEmBbZosBu'
    '0bwJtaj7s4yLIkIpJh7k+Ah1qto+7Rw48aDGrOry/mFmjQuNFR3YcNdPv3cPfA1p830r88Y7rKU8oedXtQKl60cJiA3/PavuZYIG'
    'ZHaB1JaAvT9HTdT0khRZKKeQVmwYXZfempiSPC6uZhguyTOjuEzNyPMcoMU/ZazqEOtGn0xL9Ei0XzWCd7kv8+tbBSrWdtAvrbbS'
    'aTLhgOIhYU0ijy4jwy3LqlJe38gR4WVl+UpWIrUgmsXmd6eLWELiCawpNlpQS5awJcvrUTJOB+ku38jlTs8u5sywGw2HnX4co1Sa'
    'V9uUcaqOtT1nflVTxqnKFBzKo3SZX9sp5jRAbL0UlLX6C/e4q/7SCoEegc0Rvqqa8m940uoPedvciHQkn0tlfFY4RxeszMtNxyg+'
    '6slPO1o1/tct1tNVByMT0Usaw6zrgBydk0UpcU2VEkleZ6tbVyEzvKC+hHp+q95zQvpY4p4VmOzGkzEvv4D+4TJP85C9wlhYCWHu'
    'SbL6iMuFNREShULkU0K2Yh2f/Mb3OyxAIRdVAsiEaW3YVEddaKe2GsBBiq9weJasW6hK1TagCHN4mmsTh+rKJcTT6a+Km5A464BV'
    'kj0Hb1WkPZuW5BIGkvlzvtmUJTfAIMGZrkQCdxnssSStBR3+HWf66QYtSZ1bDcuMxbvJKIxBeC4fAynj76lvFrHTr+45ooLlq2HH'
    'nHBkB++uQ3esa2XNGrl+jaMXAhN0Tw+pbgVC1Ixz8KPUc0j++z0DQgZERJ8LXQkWM03oshhDKWPyYNhlsKns0Pb1UubejNddYgFp'
    's+7aBcYLFDUB4Xjwa2zliPa1ZVpopTFvBIJiWolIlFZnjMQMFVImeKOJ0q7lWRGP0ouJFeBxTzo3ZbQ+qj/S/rAoaSU6s77aOieW'
    'cd/BP+F4nNmInFC0ouNd2ILyqfKYXDTm5zxRP4PCsXlwLii15HuT1YHyyhabo2v7GkqO4gQCwjezU5VXpAU76ZAd/KEGlNpDByvI'
    'bTWc5dNqXHEThHaefkviGbASCpeoHx1gVOtvDIP6atDjTkv6VksquTYskFEzM7OtBZJ8kEpL6rgsdZibQAJj61tL4WRU8MlWHvyp'
    'IwfwWvthx1y1rQkJqC6lObmAUdj3TZ+UZ5hwstRMlF2yMuuVZsJwXDwmtUS+QSk7qj+RXty+WamrJQmYalq56ildU5EaQduoqiwI'
    'Jxab8PnzY0/K3tSlbM3FY+zIfJIMGr5niDxTL6Q4rBkdjlimBEx5mquoocZKQd4a4D0D2UYNO1AnOqMoB3sAI1jo05ppp2TRD6hU'
    'yXZhHfBYIGOaYDHKwB1a5uJZB0CLmNC1p5KCyRhLVrVcBC0Z2Q8VKoNsOEU2aHW26u/UW41NAEyp4WMgon7C6lvWcl47dee6cNXL'
    'IO25MvMJBzzt7OPK7BI7kxmZ+Vj2eSdzSarVAGEwnvRCAATgyQ8abCe9AMBkF3FEpp6h5qU6IdSB+mS6kG8yHRkqkmN48emLKdlw'
    'YPY2LtaVyQqOLhI2tKdC2zDvtB5Nv5Higq9PxWYDGmBX1UalNM3IIRl5GrSsgiQaj8nHgjVnVbw0CWjO5EqjZLr9NLDO2Xa5qNXq'
    '3Io0l/wspEb7pI0pXOpiDDa8/XUzj6ptUSUbbZVFdGu0pPOp1uRC4DGm3jKRdnxYgivi1wHEljZvtvbEVsaZzlyX6zl7cyuFu7tK'
    'Jpz6+AXwQ7pH561/vf3/U/f+P3IcS57Y7/orSrMyuvupu/lF0tu3Q5HEcDiU5t6QQ88MxX1L8YnV3dXTJVZX9auq5rDFGWB9MA4G'
    'bN/u7a69xnoPhwN8dzjAxuHgH9bwj7f/if4B35/g+EREZmVWVffMSHpLPUKarsrKr5GRkRGRkRH+x+2go2FCzDqZvF0LYz5uuo76'
    'kEut1x7WmZZtkvXqaY6ecXuD3NVXXor20hD3nwLfoPpRRGSf7aX7GvOsaPBFNhoQzBQ8K+yKjEdvF0k85hjudUNhieqwzkpbt9vr'
    '2BKrFyvDoCgj5jljHA6H1vzWdr9ve/nSsK56W7HXs94biX0tWYnkBlNiO0M96smTIJs6zfn2LmB64VKDmUJ0YWdEc7xrU/1g16U4'
    'b2nz5FJVNAxH7IHTTtBQiz0uQJhv36R/hiO0vFrNxuOwmlocLmlFRL7i0xRRPZ3WJCmwZ7Squ/Yrqrpwp9ZcsaAHsGnhWUjoMGX8'
    'IqD1azV4zlM/NOWG2Ws3gjAmZB4VBTGZ0FY8jIrX8HtViD17EPE8deECS4vL9UwnxocPEyfMeLhKsnBi+2lr4LVKLPq3ReVKqOqo'
    'Frs/5KZ7Tuf0i3xwTnbrjJV2qqaw1HoacaUrpIrSUi0IbFfFSVnBwc46estscMJ316sgFFXPy5nrIK5zI1zENzrsOONDp4HqSK1D'
    'WzitFr6OcAPg6PS86M5NnWt1n1+WLi64qsJV/QyVGV/7V83sxJ/PTmP4yriZEZuAOgpSnQMbOsdZufxpKI58QeV5FfJHUHqn03WU'
    'Al5Pggy3i4jEOJN5EUwRji5xFpjrtUnXgxeARS+oPArjRIbOi+H8SVRiq+EOnB8ACaecw5BFO477Q4NePJvrD0zawSnXi8M3VDnM'
    '3qqTEilfgUuPuK9bmTq/0oy78Emxs6Bt3r047OZ4KCG4DlPO2pqFvzxYFtVlXi8sB+d5zqi1I66aRGvnaGvrt1kMCtHOOCeuDj6E'
    's+RN1OXaXRWDsxvK0pCaOiYuzTwqZxnxlZ2nh8cnsLqWxUcCmr/0tpvL5kJZu2xCDGRN7/tOgzODYwwsUd0OPiOizjv3EE6adU+A'
    'Qr43ZOwX5Hfc9thgeB0BkCHpilzU8eBjXRaKVf3gl9XOUV0AkGV20YiJwsDnW7mjMCdm8rTL/t8q2PPrcCQOUj5kx3yEWZJqI7yr'
    '4xLJ1fEChrfNb2dCDXUaHrt4I3no4Ix/sdzEHbtb99XwZVjs6EedtErRbEpV7oLlimg7elfOWS/BbieLPzKGRac1opzjHwIblOnY'
    'ep8T1kgxm4TJJt8G2pMBNz7g7O41ymI5n4fsCfuKNWgBrw6SSptectZVw84WHFBc1UlDrRt1bw3SrZ4ZUO0eNoNN59nwnx+9c1Mv'
    'jBzvJ/Nmcov9Tc7Cgq/hIeD7m6hzYX1uiKuoYhjA4wGr/ojyI8pssMqW8GMKIs/CxtBwsh3vuDVGKA+cpa1Ewh8Gv8mWHBAYrwgO'
    'HJ7i+JKWP49ed9Nhx47ezkDPmY0NMMCAuLeICSGTgV4JJsuoqpt4V/CHYcJfraPpej4F7OsJzjbdIk+TSNwnNzjja+HUfRPkqB98'
    'WvdBOEZ8oaSFjLBvplrvm7eUf/hiu3z0KTGhnTahTeNY7qQT7pl2/or9voSWraNk9vu1Brp2UIGy3JupYou8StP648etmGjG9OPp'
    'jR/f/aR5BuEEJInYE3BzX/LoOWtA2/YqPiHo+ffe2Che7r7x4+emkeoKHNKra3DuUYdmfcFZXlba+o2L+xVRCgzCtciHREzSudfy'
    'BY6TK5cbnkWCoSYX3//5v39l3LQSwOBILhx1xf+LJykbZy6COnhTHyoVI1cRvwmzH8wtWW59EzW60rgNY0wfVxARaLTBKBqHy4LD'
    'mVryjVslEHqEdnfag+NW4gFjAsfmbTq/8ZCKeCUXRv63H7G6PZp8CQRkO9rV2JcCEJrC6yxq9l4ZYnFIHnYCfBz9Thxatn71p6tG'
    'FRZZkjyplyi67SLBk52T/a/2vjnZPznYe7Bz9M3hV3tHBzu/YQmorVWXiKzrloFv45ysrgpZI2EMmEPGBe53Dv9/iwSAC28FqIFw'
    'TV3hqimMScTvrDlZl005kEIjvOmuEkq61zoP1YpZM0tU1F0z3AIPQSRtZc7N/tvOrDvLoHEVGXFOEJZKAjvbPd1T+UCZEZzFSYIo'
    'GDBgOY3SJU6hCXohmK8PmgL7JWglF54xosvxRboKOyLEqn4TJt12LOwHtz+72asxMeuy3lyjpMWig8bmAQntBIWnMQdOxLz31VLe'
    'EX2gSdbwRcTR8uehBgrp3njx23Dw3c3Bn7y8cRr3g843nZrt/4Uag71yTueSbKSKzAf02H2Bdl/2rS1NU9jVg3sHkBBNMYhH1Dfp'
    'vVVkNNSVxDtPkmrJrK2hW+mhNKBDNIGP+G0Lgcq5C3qKE9Z3QCYeIB9CGHou+wh7CoVfY9yXa44KlugKnc5LQq0La+pZXe/QS5W5'
    'hDyxY5Ah6bHec/3quEuXgWr6EA9RF2Bfl2PsLqHKKaGVR9epx1hEX68W6zVUAJWqyVWDeSJqEqevN7jyDzvGnO31cJZHU8r67OhA'
    'c4lJEb1Xo+WMOBBT1ayZS/ttTLPyuttrFQtQcx69yV47NduWe30lfx642nlMZSwKNG7NRX7ycHcWzB51b1i1uPd9gIlNy8GJPczE'
    'HTfnQERUsSd1L2mXuNgzse2SqGAeh3iIM6I+zOKMhASRzMvmH8GC1yJGJLbZFvcF52HPLtVlOTGGUCywlCln2QVVGYJNmkdi7B1T'
    'r0nq5dMVYAj7fqU1i0N7yNXwHaHwrMZ2H1x09KWQDdedTaFkU9zPrqc4jfVa1e1Ufb3li4m64vJ1XCP+oBX9oaBpz1UAMpA5b6vW'
    '748rrV/QsujdgPJGO070cJtDjrFsDYWGidRb3BAyekPtiG/4tL/SwzbhjxAvql8YoG6Y2qkP4D6nFoG4qqEtHPG0pAGSfZIJrSNv'
    'EknwWGRx6p4++vMPDQfzXEhm5YZ947Ytm76muPUtSZ3GjfEyCKclR+aKGudfbQyf6WDfOUCpaZRt+vU1y+u1y/65F+raZjLiuj5T'
    'oxFm5JwrWHoTgjit7SuTD1mNT8Gd8ZFF84JjfbskgC2T0uNra0dvbD4muWh9y1PtmPDq5nt14lw1gdJV/eJjrFQawAO6636ryrYs'
    '4PUr8/u//2smgZPg+z//G16bXadSc8xT1ZNL8OujaAz2WxZA1/teIxVemK0G1EThlUQTF3iE0RwIy37UNXiF+iTjs+pYyK2XPTro'
    'OtjEw1Z45x0vroHsFWDbabtw64KoOl/0onLVjlHqVLQ5/MicnhEL/TpFmJxe7QRTKXc3WkO03609pf7R0FsLv6AdISXGIAez4r2d'
    't2TZ4Du18q0grYDqbFjGn9Sev3FdAmmv1Jp9y5nD5o1pR6Tz9rFtYLoKgsHTFZFf1albjHe2Ltq5Hu4d//rk8Kk4sBB20HHpJ/V8'
    'I/sSbxi+js2RxbrVNDXFsYDlMYhjrTeyOfKgkT1qYahc0rm+W10rEwUOZ3IpXV3Lmrh31C+jMyYCXIPKqBxB6YrWdtqZNnKsPuK5'
    'mPWL4aEqHZgjaWVDZUfjsJdUS53jCMLkLFwVASvoiiBMgyjMuU6xBeUY2BpBe1KxOb21/IsHjyqyHdouwmlUroLTZZhPfrzorNhT'
    'ifGbkMfizgZRXhkt8PTB8arAtogYPkUR7Dzdx2gt/RbQE9dPAINCc4HIed4CobogDsBoSeNBGbJRCQdWgiMYYoBZfmMU5h94tM9Z'
    'SNfRD0xnP0o38E+hGFinF6hMomaXSRMbtABXkB9cl+Q4QshaQ99Un9Ysb2frEt3BZr0BLfFf1BmJX9yw+gLCm51RkSXLMmLLE5AK'
    'KO66zM0b5MH97awFf2giFxymRTS+BQdr6n3QupuqDcDlagmC6ZW0EsjnKiWMRgLpjkIiaNVASBPW9KY2XaB+RPGWC5VqeP3NY+Yr'
    'EAg8GM9otlOzJUseGjNR85HQ0B8y2Z4TaKvw2DFK87UikNnwW05fvDBYAJTxcO8HAaqfqmFjGqgz5/sVMC9qN9ER3zXB9Tssct7N'
    'KvW+Dh6J6nOmPnjDFMSJOGjquoogkGe1Dep21TgIporiOLF2kzCXWKJC1NGXI06oovHibZgZTFGt+L3AGB3pjR/XJOb+UHdPj/e3'
    'NamVj8ZDlG519WvUYrwFzTlzbuNsmYgHtJF4PhvWK8fPTsGXGhmid9YaCos2B+OFtVrX04XJdX8aq47njqeKrkWX4cwiI7LpKoeV'
    'dW7u9/ROsrmx2bHmBh9yGWuaYwiV2uyKITWfdt10OkCb2jJ3LhY6VrwMI0WbYv12w3eTJv5NJSOotqJljeg71+U3XI/uSjNOWfPV'
    'Xnq3TsUloekYrrI6J+H2EQGbKza5fT2AqR13VJy27E2VfmvuE3O3xBZoKAvES8VTVhk4+dxb5XIxHufG9yRwK8dI4bXpiMB9R3Fw'
    'pybmm8m+rmLTlazcOqhDa/rqCyxOmaELQ3ZT3wTinUuLnugl7DpEmyJOVUPw8d3g1p0ai7FOP2gWgNxGJUaSwcy7OMBs3ALwQX3U'
    'NDjdl3BK9mAbpTvW+d6FG3TcdM/uwWBSnsffET/sH06m2TK1d4OjSWVPpSwUW1QJznuyTrGcindpOyZrufSKN00anP/lgvvbSK5a'
    'lLY6Fz6pFJX3K8exYSWo6m156vZH78wILhCnkAZ18dE76ePFq35LJyG7Up2fGhHWUzxULZiCL25KOLEnWSBz4LuyKIKzKCdCj8jS'
    'w44jGRujgloHegzFDPrpME+tia+MwfZ2u1P1vLYJfyNBM/fmi3K1Y1bVoywXgHjGl/Fa65fNxyaxc1oS82W5yw9NHEPP1kvjm0Ni'
    '4ioyG160OQ1Qj9TqvRARnEHoOSpAPc6pkCyV3T1r2g8/5Gpgz4Nfvt7W7XW8BNf1o7n9zTLeTLi9Ru3V+aoZfh08H/D932K9mVEs'
    'BjIK8qtGvYkleMd9E0F1c2EF9CJMo0SDIYajH1TTppgirTXxCmiLl3ilXvXceHzOPWgHp53U+nliZVzI4oS7GctB3bpLVuKPSTiF'
    'Fm/K1jfIxHXfhD1jEoqHBYzaXBDKIxqAs1p7l65g5/408XjRRC9+3rUe2NgBm/G/1nC/xiqKyvua84rtvf0uaa+Cqm3NbdxDChxv'
    '2PUxXZfdIUEff0wzy7H9ovxO7Yq/uoyYeJdm6+cferOOk603L710W/nGCcSQ1nPyJL5UzJbm37J1e9y4MMxt1dgw53owf6651vO5'
    'OTP/Hn/ixR2qcXPNAifWWs/0XA9AqswVm+fla78fKahw3fuR4imt5X6kcRzClI35GhhFmmPr7//mz+m/AGyd8VMjSetDfdV0A5P4'
    'jSCmxO9ibxZPRBPXQVzE6lMVupAD0lcfeLf48uTxAbR3PNzPCyI4Add1d8uGDNu6R2xXMf6ynCeOfrh38fkNZL/3QXtRpmVbQZay'
    'tHx3i99hEMhSZZ/JWG/r3j/+rVbzSmz/xplDUU7QTxkwd9k7RqgGom1gG4x6vquVD6PqSkfT34ftp14vixr3PzhwGtbJQJwbdWrW'
    'jbo1XWw0OwYODOxuT5tkuIAJ6i78k2gYtjpiMHIvwOHW8KIR2WodXsjdeg8vqg2qU+Uw6MFv+xWOSHOr3HcIQkN7ROj9myjMu04z'
    'LahEHTHoIO1iNFvGX8vnHw4GAZurBX92+GSPlhb1nq++LhdQ5mJBcZC9qUBhMLAlGxUzOgy+o6W5VbmD+VwE/paM/GFL/PtgO21D'
    '7a3AYW3ubh3vwo+C9HcLAXyThL23391iarpVj8+VpdzI3a2WGIGM+H32USX6g95WcMPpd2N40LES/zYYrbbuPZfnYLT6/AZl3Dxc'
    'YbvMeL0B/QY3PDCRAXDD70BLTeyydpCltVoeIDmArPy7ZVbe4VHKI8Iai1E4NwAbcGjnR0mYvsa6NEbBl42dw6AN8uzMmdm2fNM4'
    'SiZenhpFkmxJOIqSrXvsYcBQL69Iy9ilC21AfBTntEK4Mm8YVI8/OT9Bj2n1/fgOkwTouvZhtVD0kKM+M2/fISz74gEMfOdErGbb'
    'HdruEHNpRat9u5MSvcnjcecCy2PTcL1X/wWrfvfwycnO7omu+wVIB186HWVlmc0HSTTFBYQcy2y8cd1rqLvGyl+bsQnz9RDflTJN'
    'oLeB3DTQBnTG/xvBzmmUjld1wF2zrr05ib2QGXLoppYFFIGav/cjq346IygaxryxMGsT/JNA+IhDEv54AP+X/xh89G6VXwRM1Br0'
    '7PoVPv9ihybs+RdfPAiOolPiGFTe+aMrgcd5kcdXG3kDmtG0xhFIsMkaR6ChelkgrPMEkngFnoAz+jyBK2iqkNOpslrvgypNCmsg'
    '37w930UJWyXt98ywDUSocDdbV7wgenLPLc9CTMUvaR3UBbcCYrxQjCH8A+HMw6gHRy7O4nI8M3Je7YTG/egNoS+XeHjOGuyhzONR'
    'BL8+kTJwGNIHzsUEDTDqhTqNJ8rvGoRwnP3JfQnrWd7eSDiQkFVvblkrBdeZ4jXClTqnHYhd26vC2NpTD68PrhWLGSr7PnJHyQn3'
    'axeXfQdMpl5+uVMdylbgg1emTJekFKH6OTxOiiGKHQAkMR++1pmTad9x4NXu1sl00PXkZLrn1OfHCLHxtY8Iz6JcXKi3B9h2cnR7'
    'G2uBhudpnDYrcozL2/L34XRlXdXi/Jg1D2s66OQwHaSZOJ5lZ0pyqE7EiY+C0JnttVSpviSlESE9LtLJulQqs/6+7YbFPirTgdQu'
    'x7VG8kPwnY4SuV4LclWet66CU1XutoM5z/Fg0e54sN9mI+/W22YrwafWNgu0dtpKYxbX5uz2mrYTFy3ggHu6JFarf2/oxlH/2hPJ'
    'ys8YB6Vq9VbmV6WR7cyIjw8ANTkdrOqyAIF6eJ2/wrutTtVsHVeOnecD6RsHSBVdsa7JXK+Nm52T9RoZ6nXZTcko2tSNmN/GRp9k'
    'vWaOem1+K75XMa+h501vZH47XoaW6tzt0cUv4Wl4v7/e6Uul7Lxvj5wTX/OTDK8RsqklXhPRCnOM9pCKP9TSvCsnGwwNvchnVAk7'
    '7OVCQ4nGJTdgYMs1jfJjEylVNLVBPeAV+pqol93eOi/O/SpLW2kc4ag/7eqA6K5+aCvAvp/r/p65hPX77BeAN2d2/3wctTkrlwxt'
    'BR0XzZv9nXtZndMlOfoFszuJCafoM4mohUGTYnokhunmFsjTKGdeNB1HJg+YJnbrjD2M5ouEUbkyAVtBhDigiWd1vPJ1OMogDB4Y'
    'Ng8aTr5YLXXZE+OHh4+D6C2RpSIoMhJL3sSnbCGGq16FMfqcsTOL4E3MhmKBah/bmMhAmU85E/kqjs6Mu2LZyeSuEi3EibNfS+Ix'
    'QjrLPdvCGbWCxuka77jcXTsKDgdd3LBBnwuwa1FI8uec6WYZJSufgXbbDN/IKtnAtvjZ+5L/lzfrbLlk26VunFBHcJnrCrU62fsb'
    'aj3mO+QPwvyKfTXZ+25fCaD7KZsfsL6SXWZS2QXBjUBbKE4BKRAzZJmwhS94tbp1nHadKN7kMYjklfpks3Ofbt2+6dN2Ew8X1Swm'
    '045L3sdhKjhl1six2KLK4V+tYbUDqF9p3FhJ9x1YQ+Juto1D614/uPUr3xBgo39g+5EjpkyWSXRATbUaELbkkaXgGTSSoALJ+n/5'
    'y3/6/9Bw8PRo/8lJcCN4+vDR++uIEzI7Npd2YCHhvh+myYrdLjsHxtFbPu16+IgzwyZkz6Q8hkcVzf9eAfz48OHOwc8AtLDSEaDI'
    'gS0bcPdddVOfvdtWkdrXKzBQjRxhwMzCc3hhJfBLSqP1RmEk3mnYSV5Sk6Mp0GAxjinIXXeAVRbfWnJzAy1yG2ApLXKOXXML466F'
    'YOt1axNgTZ0rqZ8DSc3S19FK3Yabo0O1IacPQlz2cDDPIjEHF7EoXs9GNJAdWvLRYbUQ6mFH3Eocq4o3mz00eUAXQKqlzbDMnuHE'
    'bDc01vZeB+rQuj9EtPS6fymnxBWQ0J8bNWjZMD1igkINXl4tTTS7mUDNEfj9Dp/skqDsnOwK5IVXYuBfVm9tUj5gb+vvlT79eu83'
    'Dw53jh4Gx18eHp3sPjs5DrpfHBw+2Dnovb+OWTA2Z0GXiT8P1FHCejC5fNuZFhimPrIzVF8b2Mqtso/zQzbEJiJn649Mkndv6QNb'
    '37jMk19H7HbKrV0CtzkJJ83T/EtDrQhjE5F0zOYJD6NpuEzARTMJf2Ld4bu2oqot+SLJRrR6aSPMy/ES7hBJ7iVOnQghn9SYD4W5'
    'iCR+W4t44kvA9prI9fttmjzWprqR28E/y7K50wtYofL1IHg2yIKzWUx9hU4ahgHs1I85ucvAfrcO9o83wtG1kR3ZEBlrV26lAxuQ'
    'XBb6JKeChqvLU4dBI2NJRjvB8QhjdxzqMyg+Dm4Ob37mhs9BVoarZLePnPWWx6h68HBGP+j8YQx+cPXBD648+Js/18HfWj9QM7L3'
    'vxl8uXfwdO/o+GfAruaRnBz+XuKhKY+pJs/u6aEwhEZXVko8pA6rHjrqRpB2hoOwKKsMepfrvU7cg2f7ByeD/SfBzn7w/Gj/ZP/J'
    'F8Heky/2n+zx5ycZ31uFY7E4V1cK+ZKkasJ1SkhWOFnQC4XvbyAfOGfMT/cODoKH+xx6c+foN0H3s5s3P0Z38xi3jyTb+/rvA0FC'
    '7uQ36KQayMIPWx6mxSIrYhFQcUUECuWtMpptbW+Vs2irvzUrI/tczk6dF/yYl2hWmmdUEE5Seg3TCX1Kw4l9nqShfQ7TtPoQhtUL'
    '92AWR7nUGOfccpTHzvus9L6jCC3CmEgoJdJTRASNsiGtJamWDaVHURJJVnriDH1+aibBIstNQ+lpHsU8gCnNOA+IHtLIT4mhuHJS'
    'UPCMhoG0MxqGJmXj8TLnovyExz49ylMtEY9+ImooIhJsQp431aSh6/TYmtjMijpYj8RqSvrELzG/9M1LErV/icpGEdR3iqNz7Fb0'
    'jZ9TfunzS9ryQaY04U2RJ4seQy6xNjXkRzcVleA2GowX5Jt5k8art0n9m50KKL0rEOPFQL7lC0ohtOQSHxZLfujLQ+4myejYxyNu'
    '+nKn+Q36bB4Nv7V84gle4nr/dJlg2viZX/rOy5pPzTKob0mElUvwA2WmX/81dl4Fb8cgEcwEUwb6nY2993HsfafPzrssuPGSZG9e'
    'SezDgVfXOBTQuWkhbmvU89WSUGOUvonzTFFJXgyS0Vser/0UZ3na9o0rxVGETjQ/Kwboc1FLlyILBD80ZfBiC9ELUYp1X5ofmLiE'
    '8zgJQe34KQ5BAPmRn5vJYeynopJZSPhaFJSOIwl66GtS5CTxcuEDCl3FzmkFVou8tH7RT1HjG+qE85wk4r1DHienGDQ/T9qTo0kt'
    'WddjyD4CZNWF/IjV2J5qnt1kXqAwUtcvcDagL319ucYHri3PpvwtxBqRN33t8+var7prjYGYE9mQsvlcdgt+XpM8j2rJUtE0yvWD'
    'hEPi7Hj0EyXzPBrxBoonnHBx5vm8LbGRU4kXSdvhUgkuvYBSCiEuSnlu+RC1FeH6VuVsjvQZP/T5wU+g35WbIltdalYnHnU1yWPh'
    'p3L2BTzOIHkRRUyZGimcraS1eMosjTyWnJUe8dRIpKxeopDofJHH33EX+JEJV7GUp2ZiLSfzQDS9GWy4t/GY5Xjsa2pbcthI5Vry'
    'pWzi9MBrFb+Rk4BMOEjNlqAOb+IxP/X5aZl5aUz5YUofp6eg5hI/DfSdnlqS6vlM+SjVVDxp1loi8wx5SAgO3OMnJnB4Cr0kYWV3'
    'AZY0INFa7JBKl7VlpvbbYokJ/XZZABm/XZaF81YWS/umHPBK2EsG2WwVOW+rWVR95Nyhsr8hKivDcua8zcrQvjEAJPOZfD6Tz+ZN'
    'ip7ZzEXM3HMRxljORbhy3oiiVW+8UWRzJvy0CTIHOs/sGzPlo6zEKOl3icbCEQPEec2cdy5xStsYkhCPAlniU//9lB9sApeZvZEt'
    'hfnl2ZvQfQujN/aNMyfzQhpN5hnPBB54ZkyKZDtbhZKI439kO0vw4KYk8lQlccn5a7Q/D1+j/fnr0H0Lo9f2TViS+DRlrkJQeESb'
    '8Kn77r2iBFFgKYIHzkMPaXzqpcwzWQYmRdhrXlmTLNKORm9yRipoFIFk9F57dT/z6oDRFTd+KuZXWB1RqQvRpgnzrRkzzZZxF/VV'
    'duizTPdb7MBZela9pa+z6g2ZSfAB4JKYwUg/zguDW16QdZ5nDPEsZ4hnvJrtW/WCvNqONsr90WeuwzaffZsy250yJ85kQ595Z+Fn'
    'zpeuEn5nspcl6cp5S4UGyivnpiWP/mQQNZGDBF/vXcRdfeUSZzlGDostJmKZ91a9MJMQJrxJ8QEf+ILaq/9ZmJRowdz/IsoWLBPg'
    'IUpqKV4W2ZhDJvf45aGSNFRP8HNwqVh2thyXC5Annp2W3rv7ypRpzrOCC/agTFk0d97m1SfOS19JomfERKo8o9S6ZDzXkllQiQvJ'
    'zt4MIZkUgtn23fss5DYtWcKm38hK3TNffIlmcV0+oTxMpuNSBRz3jX6qV86dLScJz/gyAW0+yyZL/305qV5RYpXlIMaIGUTfV8u8'
    'eslW1RfOWmaagI/LlX1eLTPzzNSIaCYAj18mPKG88ZyMWfUyDlNDubhDY+3feJkl3ruOZ1x1uJhJEfxynmImZdwEKWVSDGQcQNQa'
    'Ylooa3gii3jCi1tfMveNt7g4591hijtkomYpSvc9LnLnnSWfIuQ9hzcJd3OS3WrC7+jabBLaZyedB8F1nHEd0VlhnhkssjMVsgsV'
    'K86pb7IfFXY3KmMsEkSBAGMQR85bXPLUyRvnFYUB2Desv3LpvkVL+8LdY9JEf5mbmqXOS+S8SdYw9fJG7mdmpNLpkpUSiGE1KWT/'
    'lU06wC/ocZYKRQ7sxPDGxL3XTSrQgYG9FqK5zc+BQ0HjdBqORSsT8BM0MmORSWPEb2L+OCzOItZOhPCLkiSGJyBOkakfdUsedQQP'
    's6XpvavTdNWVrrpxK8umIOxT1mlmzECjI8zYGK4mEzESMJtOed/CX1TEgEHPRyPRSACTZjFL2rHhQoR5KbhaHq8UwEoeraTAnAvM'
    '+YWBZaBUMbcE1pEzoonsd/TTQXVjEbnoh1/P5OuZfgWnodnpoWN0Y5IWF1omlHf8SgKUEpyCB1MKy4dT+YEzzrTkzJSkpaMJE1tu'
    'EksafqXLIALSa37SjpvEM5to6I9+0EfOPseWxKnyJInEyEsaHrQG3MEY51GU4krEYCwwtTguZs5MbdRkGVDjx2zZlrysZeY+jiOm'
    'ZXwGA3KA98hLcF+ZEM/CfCyshrUWBWj4edbyIZzps5cuoh7JPHHJqKrPor7glzJufJA1WEYxYzSe8pjROsbRRS1RVFv0lrF6iR8l'
    'Nx4ld5Uoe0xKPKgKlvKyFNnSvNQ/sCyaxeMIimBInnge8AsJpNk4jkwiC6jZ2HnnhcbncSyRjHXs9JDVE+IsdpOEIecTXIGR4y6U'
    '1drFWF9qn5jDzYzucJ6pSpEe0qiWEtUyiY5gEqXMitGTPPb1MWpP9hO5jgQaMk7HE2elh0ZC4iSg3O+W8fi1FJRHZPzdkh/8pLiW'
    'JGJpEqVMucU3JxqJoyStpSQCBpOicNZjBoalnj4wkBfNZBYLovxNJupefcQWRE+MVn5SnHlpcjQDsmCOYvCYRnpAwy/1D4q4tAcW'
    'kTAqeI6EKaLHRqI+uYmMiulpzoDDQ8ywlCc/Ufi2PJouOV0fOTs9y2MjmZ/rH0SCDZdlrOp/+8Kiqz7Wk8OWZFGA5Hk8wgd9YpaF'
    'HuVIwk+M64nC+MFMW/tiX2Rnoudle/K0lsz7TZQstB59xAZDT8tm0tRLEkHqzHbDPLNK90w7UU+c+oncg2WeMy+Hhzhi7TmSOl6a'
    'qg5D4j1ZH8gPUBGGeVxLifw8gnRUTT5hOsrPEyau5jFqJNNTLbPILemEJTNx88rSyiRlybpK4d8qQbiJLGeywQ8hn+fJg5O0jmp9'
    'cHHHPRD/4mjn8eOdo+Do2cHe8Xs+/v6x5+Y6lm9kLHeDF4375bTFq4YzgGq1+BkNmLr6Logn252zaFBEUaevPrFfdGTv62iYq0VY'
    '0uJNt4MbX4/Ooq+Ljynz16MbcT+ICQrbnf/6b/7l/9mByXUZnWb5arvjDVsdROEi6/arreewGIq2YBEn4V2MA3H1Swtn/bSFjohD'
    'n4Vlp4AjlIKrMxGChq+MZ6q3B/B5sN05YmNZQm6p23quersdsAPesnKc7g7g6+IXNAa417Off/siHHz38kZ/fPfe2LcB7gUX/Q9c'
    'gM2iML86xJD7R4AMxbfk+kvBl4Tygm9MwXONxJ8s4A0yCAsNKL4RSFzbFaAknf5xYDqDBeXV4cTZfwSguPyWolbBkIHTOpzxDIOn'
    'cFs/i+bG8T/z2RVaeV0fRadxOiizZtf7HXvnsWUUXS5Y3D8HXS+L+z0aVJnRn6/PPq5G9f3f//P/7//5C29czzlKVlQU/pgecHUB'
    'CZ0cnnlLqpX3PAqWxTKUW0+TJRsxsD0UTir4DokAYA1GHMfzRRJPV5sxYe2AujSiHuIPdL/pf/OmD28pd+/h7/XxxGwVV8ITk9nF'
    'ku//7t96wNxN4vHsH/+jD8pjsyGxOa5SFUObx1JiGBxEpQM12Na9iVbBMmdPM+uXld3tNkPTdv6HLyoS4QcjJtjpleDVjYtzhA8f'
    'ReeEMT2hfqm/xv7mv/fA9xQn5jSqryA7eUA0X1iqCs6IHnG0CPX8DvwdBo8pUdbXkh3h43NtdcUF08/JDxwAl/1JRsDWgxGfOuKG'
    'pkNJ2eqVVtYsVjrC1KI2jmIeFrPBeFleDXORm7pP+WURjTZSBHGCUsPhxzvHXwa7z06Ck8PtrUBUHfBcHIq5ntrqielvn90a7+jy'
    '145XzMlzXKZMSNZYVh7xfqbMloE3VIfXpcgoA3Klv737HiX+r//mr/z9haFyoFDxgf8VTteEeADzg5jtCOJpDL4FMVaIqJR5lp7i'
    'Atqc7+IvojF9H7MiqYY7csBy3dFIqfp+cp1RHMnBDiyDC9WNDoNHMXBeOr2AEWQR+X2u0OYoWrAPUlGh/kGgzYR1vgN0eCO8+x2r'
    'M4PLW7ugWqnS12fvPulfgBx9fcunRf/qP3lzcbJaZN4U+BCcRCURyWg9XztZStSZ6JKNWjvU1R71PubgQB/d6vQac1ip8Ys/AAGs'
    '2jbKYhBzsOxrrZmY5AhQgOwsPS+iZHqOw4dzBtw5Ca7nfDniPEon58zrpMQPnMNP/vlimcMarMfTK1cidIr/+l97U/yFmJv4C22f'
    'mt0imXArLolobA3hSg3+fkcE91WAE0d8oixdYzSGaxbw/NNEhUfxW1wr4vyb0YAHO+KpB6h83gGnhgP8cYW9TaBDXoCOjQHOxUbh'
    'fMIvbOhwrpYE52W+wk8R8k+SZa/xOw/5B1bR/LWUz2cgkuesVjsf5+F3q/MJceDnU2LIzhFN63y2zMsfCHX4q2MiXQFVIM8HAME8'
    'Ik4Ch6JEfwny9AA+uteA+CsDcc36aiPQGUzorsnug53t0Afs1Om6uMuFMAMzaDmJD8rP8yybn88yi8KjEDMTljQv9EC/fEfoPCaY'
    '/jAYYitT23kfN8FOsLE9QAdXTBInYxRNsW+EHN9hPe5KjZuxV4aLTgvQOg1AklA2C9MfIJbh5ZwoLkER2xwhZVGc5yFaPOdTR5Zs'
    'ZsoaXxdmD+NJAGQS/EIXt+4HWyc4OgUyguLc0XS800paQO+XbYQXZb5UOLvOsERYOyM57ezjTsBwdPYGPRlNo1OOISi+W7JpyaoX'
    'XGtnw9TAbpHCQguTGeoFkWF9z6Xaqrlqmxg+oDzXc8dzOfw752PKcz6dPDfnfBhHN83gCv6cmpwxlc7OgDDnKQ6V6Y2yZOkPpNe1'
    '4dt9mWUEI2cvUxcU9sJpuYIbLhM7dRm1sE0HRPIQFXD8+g9qy4Wz2oFZYpfJOOyEyYe7L9IgYlY4ionrXHmwP5nFVopkGGGNoOlh'
    '8IB9vmALTREGGhdu4cmacPA0DxezguM6wSVWjb3mjlM24tCdjnMCrYaSGKrkKv3/y8tEsqdujYUjkY3yOJoy8qArsIUoLBrROkea'
    'CUCpWEOjBHvSgjw7Ez7dx1EnYpj+/NEm5A4PtMPXotbNSfib/8PXAMJ5oTcHXxJ/sQqkTUQhHCKuCgCMBESkJPJBC5sW6NYAog/i'
    'CSL2DSZnLEpB0WUUJc9TywwcUlVqfmwQ9ecJ+azq6PUX7Pd//xd1LUQT2rxY2dsYlPiwpOegoHBTwLJwASVaCA84xDuzXp8WaQjr'
    '/kqZ3wJh1dkVf2AnQpVeDv2PBjlc4l5FG4SML74uBi+LjDCvps76n/5DfR5aVZpHVMdAylvFRJJA0KU9ew4fmUayZ69kNAMk74C5'
    'KFTLOc+yul5CxwFfj1RRMr0uq4WC0ORTUX9Mf/n/Xj6gA/jLRlEdjlXL2mMh9LqS0gvKliXittbTuIDMtg+MSkYD8GPXVr1QQRoY'
    'W7MX0OB1qS+sUUJtnjLvL/7zFadvTGyz1CcWcRi1Es3JMHguR2CsfTSapHEGIjUNWPyiqcwCGn50v3WomEKEW73uSGUGURKj/DYb'
    'nRPEUxI1WHCGl8/zecwXlc6JSS9UVKtObP7T5UM/TDUSLNV+Q2rXKT+NUngkNhNfaZNLEOhgGkWJYDMfiBi4tM/1JMxfs2vY+dXO'
    'FpAfU5xOoCbnct68/u//w1XmFWE44eDEOVfAjBFKmtdiKH7V5dCzIPpJ3+DPrcHG6EBYYh6A2bzuXHJJjIbKgj2eeogLP36FP3t/'
    '988vHeBzS2QWM1wS9PWHFlWZAjF/xr4mArhtycbw/DiJ31B32oeKfTq5qn5CMtNY4hTzhrOBcEWYMn5dOx74ny8d1KEuu6CI54iU'
    'GHwBKQARRRyRp0FIo7ccmVj8WpLE3T6mKIkWhOPlFUdlsptxyXRB7q9R1P/t0lHtVj4mids8JXKv7nGKIA/ZXUKYQmwf2yMb+DGT'
    'YzBiugs+bG4f1GiJHk/h8ua6SOkUNWPsEqDPIbSy3H8+X51DqdKTdTgP66fC//5/vHTonk57tiqwKfQdlbzuhDgmhU2Yw/Z5w6RG'
    'BvPsulwsDZIK8v5O1IR/uZLaBP7nyynlblgypePiQiNT3iNwf4TQdR6VJAeR6B08iGoLkC9riYixSsO5pZIvPXuc45PfHOypNU63'
    'sDawcvTJou778lJhnFOgg46JDSbI0yHgaOdcTkbOf7eMy8goQHBBBHYk59MwzukjrdWyXPXs8YlGgFtsB1s7b7J44h7pgMelrcec'
    'OVXnNR1uojMMdmdZ5p36iEJfDQrg2Ifk1070dhYuEYW+w5qSjpq/5/CFP9zCfDTGY06Jz7FlYOcIJOUc00nvqvZw9Bwyho454u64'
    'fAQWvn9CWzvjFrGzftTd2jUxsfl6dM6PYiAiz2q5cc46PGt0YRPgBivK6x0WoHek1uBGoHV2WDKTU1lMXzDjCBPGZIg4u6CzE8Du'
    'jPfZQiErtkUELfulswbAI2NVcW7tKc7ZHQsekHG+4MQNmNKxdXSo4x1bD+HFP4P5xZk1zREobwedY7CuaEX7i3dbC31ZrevuWZi8'
    'lvlE/3AoVL2dZtVLAyFOxHI1QBGcCFMnxjkrdLnfBCU2FeGgwEwm4F02FXfM7V2BZp8oUMmAi/jpNPyOH6j14S8oCzZ8kF00eC4v'
    'sCQ9Z4VIsuq1I8GbEBqQyVJjUMCzbLUG3SoJwCc5eu1YjbX3lc9dziWWgn2gXuvTWWjSztoWk3SL9vckYn0g06JcnLwXQbdj6gVF'
    '4JZoOQfHQAMRh10LCGNjtKafRM/zSfsMHomyl5qoMnWkAZ66Dl6xWmKWFHi+18FjQgAuxcgB92mgAC7PszORI/zk9f1oq0Q71FGH'
    'G+vQOCyFnVpksQSAYHEilJk0cSGQtr711ipM80QW1zW9wL2DjfA1Oaqx4FCjs37K0Gn2NHMJwBpZTQvxdC2gSDQiKhyk7F6cKP45'
    'iUXwIValbABRvbBpbx6maynMDGIdLwzeHbu4lXaOu+ONdh5aZaW/q9wPHuOwWhwlAEPC4OH+zsHhF8/2jD2KtO0zH0d78PG1px6+'
    '/sCtgXUw3zzdOTnZO3piuBUaLdtjqExYBN//i7+iDZFEIJIJMQdy3sKzMsc2SnPyW6gkQfbBLsq/Qrx/bwcvtr6EOJyTvFFs9QO8'
    'KVXXN9khylmeLU9nWy/NjNu6i0blTt3HM69y2bRs7cczrb6lWmAP19tW7Qk+Sr2oh1+5XvuGaltqBZVfpg4caoAYZUlpBl6wl23z'
    'RiQXPuKllXYo+DXXoGBrZpBUVeNV64bde2uXeZ9cP3dgj0w3p/Fbmi1QNeykAa4OUTq9RqsIpyDj10hr77/fTGMWbTN41XaIJrjt'
    '0Osl7aAmYhHXTsAkzxYFH8+YWYhgVOQlcdygBfiODIntg/FbqQ3Gb4WHV2uG0zgORNzehiiR0kkrwKiTcK5iJmWxTBJMypxZ4+XC'
    'DA0XOJinWodRfgu1QdgW8KJNEJdTNaGLb0MbyEDEee1szFm0tgsC0Xv0GbZjtETXdtyrtdZxp1buoqmWl8n6elURtnYhgESdFZxH'
    'O7kKMYFOQhQy1iChvd9+A7V+1xpAkt8CUppNwAExfDRDhh4bHzE+pWPeLwhbJnqH6wUagLPinMSgIRFKzwmJ63Ei0Y8i0RvR+ttu'
    'J6fCr7YODifecBNFO3L2HWQjXFEmrjUYJ0s5a5m21CmSloM8bp1HVGeYbKOa/TSY5iQV8Msu/HzTwm3rJB+fZWsq9K1VqabHOye7'
    'XsKXcNdt3ivgWyZDmRQf/F+PYj3Tg9cR0ag4re4Ph8NgX6LApJlo5QROKBIWr4N5xAlfZmfmvHafq7rfHCC11ZkHRZbnqgn2Bvgo'
    'y08hG2iF+4G9eyzN67yf2KssyNjWBpFfyr7KltqI08Zv2KIokCv0sHrQpthGIuCpoXJDRbqVnsW1t3MWyTEoGHjapxugOyZBBi7J'
    'h7opEwOMyDXqZYMNXBRgAJcDVez6vBu2NotyMmEIQZIziWy0DRutxpyJs3T0V0Gs0ID8DE0BerUOphgKW5UgsVTlQ332WM0pA6EN'
    'xjyr9vM0a625ZPHTHPkEjdlKEhkIQ5nE1/lKFEMcYVYa+BLf93lSiX2WGSEo3ce35zMa8Uwy0OjZtTkgyJr8VhRlHckkswZIzXmF'
    'rhOZ+LCJe7BHgi09owxvQJz4oFIersFTwbpJxmJYc+nRWsmWMsTnBiXgDD2JBHngSRJ1KIKByaHdMmBketmUDh7v7D8JDg53dw7g'
    'DfgPSUb4IIlKiVa4s/8wGomG3URtcEd4eHDwm85xcLz35GTvye5esE+/Bwf7X/DLex6DOPzAgYAlxNu0f/xuCdVeIRj18DCAjyxK'
    'hiFAF65wIkQ37KlM9NXOwf7DhkT0W5Kgy3OEUHvx9fDr4qW7gcg/9seA+1m0zLGRYguApCobzvk0nET2N07ll1DvfBIXRZbw6jvn'
    'Cxew8DhnFMaTlWdZb/z1MPt6eE7/F/Izph94HOhM+If/TLwiYXqaYC88H+umeH5GxCrX1+XiHM4tlxwZoORP8hQTcPLynGN3WC2E'
    '4vrJVzcexcm8UttzdM7gdBlPcCxqlOC7R/tPT74RXfgXz/Yf7lXSpeLSiUzBnKkTD3gRFuWAnR2Ke5BxQjRTXGRX95skkp1jzVDy'
    'amZrQ6N9jCbneZiyXS898v0bmE1n9DekeYQbCEpH0IqI4TVEHd1SQkawgiGkYkTT6E+hWlW2eXAzliaG7L3g1k1X54BLgBqrGTZU'
    'jrKIhwb1V+f5zsGvj6GLO3r25LgzDJ7icFm+673J1qON4VaLTeIPGbH2d7WIoGS19XcsT2PMXIirykNz+ZVViXwiYGdf41kUm6Zk'
    'd+fx3tHOuXBz56o1P3/67OAgeLCz++vzPzs8fEyURH4Pn52cnxxRcvB8/+RLxj0D9RqQ/10gSs9xo481fTy1WPmhFQtQvm3Ix2mZ'
    'bqlNuEq99W5DDgqwMs6/Q4AEWsz8i8XM59PM0bh6qEth7N/x6lrQGiK2CbRxcX4mKMoWFqwMI7RRDICvqXNs6uk5GD+iO7gttham'
    '3//dv611Bl42CrFXDDowFHBPMaAmL5xk2h7FzAPfo0mnFag/uMMeNJnmNAC57x6HdaG9GROswEIWwe2Pq3PxjRB1T+eI1MBTLD3F'
    'KS3HSTxKWOHIdx8/roBYJwef+Zj6N/8u2F2W/mkdU4HpModHGQtKXlpwp8EHd85RnH6XbulxXCt4r9L7K8HyuTnkwsQEXWv0Gept'
    'Q1jSrwXiGdCY1gzKbljB/+q/0xWsZ2E36qdp5gCtcbu+beyNRq+6/uylZd2MhBuGyoPNRXgbSgl0G5Cm5YSuDU/qi809Y6PVYw9m'
    'YeveeuDGeKTnD+F8lEStSNDemytN+yEuLESDFOwBgvzpFc21I98pmFM2km37PP/Vvww6TsaOWgU49YdJmM/FwLWyABEZLFLOnyk5'
    '62xHGa2yMMFh2spIdg0g1DrmDb2KAlwb/d48U1v5hW8nvW783a46vznHmS9+i3BCf9VrDy/CMfbcBJeG1BUQ58rHtOOL4V/v697a'
    'Pe7/Wt8nWRzmzBYWFeag3C7WcZjj9B6aJSKsLWD66frvAXgqhud18D5Lp8Q5sju+cgZlP6FmF15Lg2kSngbw3Gd5PvFNNRJ/G5xX'
    'r25cRnu6rKiDYvVcVGr8+CXsNFma51Tz/CWfySbxd5Gkm5cNROuv/8EdB1DWWCixbQ4Px+CqYU2ILBXDAAocyPhyJnhwePjriqDd'
    'b1vHX0boVE9M4HgYpt9eP69K5x4vExpEgoU9TsJ5dXK9Dr+75ZAZ8+6ND2+c9hDq68XLnt3m7gafePTsX//tphYmcbIkih7PFziG'
    '5XsGiq3stc5BVWgyT1dNZKU+rCFgKpkcq3t0Fe7Gs4iDBKOtCuzGhzrUG3OY7GYz9gtosOx+FQnJZIVNZ3GMOrsQPsSuqmfiznzF'
    '7DAuekAHeYqTQ40jPR5Hi5KxJE4NkphQt7BaKxZJXHZvYEe2UP2coGqCJXE0cI0rvIvBsEomG70BzyA6moII54Q26dN4NCL+tpi5'
    'KkiRxAS8dwNusswO4AtKHDWYyf16xPvUu9v9C9y60ok2QZy4vOkeIn3dbO0fAk4zta3cEEr7nCaf78qnIa0e6mP3DDj2/PDo4TcH'
    '+8ckK+6dDEnc6p5xB2yQQBKg8q+ycTjSjwZUd/wWjoBs1ILT3I3A7bsJ0DwNPg8+u/nfwDBJQIO5QvyB0xSXovqVAhEMx3SqYHAa'
    '+Ty4OfwMLJ8HmnvBpxYwHOO4MXO5uUgdIyoLaKf2oGsu2oRArazH0a6I6cIKiWlMN+/Qz+d+c4PgFqV+/HHPCXfPGV7EL3ma9OXj'
    'Wy9tV+lT1dvbzd4ixJs3tRLCl88WEOW8mMNcRB1QELMfwlyLFgrWAzOGYwkoWy2hUy16pGUaC0hm0FZ5VxGPWt1ZLNhTjHCCBq0D'
    'doZLOeqH10OC2F5I6JyfmdiUApT8TPBcqTm0BwZmNNqzoeoDh0VCAk/3Zp8AY+uib1VlVQg76RQ0vbqszB1H0xZrGTXsnO2HLYTo'
    '1qylonmxqdXE8PoXeAwXy2JWlbQ1XugTJuzChB7fqcwbbAVOZG2J0hf6UbypGFusx6V1pgCqp0qY0HoW4cxAx1yHrB3xnDC5Zl9y'
    'fdOz3+q1lLGcqsnfmstysRtzGYu4jZmMReDmLOr/an0etqDa3Bs9c7tCpjDf3CF1BbIhh3WzsT5PAfJOO2jQCRD9meMGV3ETc8ZF'
    'HzMrjPysgZFDsOk7ZfdmLfZw8DGVk5V0q6f1E44ZpQIsSQShRKfFfsGc2JALyfeYtYG6tuwmxR6cYH9dqDsn0WTFzjDc8tUil7ql'
    '3a+kzfrC3VB9P3j10a3go9uvbOYOCd/9TtHp2fWItv36DSTrkPNybYCin68G0Ysqrqs9erQkFOwOq7jFuFos5AeTHOqUBjmwkpCB'
    '1iVrfJ8vtGxGxn3huVnfvhGvcV8o2Jc76JsXyo9B3k9+BPI6G+KL4XCYRmfEZJZdU1/vpbtr+PG0mZLmbyKuGl4tRTfZD7I8JpoX'
    'Jj0bx/pDkwS+58Mqr92gqyTDlJkSL27KZu+8151xybw2atoABCeTgUYNGG6H3EED7x7GBW5bPSjT7uto1Q+ixN3pR2XqBn6VUKMa'
    '+7XbwUWLTCOIU04J+voE5r7YuuLBROrumO8c8x7f9k9TYLtw+LKhY5uz+bxg951//Fv75UrBxhHStiizxdM8W4SnLNUY/LNsqnYt'
    'mhzb5guOWU9AsAFohyyzDCtXPegN1Uki9oqYytsyMien+cbxdeVbI7g9Zdb46z1Cw5sS2164Ap0uGqhESn2/oVIfPfuzP/uNBhhl'
    '04parNQDGJ0WszIicWmikeqYnKUSRBWK3GjyfqOkun2MJnFZdbSbLcp4zn4VyrNskGdnvWphJFWxbtgPRtXiD3n9juxav2mWeNgu'
    'c40ccQbZRu3Zwlo22hJnw3BUVNUObFU9QyW55J/8yR1sLKKFwYHRB7IrIKYz4eFOnoerIQIxdd9J8W1bEdGOWxe0cr7pBzGjZqyR'
    'ex1Z5hbLMnerDrpCjIYYXubYgkhaEYy35b+V8t+ivIVD8G1VPuCyL74lohiEL+LBLaGOoxff0qPlxu/zWPy07eAW9Z6hNKc5kgwv'
    '+1of5exXhZxdODBgQb4akeT8ppsvjTB1xB+LYLmAUvdVQihTvnIIKgxYcgiJo5WPYBUyTZfffbdiHoclvn7AlQSsOago7Vmi8rYv'
    '9N9xMrAAc5b4AvLj8G0NswuSVKNCLHVY6yD5bUXz8C0RfRbvUSVNzqcE41sEU/P+x/R+m94/ueOIfMUyKY3EZ7BEEQDGaBNInCSk'
    'WwVBDUmk9zarMwgexn8LF+/a00AUDqKsex0vsCJwFXka5kTASbawrIRdJlz9gAeA5aFD7AXq4D9yI5pPZPDuGj9L+lXXHFaFs94L'
    'boJH4WcCjq3bCqUCGuFW3jHIt6va+lLwwmM+TRHL9fySSAEfJPNiFk16AbeUuCZAjLfDR1YYq7XwtyHQsKvEipZyOORmQTX4ASqa'
    'IaOXQ0+c957WYvgjxlFNnIcLYtqo0pxL9MzaUD3lr6FqGfDlT0E3tNf9JLiJQNQa6mIvPU2g7vrYPSdnJcfVLv+huWeFWDIxSogm'
    'RqyOIJPp8YIuTLVqsLioxgwagYXjpHCgFQ68olGgOfQEB80LJYjIG4mNA3/97PY85QA0HJahCr4kIV3gWF3CIk1QrQbfQwiWrREH'
    'uNPnFTv/5xB5GtDvLJLYeuxCPjfRRjj+EMd4kdYQeGZrLsHDIgk4Z6KVaIBqCZEtAao1oF+BrsDwl4PIcDdiHq8G3TubZRK2TWJM'
    'cTSqUyRx7ByN0qPx6jh2kwm0VgUKSjMOZ1jIEOcaQJXjEL42YcPYUb9YUW+tIg6kqLGmgDIacssEZDERuKM5h9KMNPiZhOEOZXq4'
    'X9IM7CckotpK4t/JlAHWGriDZRsTtYchAlsAQGEqMU0kqi+xABgCVyqd02BqJriTBP/ZEuf0oBwmQAT7tJcgo1WQ4DCV0I0Rv51K'
    '9O8Jl9VYgxw2AsaQMvEcvy4zccNGUXkW8TDlnhD6wQ0JohQSVSuTyZeOZdMpT5AEI9oC7yWTaCLcmfsaiAAg+GRjZ4U5Tu25lAFa'
    'JsMwAQ7dCGnAfRulEWd7PBDGVtwhZzAKFOaCvZn8jrIVwyJPOMRMzE3PZPHBCgtwXdmwwxJlRaOtpBoJLtHfs1DmbpQIBiG8OYeI'
    'lCA1ucZGZcwGP26CMSRS3emS4+rOZC0ReeKVOA0V0eYG4woJwRIu+dqbxO2ItL+JrqtQMCLnKqFSk6ALnKtg4gFSjQlik/AttuRi'
    'GPH4k0hCtDCCQGbRKIeC1+JvnMHDzZMsX6G0WWpOwNwpm5xq9HgJGl+ZxNooQUJBTEgaJ7SQG+rHi+HjROdxQu+wsZrGj2CCAis5'
    'rlFs5DgYX1jMGBNkIGb0Z3xPBxgo0aNw6sZDgYm4DSei8WwkostCl5aEf5G4f4K182URj5kkSExbomU4+VQM5wZM3Mok1CUAHwwa'
    'HoMxIpFfos1nQl0kppxQsTPZCvhWoMQwFFqZhyPFrCUvKDAAPD8SFnesg8bdEnyNme7YsIvcs4Kn63UULRgZpKGyigqaaxxPnLY5'
    'WBNPuSOhDDgBu8jhxGXuIAXwqPn+0xbJvHkW2vjCVVyfKtKODddDSRx+G5UuJ/Itm5Ze8JeVhszRw2XFADkH5gmaLySPWoNwj0J9'
    'Sk22EfuHkFDg0hAoo8SqccKv2siRfC2eB62rU6OTEmPIRZi2C2E2O5JuC4beKY9gwkJKQCaNJpsJSpVnSnCUEFoCyI4KDSGk7a9g'
    'Er7Uvk2hyzGQMBsUrRSAUUkVhh0L0TIk3exAk6XOMlsy85rlWPcESRs8moA940sxtJRWzL+Mo7ykvutsUA9ijYdufMBq6PBYHvUY'
    'UibSzFUNH/y46i3Y4WJAhSkWQU4JAU218HXjUGwiBDwHfHmUw9ueutuVbH1bfCzLrASv0oSX0YQXh4SXYaqRhibu9EyWFAiiUMk3'
    'K7dNNs/hvTvkrTxkrCikWiY9EvtGomSGOQeuzDLe53ldTvKV3WeJZ+HKZMc3sUnPtAllZUYmaKMGS+SjOg17ykORAI+JMATulsDb'
    '33xRMjoJORnl2WuNlJgZQltRPwAYAR2EThEnUXjgzphymQ2S7xMi/Uyo6kQWSG4jJ5cz3ihMFanZ6lNne50mwnfIEilk95lmpxwI'
    'j+sbg2hwO68VDaaJcAZnMv3jKE6qqjVCkD7YCEVOpKGZRFYGiYxxoyk1e8NEWY1RCGrLj8QBSc9GS+ItpBWWFnUDoQnn7XMU5hoQ'
    '3o0BTxzPIi55lorxTJBgwS5UpWsmgFucLwRHLYNBXWT+gboxLYXShyb0LlY6Q2YC7bLszLJ5ZOOIuSLo+YXpoFUvtIiI9UQXgYyd'
    'doHJqQlqnOU6OUw+UiFjoHuSOo8nhluahLyX0VwzU7JMbcz3VLYdKSyh7Elg4r2UhOVS+BPmgoVnNTUSU/paOCbm+pSbt1s0/BBY'
    'gIIMJczGEyMh+9PvlqJolQUhoDUcczSdRmPZXSHUSqx4iXIfkcRoKk1CiYoXChOp/KF6+AI0eayTEGZ5zClPI1lSNFkTRpOFbpbQ'
    'DOSZMhtTGYkplmQaMlxBsTBR4oTDXMg8fZsJMz7RZQjXdHxZ3QbVIvw6FdGGqMtE+ppkqzDhPhGXn4crHgkYn5SzYuuSjMQTjVfK'
    '1OEwyNabveZJWfEmxBIYyVgSrpRvkqms9Fr41CRT8jRaVTwmrcdYGOrCRryv8ZxK6020McvjzpR1K7kTLC+q3CVMMSIAJ1Yukfje'
    'hlpzn9p501Y2lq9CcTeZYyI0iAwfO0pEjOMbIVyc6W/CZPc0F+lpheGzSJeHAl74XOcdZ6Sc3mnOi5d4ObMfzuJc4oMypfyWmtG9'
    'QIntUrj6WDFEti2ei1GWseh5mvAVdlCSMJ9qf8NTWcnRVEPLihTyOo2nkSONWF74dbSqBCtcn3bJ+1lcGn5uEQqvm7CvZlFTRNIZ'
    'XqvhQmpn+Zt4UI7ti64pjOAreqk8f2gD6NGKioVZmQjqv5aNPuQ9fL5gUgGXzEL1xy7mkEwou/opjoM47vLCYIIMdiqy9SIJtatv'
    'mS4Lp8vAkZdcVh46I3oQUXOEkppkRgkTWlZXGYlRNJOtC65wz/g3xTVifioEg0fRSmgeFrYgkeHEJNwozMGEqkkBdbOiTCwrCkr9'
    'pMK1SBslr3aD3yoxm42W1v5M5fBKXTAjmmQkbxLYlT/EQathCZkhpY+JICFLqGdMzpl8LfEtr2LbR6r9gBqML1QpYz0ecxyoUw3r'
    'OXI/Qv9tWMQaY8jeRRrM7hZ4zlifzYlmCyNJa2uyrPhjEkfYMFalgEKMUmscbSVOQFNvcnt8biVeyHSFVtZQM3pBtHKZ2o6wdZM0'
    'huWm4obf28r2XsO+p34l4YiE26W+YPHQwpMXGImpTBPxpRBtyuuQKylMEdlQMGWhD9AI6SP0VPoILFNBJDafCdf0qcyIWlrloZVy'
    'rBhlV4WDe+Fck1Kj7AjTldHwWH2QxVBhupTOWwHGVVPpWrI86xiO/8pqVgVYUv8kps0+r8KyGvknirUvUardtIsQqg/JNM1A082z'
    '9NPqZTRehNRLu6ZkE/9ekeibNI2EVJrWMF2zwiGRS0bsXrZKDTWhmkfluELzkOk39R/vUQirCa0kOdUEGGbJyGxLHUIl6VoZWOJf'
    'iGY0NhKT6PBgzKxJldQIaVW2FVeBV6jzANV/lOZRpGTc3JYU7OD6JIplo5otokT2t0rxTFu7yWrUjBVaVhRR4nioUsxEqzXi7plt'
    'GfpU80R7ipGOpTH61WqN0toQSZfOWi2l1ZJrLDZVP+NSslC23OI9vwi8nEcJClAHKC2XCrKma5RoHtWJnqmqymHWW2qwXVSTLKhH'
    'ipj2JY3GRPBDZr+Wqfvm4q+znvg5HjMH7QXl1Qi6Wq8b+9YJQSt8s4bJtvwfnhLLfTohb2l31v2IiIQ+YdPCBiNvtCr1STw36Yv4'
    '9KjqrKRaMWjkRyK0RtTVk01f6h2xDK4vkN55e4c0X7HKqgoslOEJ5wVTDWLTymhR9UTJBG05paodiRuPBRHeLkg8F6FlnLM2U7hE'
    'NnCNPJpH0r4uGJJDdFUtJOKP6JYKRUCq6Exz0nxEE0tfphiSIcKnS5NbFw1rL7VeHo1VG2GQ2vLStEdcU1FxM8SKKkEjBt4QkTA3'
    'i4v2pYkhbIWV0LWmaWik9mI5Hrv9lXsNhqoXY7Ad8lbx9jpO5voVEmDrtVC2HOnjVBwubMn9gNoBHqzNccFdLbpsOp9NsgXxmX9u'
    'DoOw92w/s/enTw+PToLHe0+evb+OWCsEIse0Kvfegmw8jtJltxe8C278IkizQbbY5stdOe7SYcWyNQPRihGV+8WN4KKqhXVVayqR'
    'rO8X5kCMoDucZOO3PZ2AnwHsv4nSgsSuh9SrPSYs3cqgCMad2RQmdm/ZJLKDlUPLEQ5c6xc31CZvyXN0TLsYe32w1nm036pp3oPV'
    '/qTbKV7jDssAVQ+EoImpHhsxerXcd03u1GCzft+ACtL27Rl1JBn8Y24wEJRbNB21fZDsNes+rx/uNylja8YR4ZAZuckuDg+7Uptf'
    'tTGsk0S/avfbhXhICrocVsi1VMmSaMiJ3c4DKR48PNz900DgF4AUqhUCWKdOXwIT1Q0uN0yqb4Epyw7RebuuMRCUU8Q0M2xpVg+g'
    'Vdo1aWqUfBKO9ieOfRAT36dhGiXuhJB8l6+OaXfGlcPuqyHnGsBf7otJWIYDeY8nd7c+eufUe7H18lWFK7Y7BifslxbMNtAER3qS'
    'hQWhAcZnKAwf8/PVQIbgMHjKyquAFbL0/ZiRlu8yAN3EpQzB+Zc31VQycPrA1jAyfGNbWoHhfm3wHR085xzEKXHand794ZswWUaw'
    'j+k8S/nTRJ1BdCrYEhM1y/Ir1S5Z26p36pvk4bQMrlQfZ11Tna3vXfBQJ7wfPIXGKsevBjHqBye0qo6WaT/YSeLTFNlOCEH7wZfi'
    '/ARGkgkKnEYSD+lCMOit0wIf2Odsw6UGYPAtwjBfUDnk0xxiB4Wd2vagq+tLc2wHL/BZe9V9x2bg2zKDffhFnGwzyesHRfxdtB18'
    '+qs+whvsktgkH4KLnnpED82Atv2xDXfh8eZIMhWwyk1PtwlMIrtuB7d/9aubVClU6Kj/pty9vOhZnJdp7P34UXWe6zWiEZwEyIBu'
    'f9qHz8KM2u78iv91rjWk30c/pSLbw1+5E/HD4a0Qvv1pE8KM2D9Bx7ke2+/bPwFkP9BLMKfq3MWEIJTd7DJUr/fXLqtu76VbvxAZ'
    'cW8ry0xorE8HdpKESIG0PEh4C7fX3fjqmLV5VzKIGxV3udaWPZ0JR9BxrSHlcokUwI5QRJSZ0u7Y+yWIhqa27Kx3Fp7FseEF+e6w'
    'YUln21roopRy7PUJ1WKbptUnA97irxZRNbPqG7C5zj/5ZbXMb91WJLTX/NIJI8M7GuaUfr3PF707apHpDVMv5P1047zGYGgA6waz'
    'prdVKKP3OjFXohprh03Eww77KoO2l6R+/5P04wZ2DdS89SmAwBoPebkCHJwI0z/P2T/a/+LLk2tM/u0rDRvnX8VPNmLaR4hWd4KP'
    'dfywEYjH9TE7u86tX4Y3f/VZ5wrL2SFNv9w8MJIdEHT3sjFdB4u9O8n1HQ3V22tJFdOajbVNw2wqGAu9CkHNvkNcvkWUl3FEr+8u'
    '+hXjeKHwYBERoFKmGluSMP0d458CfGDVujC0wzJ7kGSI6DruDWFj1R3Ra337CzcIo6GRQ8PhLI+mlPPZ0YFmOuRICvTOtdp8OI6B'
    'aEl5X330jjtWXXN88dtw8N3NwZ+85HDY33R6F6x3eGUK8800I4uiqTx6k712mpJ+aIa6uGRGoXIT1AEyI0MWXUVy9YfvyK6uxCUy'
    'qyeqrpXOJO82I7w0cX84h9L51IhI4jOCP3V6/eCPbzo32N639ufw6cn+4ZPj4OnOk72Dn4HeBwZehwteGyrer9XVZMTe0YLIivBN'
    'NBBdHXF64hMF6GcvLppMlTD5TZxv0gKhZjbgJdER19wIj4j/7lKpHorqzcVJXPCdjJaWgvtBZ5pEbzvBNqgrcXlO22FxWdt2VCDM'
    'pvGw6KFsTRfUaPoDuf/16vCJXAYKEXmAD1SCj941cu/rKC8CMWMqXn0gd8U6h48edfS+1PEqHQfMrAZp+CYQ10eB3GStvKB8M517'
    'HeICT8I3EqKXlwKs9LjSdl0LM+4v4slv724VKdU22HrpsO4O4RrJtVncaB3KxHc7oomhJTsaxhO5+i2VYF2iby513gR9oN5gnk3C'
    'BMqDqiHcdO1wDKOeCxc9IwtwL59tuVRtXAHGfjnJTi+deZPXInSFOMUiSpIr1MH5WsrTljdH8cvKn0osbq8GlpudcfS8UbUuOvN9'
    'L4WNzMTUYkYBNbh5bivP30zZqwxY1sq65eFWh9V5+KRjsZw3dPRNIdSDkyh9tl1zK1MIXa13Bpyb++dX2drDgtBtx0BVaeSz/W7t'
    'Vv66XI6qNNJGLpktyYxuXx1rlWDZ0lPiFJZ5VFy9BlPi94H5PxDxMageA6I2e1H7bGkxM5KehUIL2aJNhOsgwvWhVtdrLhW7UEx2'
    'atxkv1NHXoO5rXldVJE+PBcCZnGmC7cMQJa1yEEVip+G9Rhp3D6kRucBG8hjjGJ3Fi8Mh4fELwTobjJbMu1CR3XEB2qF+VD5Pdjl'
    'ixvDuIzmgCrl71pNN45RHRcFrCp2nWk0agFR7yk0GgX5KMceVnyzXOCG6p9l2fxBmH8VF/EoTuJypauwDlsdMVGQJlQ9imQgevU1'
    '5xK9SxGVOtSOozxDjblpIomdpdah1IjX9Qfj08gfOZx3LXjVilM0o/Vz2quznuvYBD0zs5yCC0ukHcRjeJ4qHqOoIcte0xXouPpN'
    'sEu0MtMRCwd+d4+eOKHBuAqTWn2vn6cUU6l5wD3EQKfUlaLbMq7dGSxhfpphjaWu+qh0UJcNBXKa9ka9C3U7t4a3hjeHN+sT0pJV'
    'XTbVEKCFT5WzQO2plvL4VeaPiWnVg1W8beRbJYdRKI+9bjFDa7rWu3Odri1AxtyOLeTA8546n6SXTd2SDLVe6Zmp3ycXsDz1bSjx'
    'e0QAlbMa3WhdcT9ufV21I7biKznh0U5dQixdwmP6QwQy5NApmJJ5r7HyWOypkfQdFQG7hu2obfpGlLVszu9NfHbYqH8aoVkb/KlF'
    'Zd5jTLZuowL4NMqrKTNQ5zN8Oxl1AhXZT7Ziar5YM1kmD40RuS6hE0M7SaMyrUnal8vZH48sVUBbgnroGhXt/b5mrn2u0Gw1LVZe'
    'rUMHrMHV5qgxKcwqONPif26fDK6L+kwQqhoEyxx0e3Ul7FlYPEtRCNzTUp5UKYp7RzxeOf3sQovucLNOSYT20LI93tpMD0VrKUxs'
    'fwPW/AJa9V8Et0RBWd8oa7U5JKvcNMOOio7KOTxK6fInZZOMjnBJxuigHmWw3MqjaYIYYVngOBjDXcuCq8imUwL2lxHOfKTSmvoG'
    'w1DBEHhgvIyVw2/AMlYL1E2QGfQdksnUlS1sX9VCix+zd23DFEqHifnks5tmjm5/1pgC7vHO/mNqKF/Vca5yIewIQ97Xp+zpv/I/'
    'az8uCKhRnkcTYjVG+P7uwvve6vbNaUUkItMxlFl63N434XwjBQjjwZyLDgouawnAnCnAvE4COt///V8H0pjAhC3EWqH9e+qAzNbt'
    '5ippB4WreUmu2RGzViKPmZfK3rgKnAoBcGRVZVrUMykeNFxMe+qg1jk3FRM76APkDTbRj969uVAXQ//lH4gmLy40uIS+Ty6CmF0Y'
    'Tl5hz3ySBdg9glVUdt7/KciTw5M9nIE8/JmcgDzBgezTcHI9bpWPcYnfn1wuDrKbNihKWLwu1AEV7v7y9nq6DNlvOCwJgba4ZW+x'
    'o2fMWlXXwp0FEeR9MtCzNuq5OnA9RtCAJUzkTUCHOGU7HAmrpe4Pd4+PAyanwSSCxWqUjldXkFsbq/4K0LGWgSrM9oNf3WyTX37i'
    'Wbiq0EAg85oP1A42CEeISclO6lwkcbpNmxxSvQ7zaK/WYQVMRRTUNIrTxY7ScU0rm7h6ADaIZUkI1zokdmQWT82pdzzZDh7Kx7Ou'
    'CTqBc3Y9xJ5H23JYHmIMfDsBjvkwwcclbjp0O1E6+OIBcZ/vAly3J0JyezCJT2OYFQv/5yQFF9oGqHJrzXht1jwJV5BACFp5PEbF'
    'uLyPcAzwtWFqFWMABzKyM3wQtKwK4HGYv1Y+rYKe2jzLtnFMDMcolHJPcbGUusvHWGZ2O731OetywyTCHUvGhbgu2cmKv1ufKg1Z'
    'AI1FkOIMDVbY8aR31SG5zUt0PeQn3jJTxhXNnDC6aFyJfc4VkIAQCgUesGUd04ZQnGRig6HfIssDE0kH/oXxmbpU6RijswO27MMK'
    'wJNr8N03Bi79gBd8xDlwIGlNzCuVo1RktNb6WtvvzEDueHmsZozVKrB32CXepNwp99KJrdfokWv05RJwNsDvLO9EXDNeYXUjp7Mn'
    'cEzImnF6DSV8v6vqPhvcbpymUf7lyeMDIP3nk/iN0PK7W+yJm62XtsesXL8jRj5viFscDOZLxOa7MyVIDtiy5tYni7d3qG8wqd6+'
    '/enibXDzztY94g0ER4k5GAY7E0RgiIT6DT+/Qa3d6zSt2tt61mmhSEbIFbW0L4X57FnNFoba7VRujj2/zahrgLOIyrmx249XaoTE'
    'gOKCd7dskQFAtnXvo3dRMf6ynCddq+/uXchgN5bWaNhb96yh0+eqePSy8kqDmL917/t/8X+blQcXg2pU+/kNKba5HiErUs9Dfm4p'
    'VyzCtGWY8IBIw+ThgYpdBPqCLzRUFLNj5YG/stCs66Vrg+r0NinYxE/vOookoO5tbqoa9xWacmgvN0A01Fy5YUHUuZBDbL1jCPSe'
    'meCj/QcPDp8EJzsPguPn++K8+mfAD4sFtZzaED0X9fX+pLoOpgmyWcKvb4c1IXYdmwddyY7QrgbkBYnt00GZLcezjr2LY2sNOrNs'
    'LrpIYyfworPIs8lSduU+4jQtJ3HWeUmrfpwsJ1FRdRJecE1HcCna6szgLBMWjtHjbBLJjSenUnsjKMJNpypj12/Z6oIuLtH0yc3E'
    'QRmOHD0fR8AqN+n4StvdhdX4m6Fddgph2uT87vEDWl1sPHLY3KrHaPCdbkKLR3k2J24u7KIosQii+2Zthse9x6d5qG7p5Tl6mmew'
    'LrSFeVzfiD5nD4LPjmElHmX5Pren6g3eH9y2be1D6YXZW5JEzD33if/Vng3dVLmc1K/l5qtCbQXkDpFTpuDrek9DcKkme5VW5bxw'
    'WftwhCAY4QicH3EoINJMKOnXWFDVb80xz0rlCKmbzfRQGbhIafRuSxYrCVk46RyI7hJA09zNG3GvdJ6IB4Z3FCoCr8DGGO0NlMCm'
    'UqlCT84ucPOQPh//msM1Pz06/Gd7uyfffLV3dLx/+ORi+Mq5J3fR6N9ZyL7DCutHvupQS6ZvszjtIoAHJEqjHcJ9EH+x01JXqzGi'
    'Kq6q31/q81peWCMnwoGKUQLDqF61lKqRExytuK/bbg+CK1Gou35Ld6wSgGOqH9OqD0+jIXTdhEBMUG1+CMJY114Fla6ArWZVXbCB'
    'nvyRX99Ab9aYgBrV6UWZOpaC5eYz1zJtDtfEFnP7Wls8dmGsvzfq0tyhNthzIs65oL3rzDJWgq3+futmVQHC3THskqntl7J9efj9'
    'oSCSi80tParhz1P7WgHHnKQxRqkhUctXXgiOcBjXMF26joVijkA89BQ8M588fDtdj29yc8vW04ZtjSXHbdht9X1rJY/3H+492Dn6'
    '2XhCUL2DJ34Wo432pIUU8XRKm0vQcqkX2Gy5p020mP3hfnSW15fpuvKaW3gk9454koSLglGvaDsQtRmkVNmWx7Qhfks7/apWKZOd'
    '1lQMVau08r7/X/+BF9j3f/sfOjY78wDyr5Z97+0CV8EN6FFyV7/bREOIKhD1HHC1jOBNzA52al33jgil6ufxpJw9gJcp/+gDWiq+'
    'L3FXY5CEb7uf4HaeeDMVgZkLY93eunn7U9diKAbDZqv4PPjs9k0E4PjsJsKa/OrmHTdSh22BNuPPcGPItnf7tnljd11dW+EvgpvD'
    'P+713IhC79BoH/VtVxWgHx8Hn9zk9F5w0TisP3aA0D3DX2JnwYiwkobpigOTqg2+P94GQceOTnSxbl/61UApxRvamYHk7U9v9mq8'
    'el0gEl009f6pXERadTuDgUHZsw7Cw71D6xeLt6+cDonjkysurfi7aCAFql1Q3q2FKL+hGztlSXvnssROncfhgNWrNEjqiSpr6cXI'
    '1JcVC986xWjSrlYMMbxtsdTREGg54zrh1ZPwTXyKy1kBQ3w7qEDl7riKA2asl3BOFvaostGPtp3McaSRsmbS18bGBjGPeCbqFPx6'
    'BPxHz/uH1CTiwGlF9KhQNayYBCZhJuRWx9VRtudDLr7WwRwETDP+lEPKuilCWZxUdk0f5Szhp8skafXWYniORZgXUBx11zIf/pT1'
    'VOYiOuYaHqtlRo1MKNNRGRpDDwVaXcvHnXiUZGHZpZZ3xQnp5BiLt7tubffQSbOsvwJm+2u711Ma4bZfwy+jiPA6Uy9S3XmEv8kC'
    'oHZNJXgNVBC/KzB3pzZomRFueNRiZcGIBbauV3N5wwJMi1WGi5C23AXPueJUU6un/cGFRtwE9AfjdatizR1mYP3goqF90zEanI1w'
    'A5I68adOusFcapHmkvcFGsEu5zsiWaPbGzLStYCLbV6uCisxkGkFlEsun0rXd8MFrjTcH3ad0RjshU0JYPlQLuF23atXl4EbE9YE'
    'dwU+aMrcJj0oN5ZWBUBczjTQDQYK8t51erZc4ASJsbt35wr5x3DAl7hlNhV6Ha2amFZFixO20NIhreZ0w/YlNIjWqUuGlKyV0YKx'
    'jQ9nfx2tiJf6lFmpX1bUKhpSl4QI7yB6wEE0LTt8a6sGZNO9AddL+1PL/Oud6bZ6j2CttbHij69d8Zcs8rZU2cZigX+6TuV76eQa'
    'dRPLsb5uxTxlgZtIIRuoPVn4PSHFGrh79L31VoiWOha1pD1pXscX0PcWyaLtogQrQHDSzec0lsfy+RZpdSMfMhqIG5hioLldJsQP'
    'Qesod8QdsKh92fpPw8m2nRuMBmn4ZlDX73hV9FpqqA/ebvn1jLVbp6LckXq/wrm/4y/uvasr+NAo2Nk92f9qL/hqf+85oh0iWPoN'
    '9QPU+xmoMsSEglBKgMhHwywIXnLlpw2X7reJ+h5G9IPKjsP17LepGXFi9gMb4cKXtwFJfzXKwnxyvYYqirBxBGGSFLMoKn/wKEwF'
    'dcLwjaEMxp+G1d85c2jCZ1J7WCOFhjIMghedatxybmehENKC7ai7jRcduLRFBvwOZCR+hiQ6DcerAaJxsVlFn62DSraxqNcFtyS6'
    'tVcvtUzFKs0WJCFyRfpcy1LBpC8Aau1YpbQdzJYjZPVTnOwvxQ7aQMkq0Lsv0nAe9YN48rLGwSOdGTCB9QY633YjziWSuvGhUp51'
    'Pv90JseIHZuwrMyyhEXT+20aDDWt6/TVtK7O/f6ARWGliSbRv2gMhlFoPYwEtZwhNJsxKje7q1SV19FvQzsVWv7QxioE3jQci9hX'
    'baY5/dVoPBmckhs+OhujTMw5syNum4K9qo61dpfOVYwcFhobLzjNafMfaD63RU3qmTqarXktCQLJSc01D5Lu+0fkVRf8Omtg3Xg0'
    '5Gky62xGRVwvo8BO9OUfAshrgJF4iR0ONsf3fYNq9RIU0kkQl0WguEg1zSIzKhxRwRmt+BLMcnEo+oFeUbeV7BBCuxcc2jgGy0u6'
    'B+UNfpLmbW+jg1nKIFc2N/uU5Xr8tTEq2caBv7SZYJRv1D7qjjkNLXx/Kpd4UjFIZndmHraleAJQRhAY17LwYqyhev3As8G0ADP4'
    'AwSsGxhccr3+/bK3u3tP9oInO1/tf7FzcngUPHv6cOdk72fA0bL8dwxvO+qctlu6VrZP8Xk72Np/cjIMdg8fPdrbC46/PHxK8vrD'
    'nd9sYQVs7f0pfTs+OdrbO6HkJ3AytxVE5XhYafWu7txHD9/CM2Am9URNxgm/nmE114O0Q1fytuRg71SAig059Gn3xm+71OVz6to5'
    '/X59Aw/0/9c36K334uvh18XLG7Ffz55aq1cV3nffXtx66Xci2LaKRuMReR619OTF4Ps//+vv//xvXn5d/KJLQDtnCJ0/3Hn+5Pzh'
    's+Nfnz8+PHqy/+SL851HJ3tHTw4Pn5zvfbXHKbuHT072nzw7fHZ8fkDockRZH+89OTkO5O3Rwc7xlw92dn/do6o/8saDvhxOHzLB'
    'q/p1v3reNBx2lioOm2BUr2FnAgLdDZ5r9hU9i4JJWMxUIZ6KMSsN2xAcgWjPfMFP5cqNZ8eflXOdL52dX9yIifmCyxvvyoAd15qK'
    'XWB/ffbi6zNU9dGNelX2mE562Q+EabW19xkDayd0Yi3EkDkIR1EiOnWiTuly7soO18Z2Kn8Ms9e7wSvP/rVIB/SJ7V6X84uhWrm+'
    'cjzTh5PTyChxJkMZjLmYXK9KMpuHwUfvvFIVCL++ceO0z+By4ztcuFbGXsle1TNzp9kdm8xSc2ChWPTWquTsBCJ9pVnoXTTHjXmq'
    'hl3hesuojeVwrZ0Kj2z1tuPsfmcu1+FxkWME9sKgTKMBcCGB/g4k99a9eibcSrilE4mpvqCnsDJcdke4qZ0rVczTW2sAvhTnURt8'
    'UMHtLc3gw8IBfPOe4rFi9bWuE/BSYPHnkusEP8Qrf91z/rt1tw3M4G1nJA4sbg5wGl8dMFcFTKfk4oXIFJLp7pVdSAt/husp2ipc'
    '01k/TVxb/bbET9/3NRcctHkrvvM7ie8NlbFsyfx5naNrTz6RhWZWqcdhYFXf+QluTqgozcanhMr+HQrDfXKPgTpyesbhE0QzLIky'
    '4qoFYof300n01hz3cqJ/0p9nbMvSMdaDa7Kx8jzBTgEriC8yERywr370Lg4+Dm5d4MAfcPWCIYhj74tXTpfUXkB318YVkbUbE7dS'
    '1XMlPyL4RwzAE7hH4K2d8xRwm1R5cWTXWcFoOSJxnAgCRgaGQA8xrHYdMUSivF/VyhHEgllYsIAFx6ZZyvXf3VqvnN6iukOYwSKQ'
    'BWIF4hroUCul/bXMFtDchKdsUGsuUcklsakr2cVFYKMbBhrArS/jYyeMOsCZoClO+Ug8jNOqOqcuXDyN4aOXltyTwxPbLwsKkRBx'
    'oyDLTWeNzQTEw410sqZatEOSw2MUbzfuNBJ+5Sze3nPSAdAuif3KNqDZLpyZBzYl2+YkQyYeg7kh+ngW59iNhtjQVuIw9S6Nokk0'
    '8YZbtxXXiwNrrMTNKNVSHGoLR8mjGLHxJEP9P7d7XeBPTMOoQJYkuM/DFcBNNIIVwlEyM+6PEaOy2+mKh4NiQBO8HEe4lwss2w7k'
    'vdfpCZ9PaHA/YHcVbDNXzLOMrW/YDwUlyIW2jnUDXXXEu/rH/htK2O42Rk31/xLHrObg7eIK94KojelRNM2jYmY0Lk+jnOlFOo5q'
    'W+j6TZ4vRQqdtBdnPuT3+8MYW3JKmB/xTQQZkxvYwAwCVK25x//ELENyJUKvMh8TsbvBTp6HqyEuBHQZlm2bue4uvVpxCIzsRZAx'
    'e4zoa4Ab8M2+tO9Ed+9qX6sRoSZs/XUGq40HEUbTNg/39W8Pp12pgoh+XZRet29z47i0UdtjOO3q25l05wr7mXf8/Dhky0xuq+E8'
    'TjheZ8KdQleF0ixLNsfLssyF5LzCrtpgZPo6FzK8qo9GoHoel7OuVj+N88KgN69Vq5l6xqPRm6sLvcAdW7vYxsJsu8R9ZVch4Jvk'
    'Yq8UXesq5PJbvXVWpNPKMZsBNa6NF/CR1r3ZDz7RY2yvMi3GMQetL7xX7o1hc/sXl39v3aY/eLj9q8Vb95rwzeFnlOBeJeaLxtQk'
    'VuBgxh5/tm8NP72D/Q0+grZnMWIx3+F8NhHhWXG0dodjoA9Ybb2dZtAz39kSL/rQwKa8zEhexh5pX/VSKtxb6U2fDhbqGvDeCz5h'
    'Ya1lqLc3DnXNQLfufew4JfOaGgSfXAQIYa09ZNHP4qUimppsgIOS4L2W1RMW7wMXibOUiRx7jiAaESZFBt9L2IQqFtKp/AY4SsHr'
    'IiB+J8D5JBEOE3DaNOnU23cVwX3jueJnouINHh0ePd45Ue/4P4dLsFF57CmhoN6oO5T1tVR3ocV6H87WXV/rQZPINzyHqp9CUNma'
    'SsILBnAtZ/Q/Y1/0Lnh0hdZHAydx/upxQfG+z0FODo9+8+Bw5+g9OktyLNcZTxDMvAyFq+/gRkcesksYIqTFdvAJPYQLjbciQWim'
    'eTiPdrMlIuz8EtItS1IIx/KyX0WgofG9eBdPjG7ZaUaqrurVGovtFy8vXppDrugBKsWlX6jlP7hwfXDShl6dNTICEJNf/IiIlu1R'
    'J9XZm744bPKPUnz1eD/nYGp9jrv0luUz6+Xn7bakgo3tq4QDRnm7jafHJ8cX0PamQGyvjo3yxVR/8cqEoLtYC91ZVjrAdRzvHB/I'
    '4qxCjaIR+xFclyksIpDjiqcNvn6ROq2bh6+d8+VHwJcuY82+QPCdc6ohgJyHp3BRFAoCWWzb5qsFSbgioVY/fWCF0QOFtJNM/bFI'
    'GNSPRDxQPZJlwUdm0jfP4tJoTdchr+Oxn9ps5nQA42aEcIP86y+ic1fuD2UkjAnmoIsveDBS3LWK0EYtSSWxmZoqUHnVVWIxVBdo'
    'r5b3Om2h+PVb2p+8vUIztMhqbXA5pwF7QCZ19AXG/UDVwwz4+gU2b6pEZEK+/mXz6eoUKNGuDrj544YIKq/VT2NN+pWZN9KvlPak'
    '30lEhCphIz4ZLLHJ0qEhbIokgiu/TqJi/NL4sXqQZUkUpoZVhxPCjntw+Aq9t3Ivseu4UKgvfHTy0TvTMrHx6sNQEi70cOWVlcDr'
    'twD9BcUrpDuSzUB3Cl7zfaNAcBaZ6Cb5uofsSetXhdbohtvIRa/OX+4PZU+6P3xRNfnS4p4u70pU5ISasl2x2UErhxRsoARXWITe'
    'ymgQhDWIdgmJMBTCnsygMlpeZqXROLr1VUnT20gCsRd9i/Z6219oTgZaiD3Cf7d55/4S++214zjJ9OpY1/GqVn0WFLkcnaiRdmwy'
    '9PFnhE0GIPrQRKSfarp9vORq718NPe0mWcOKy8g5IcV6UgwtgWOPYY8Je63LzMW1H442dd6mFkadlfGWt5FaGh4G7Zdu5b2k2hao'
    'w6+Vqa2uTVpUBZH3eo1NpPJXBxHm2Kvqefwd+l8Yu8YHFgXrMmJrOYOxPxW+X4m/YWyXZnCH1Tv7bYnjDu91JNEhYHvJbuwEQ/0j'
    'Jg2WDPjh1Couh51em4e7dROhQ/F06BJOC2Z5x5GSC13BzLzr2r7XQovrO6gDoSWiKWjV0gZvx9g9fwDvd+nBwQgiyOuBHCBUhweN'
    'c3CdBIxLCcC9hgkxC3sOp8lDFOpzL7jKnnD3sj3hrrcnOA6WHYsQVr5bE4CRDm0Rj19bD36fi8NWEbk4+tgoe7vF3pItJOiP2Ioa'
    'mxi3Y72LLeJVqqm6H3R1rmZh4efEgZcGOOuI1hB/TcoFjnY5EsfdLVXj+KtCpEYEUgJwu71qDEWZZ+npPSOuWbDAIEU+feB4C7xX'
    'H4hxf+j5BCzmYZJQVjubFzwBTgJPwS0MSk7w2P6FS30gXgUZ/GKkc1EpcR011ebxXXbvhbH1stCB9fAOSVJrtejqBFwag+aPmitE'
    'PNK+qGGPq7tSf8D32HQO3mur4Hv6dMdX3V0Gk5ZDx81F6s6Jayd4P9GAXcLOdfAQpUGz/i0sPEj0Gs7RZdlehVSZoQ7GGGt1LMM1'
    '9KSiekwLwmDtIK24KWs3uJPSiwuzL5lMNWOu11G0qAD+IAnT1wrizfv2D0Plengrb7OrusExuIMROjNsXO5cLJJVDUXQQV/7dY2d'
    'vHWctc26ec5swLk/KZyN8kfi4bahnb0ekxzek2pY1nKY3PO8FgHCwuoXZnM3W7fi7frdmx3pOUNjmt/c43uVAyCnNXOghDqoM9M4'
    'n3dfHXEOHAu3ZL1wDWq4mfZ8TcoMXTfzQLRMYqY/gub3g510FYR5CXde0HyXs6yIVL0anMVJIsdRo0gdrU6GrxxfC0aVqwC7DH4f'
    'NgEIC4irwe/3oRVzmzYU28ggNabmGpoox07B1Tz5zhOcao+1o/9UzJLbAeFVjlmyK9axsJevA2fYrQyvSI5eyzn0vHcdCBjkve9C'
    'BZHiiYC+NJzdtJooA6F3rq2XqiC8YQknBoDAObA3C5b+gXY20ZcmeRPyYuV6kneVYLXJTpoqlJ0U0Sr37tTsvyS4mHaKVkibLtvr'
    'qQpEph6poVW5VM/iagzug8Q7OgOLvtyRng+cxbKYdaUWz77qorYV1LrYUknb6G4KrvwT7ak/D/nf879acSlAYIh9ypk0P7RQe5VI'
    'jdxrOz981fB1D2C04pav7vp5qLmqozpxz3bZcUqTp9SysjagazZCk/eBhSfonV9Jdz96V3VPzsHcQ8Dazs1NXYjD3HIWFw78W7Zb'
    '+v7/U/cuy20kWaLgXl8RyVQXECkAJKhHZoFJyShKKqpbLxOpUudVsaUAECSiBCJQCPCBYtKsF9d6M2ZjMz13bi/vbmwWsx6zGZvd'
    '/En9wNxPmPNy9+PxAkgpK6uyq0VEhL/9+PHzPtzH0svWv2s72ZRsgbREsvtVz97fjFSsRnuWPUtnJKEtCmPlfmGVoQJVY1TAQPww'
    'h/KNWT89a3Wr88v3Za3b21YQTLcTLeulAfyeNI9qbfr1ij3E6CXrud0GGj2uQaRagYJt55i/iS8BLCwD2aKTQGFoghjfZCnsBbjC'
    'CpiruEI+T3ecHRHaBsjN4aaLzUuRsA4Eq0WWvyQKy4kj9XppBKbPbF7cWiZA5BbexLM30bHFjRiCnPM8buKp4XfKKIKPDdzMwwwI'
    'ixjNne8BxnrgEIUYV0qjFK7yaJymM4UzgnW/c3sNlblm1xx6/vSYb2qTsqYWg1TYm/uXRKUTN9zvVIYNJuhnmw4Piunc9KxHd+BU'
    '0Xkrdt/evKXM2o1RurUclzbyUdxkLG2+ddtkn16ZlbDQhopzUdYMYPUHGzZToUQ5l3swGo/3MSoJmV2hdQ4umJjVMNAZSwTUPRM+'
    'MFVYqE91MNxXL+i2yPfCGjOQCNRV9pEwCdJdiGoRpP1C5jTOUD0nulrVqqZRykBy47QoNriXtXNItI8XpUjKQSgZ6jNR7Rvvo7Ub'
    'p4nxvLuEYKmwtnGsIrerHQAuPeagxkuMxLgWzdo5OT8OMhXy3efQZGi5uZDx8Omp/GHUIPmz9nx3WhOME4N3sv1MzlWV2sC0X6/I'
    'jrjolapyLdAROsXU8gu2w4G7YQbLS7Y4Hw6NC4h1YuHJ0R0sK2CYEw75RdeLLI2QIhIDybTLJIp16Vf8akr2/kQkOt/f7Ls/ND/8'
    'S3j43R/YpzzvOG32lWqTpId777iJuDwmWAgIvpIiNCP6XDcd27gsGSnj3RwFLI3VlYDZHFBym40fmfwqzj/XqiyCtUXvbloXG8sA'
    'ygnmDfGv60l8vmvQECXy8JLb3iBRhm/GZRHYnDN6kHPQ3CbxsG4Wb3Rql0F6Mo0mAmPxNMnSYdxzGT9GcA88obR2+F0esXQX07ak'
    '82gMj5k8D2Y8QXjc+L63sUExKWcZWarhux/4HZrBYw1+5HBJtAt09WBiFhpgLE/UxM4T7+HNKJ2oYZoTxzSmPoM7w+EszjJ+eTpJ'
    '5o+jTIrA6ftMR9u0MkqzaQIzcq2YN14r5qUbQwD89+wYM0kSoh/MXZvnMRAfZibZ6WSWmO7hAVAn/z5GH0voGK3t5Wt0FM8X7oUz'
    'vHtuzEcZwvj3AFhn+QV7IAjiqkgs7vq3YJMvvsCEyb00KeNgwk/Swct4cqrlivEFXNuoOd7O3cAYDrgGbLkXbqh4DUsIWr6K2QFV'
    'rmPTnxbP2EyLkfsOBOA/7r9+1SF82qSfGYWyTo4WTVMoJDuJwgm8JUi0UqCiQqCd05hrdG6GHMwvc1nWz0KZ+riAS4aRl+143Zme'
    'yCGiiRwZceqtwCWUbJl7vYEYDg9pQslYVAaYcuXy7Usq+Sho4F/W7lIECBYGiJaZtcjJ8GpNFM63L/EvPNIQtIqZx0Q3IYaSUMrU'
    'YqrC8jU0jA7F7K5e0AwXso3FdNRxyha8nYdTonQUKcWBbfOF8LUOPQHYlugtndOEUiYgGkU6AF3DXwimyloGWXAZQgBYgGlM0WOg'
    'UAVrU5ZbbmAXTT6wCh59GlPWOKwHaZ56dtqnMeK17WkKeeQfaJbtoLtSY4CzjxFHFhr7tI/N3L7E1kjveO/TKu31IwzuJCG5zmyE'
    'JuRcafGN5I/9rwjuTNC3VZrH6PWFodqW76ExQ353BVdCn/vA3gUIewF959QX5C6o35KNwyvsxwahc0M3NAYFx/aSOOrgDTBYdNVo'
    'H8+SoTV6uH2ZO9Awp6M272RLg5q8onRX9Lslh5vyQ1zVNidkgd+gfUlNytOShoSkgIae8i9gvPEelkbk85JGUNkPLezLuZmbWVny'
    'pNWgt0ubWahWFmKG67e1aNlALvWNEfGDTWbQ5gE+uHOdmVU3BNKqjeIRprCm0ObvmChwx9qsu1BZsJvJydI5E8FEERyhyWf4EPAD'
    'tWXJs9UaQ8oNdxIu1BNKp8YvqCn8uVorhtiDlp7Yn9SG+bKkAUMfWui0m2i+rLQo0RAa6MKC7GSYNCMCHJAbj1CbK7bWniJFaNp8'
    'EsijboloRjyGY7NIKgWpYm0sotj86ojCUMbmJOBN4t7RYDU5vWTuEVPG0Ji5xwL7ymtLSOglzSFmANSf4Sq+g98B/6aWDPW+DDiY'
    'rEfY4F+AcOazaJJRBh7MMz9jdGZGKBWWNGuofmj3VRxhDqNg814bk4MH7hO1p9mIFRtVy7gnr3LLmONEVm3XQKRtVcOkx8h4QFmJ'
    'zA2f498L9jULvwYWuefYIrl/liEZpoKgi/dCD8EGxidTQIaYCsKgG/62pC3huBDWzS9G9vy0Gr5iTo3boB+mCXjIt+ATx0gSrz00'
    'iJycqX/EJcBQLUQTY/P0ei2YpedQ466OQEb9aN7QkMU/rptWLH1c0/8+kZLAMM5PJ+iZs//sn5nEnMaDBMalz0RxeEyIVo9PcarL'
    'hrcE190Ni4YnxoylQu7qWZQ46ztjy8EDFK4ZR/fh0IQozaNTXzqY86iXkLC9o3F8sXUcTXvfTy+2TqLZcTIBBmI+T0966F7v7FL9'
    'nNbzdEq5rIX34Y9rLqBRnQUYYPa88Zc2stx+mBhzwm0i69YeHkCbAYBxPmX2rzMoZiDXHu6OAWsWh8UgQWvNAKcaXis1YOZPD8XY'
    'N2eN/SWWzwVOtGjsbEBsBQvnq2vYKJcbJ4vo2donO8Nk+qxkpMZGDqVA5ZbIzgj5SgVv8OLEnR4fw6WGOCAfKc4IwTNgUGcxMKKn'
    'GPZ4ojwLOiaOnDvZ1z3J1vrLbKV3dp2k2Ft136wqFXa70+kYBGCM1sbR/KWGk/wShuGhF2ZOZEbEWjM6weqMT3CVBZew2aVIvD6Q'
    'yAtH0SLp16EZnqu1zYNkt2YpmXdrDoQt0b7NAZeNnIgUyNX5KYoG99+jKBPA+3TKX9CwwfwekDDW5xrghO+j3DFH/0vfsHZNPXvk'
    'n1n8jlO+vArF4MlbeWz7gNU8TdvZkiWiX2QHQL9wpPyLKJRD404JF0pogPcPLsB0OTEs2FpFOelWRDnxcff3hLtps5MsmKbT0zFx'
    'N2LIErurRRxpBKyCneEfTwkBQu/J8BSZNRS/BHDm0nM5FAYNqAHaODEYBAx6/nGO+WsVLU/Pa6Z4fgLhFgpHjikBo7zOTmdH0SAO'
    '3RUEPc7x3ELjM/j/0cNv4VYe0a9dA/b2jUT6Um/2Cb5cAQIw+7i3/vKda46Qujy8JmcDflzHntd5FGpUuHmAxeyp4NOAe99yh+ET'
    'DJt9UbCI03AnrNyGvobQBgMRR5SCnoby2uBRC20hf73lQi5gQbkHWJGexGO4f+iElVwF1FLErCnKJKWrkhb4YFY1wV9tG8sHxCfb'
    'XNIUoraiaS65bHiMHVZpj0teY6gI+qs0jOWWDZNw1CqNUUHXGoKcf9kxuJlDuE4n62HxZJbx0eb8CbIAgqmH4ZTwwJZQ2btW+toj'
    'BzxMSUD68ygL3qIO9OeAopH+zDJCirL7c0C8lzoceeobMamhvb9fC0j5yiHCtteMsAKFqtDOPD2eRdPRAlrdATo12D9JMDVrQKo4'
    '+tvdvBvcu//g+x9+q6l4g71L6XZNsvtKhXSMODEngUdZryeFX0mcDluLLjNkiVWb7IVg4FEhkCwpg0tk8UbU+rr/R4wDCpuVHE/o'
    'hmqZBKmkKYVmtRA1dFpR+8WIPkOnJLXfjIgzbCl9qf3KgklPnbrQX6lNp0l1Y3HyxVCpVt2IrKgw1GpW+10J/qR30rva7yS6g6pW'
    '9erGZIRgoVLF2q9W+BY61Wyu02ioPrKatFBCRBOhZzhduYmbdZvoaX9tR1amFRa1wbaQEbKESjlsPzphVOi0xW4dRM4UliiPbSEr'
    'GgqLyuRCIT0aX8lcLCqrJ/rSvPrZgaYV2IRWvaRAQCQtoVNN229GchJaTbX+hGIQ6dzTXdsyJNSgykqR7Vpg5daKm3839JmB1d34'
    'SvhU5TlV5jRFGGb5kO4VEkeVRPXKkS/aORIQunbg8MKEWsLowx0oZm2s8I2zEiefEPha1S3do1XumNDPB99HjIsbv0VeBWPLY40A'
    'rzx+ZkZRGj10hPq66TiZN9f/MHv0h8k6r7AxIiMLMP7e+LnB3+AQ0aDwr/QXWlYQX2bma9bJ0pPYOYsbfsW0kjELRZxSj1582Dj8'
    '+Wfkgig3Bb/qyitijPjVpryiEyXv7tI7w+ZclWvTGSZQwWdvvOorcWUFc/1dxkFGnEaPjHF9VZh7Ze6MsCJeAHI205y6sGWVWNAS'
    'CgmP81oo9LPMxQuoP71kn+Vz85VhDBiSyyIZlKq/rzOWH+nQlursgzuwtFuVthtemFI07bVFngECqjDx8Ft5DAzbilBSOYGHpDUu'
    'n0C7fgK5rFtVU7gu3baqhNZtfmbwmwUFwsFDK5MRK6KcoEa5GKIjWz5yRNWyid2RJ4tKJGJ/lQETodhSK6aK1p0FKzf9kMLdljT/'
    'gW8BWYGCqIyWBbsKPsG1dfvyCcdfPaeMRvtkztS8+yBkB5ygdPxkK4nt2MxZuVLGNNrsQjK8QYrNijRp5UZNJTZRzuPLvsonQbMf'
    'VEpe/Aqc2Od3E0pkn/cbaxBXRUMlAB8W/ME56KU2/4rZ2EhFFZNnE1bsiURaRplGw0PhsYgFqZVPty+p4tVBdxN4LfjfJ22e+YoE'
    'FJ0kexW9alKc72O2jceAZo/ECIsEcjFl0oE1RwfKWDbd+hABvQs0XPwZEF+vMU5RxxnQ7wls3ywZoPAPCMCR/biIo5n7WkiuXNgX'
    'df6jJXkH8olBay64VSwEK+BUZb7D8ZibregYl3J4zIputQjy049c1skTZBwk4JffMCQ5H48aRvbX6KFQPyd+oDszvAo4gLP5VAZp'
    'LP4xl3SIzDYPRMsrcqj1bUpJZZsafyqpqtJ6kIxv+NDXLhTkYfJRcjFVFlCKh4oSxoS9poiYTNeUUAoMnn8LZb1XpYIc5QIJh91b'
    'lypxvFqUa4oJS76K6K/qsxHrVX03srmq70bWVvWdRWZVX0UGtmzhgIDzF65CSK8W7horNCFrh5tNgEjvmgng4a+1fZH8myoukNCR'
    'NhHB9pq7H9ZUvCFOD+JwIJKYwgQ6+R8mD8WM9b3NzQ2S/92+FISDujnqapmS1apVy6ywGyINByTUCNcePgXCYlXlrW13CnfFXOHy'
    'tYdv8E2wHrx58uzarZWNEpp8FZ+v2pQvO8UwLazt0MqMIe7BLNzSWmdy/3XzyC3NE/pcqkIGxi0ZeFqUaXQcr1VIeRHHrT3MgxFi'
    'c3g76uaNHATP/7gOn7BS/ru1hZThikjQhfT0SlujR5s9jWZQI5Qm2broiX/39NXTtzsvgt23T98HuzsvXlj9MGuT80MzXKDSNy/t'
    '7ySeR74xWWkRGFL/obPKhH15WH8L+qxqaLTRK/ex8LvwDDdDiWrkb5wRrK7clbORLOnLyllXbs63lSxpEl/nWvMeBKI8M6BHBQwI'
    'JONsXms75Gn+G1fl+45b3t7Um24SdLky5DdaODv01pwgz2aYRJKZMvTIV0INDRxt6wKUm4QzCv3D5I31DMoVcoaff5iw+WWhiDXm'
    'rPjwxtxCfDhk4l+6FO+VTT/A7xjJpqVrkQcRY+v2h8m+cSHKHwJ+D5MDdLMvrkXFMlk8/+oztIafbNhNJpvwW+Tj152rb3v6h0nF'
    'Z2sH+YeJtRMtTNhZjALkGG+vPOAY68+vvCpPrU0k7vxETEaN/H7pqtjqhQHnhf0li+RboJZcQJ52oaYBu8oVi1OGqLQ9YCWe2t95'
    '9vTgJ4CS/TdPd5/DZfb81f7B23e7mAZlvwi4rskKLFZuQPEwZwKxP+hYQ4Xn60+dsQPyI/bpyfor9ztmiw+Ys7J3yEoMHKxdg+Pc'
    'UD8ptDSlcYBLenvtwZoaZiElp2E2HSncsDpso7y+3pyvafbx/tnXs/mwS2J5ttIV+aF8RYivm8V/OgX0/xXX40mMIn4UZAD0IUtj'
    'p4GnpXyCdEzq5mdYq9L53SufnzYasqYDAcViWGG+P64LvZt3jCuRq5FY56NJg2Sy+71PZ58pMRULczL2WVrVFZKFPgVHSJNV8gZi'
    'xbLoEpjMTzf5kcWD/ylNTx5Hs99brzCWvpd7uqp0HN+UCYd8XYRXFWXj+4NRPDwdx00vUrILKnNV0bYVYdXIYMuExBuHIpUtSk3L'
    'ZaZV8/YHz4E6Y7frL4EBaTam2hWc7Ie3JIK2I+H2TvuYXJFbKsbilA8GgxEx1ULd0iQY5H3iMjapi5ynlEhpHfjm+PFk6Ok8CksI'
    'a1W2Ur6gOFAd5BnMZKjhQ0JaNZjPZIXTwAoOHgUH/GKCMuE+xpQcAmboNLxYVSW7WikO5eiwOYHoN6zm2KqV35fDTj6QXb043dOZ'
    '5MG2ZFW1tuJGOMJ4KeszHSxJ0XpVlPtf5cO42VFmCPVqlnZrq09+aRRS3HLlDFKodKWgoq5cWTxSGx0NDh+atDz6tAL4fDjcqgGG'
    'VaICrqTJmaBVyc3vgLL9rdnd/DGtg9arfPDnsmJeGB6Ow77akuSiKNNjyG0Uoyj/EmDxaWspoIZfRVF35cUzKoQjMfdbdTwFf4Ch'
    'j12zfJOsrrmshGs25Eky+kulH9EnVIwx94/leiYgUq0685F7ASjwyxGkmldeuurHaiBzdD8FLhnhUC2MxIkOaDkiS6AU9denGEtA'
    'QoHlGuUDVdMuLP85UJLpuRTNZW2PjuCCoeJo9MKd4Y7hCKReMdV7RSUpTx/qA9EdRH3vLAIZty88dP2BVNnMLRSbg+EaCVWDFcpo'
    'zn5uItzlM9FOYhXlLW/ggYkSgbzJxQ9lhSh6ykWcEz51eU2T4xGJdbIgOTnBXODzeLyoiSYHPTzBTOHUBXASZ4tCgDmKVj0OaCeC'
    'aQQrThThn07jbL4zQYEizJ3j/THgFCLU5VPVlQ1mKWPg5u/pJm+Wld5lpA+liZtyD2Vgsgr7UNsmXUpZeYMqUt112hygo8e1W6wA'
    'QNFxufAi/SWHSSq4xZ/3Q6hVPDHo1dhYzl75BkSl4Q0JoOazhTLMHctHxI/PgcCFoR2pDQQMk7tfjE2kyZTpjjEqKfuepxQHvbL/'
    'YRpUFz2NzP7cJ/I1sh+9VJ59HV3SleGsnrYBysTpPtpMn/zRJOh0BVwMSuxBh6SE+2fDFZSMnqYbnTwnN9nAZWaEajaqdi5qnJfQ'
    '8UjF4/YiKKmwcSaV41E+Pn2htGR45GF3/FxbumA6m46iSczR6bFh70VZDQB6BIFpABQonJhZEo2TjAQ6H5OTYw5pS5QzBQ4PUjIG'
    'z1QDJk3lkYQWB/rB/GQr1MJakrObN4jAtNsLmuOO/NYq8lSMTKFi2qKR9QJrnoPmoqqxq9Ak5rqlXt2yv0zHuRSu+aip2t8OyUug'
    'pZsx8cQAbSkc5PNoNvFSYuDpDOLZLJ31MDRZwfxvnEZDHTQ2Pak6v+JXGaGhr3eWj8vPsg78jwnvS8L+i3GQIi+xoKo3FEj9pkgZ'
    'Ch7IBbK3+MEYtfGT/ZiPQUtl/JeYrk9VNWTio0ccFs2NThXKyY2+GqljuroWucNcckUwWjpcz4+CSGL/AufJ0yfNRCmZkxnshZQO'
    '3EWTFjTdlqDVyVy79t6MFtDUgL4WJbBp5mgBylqaT9xmF71I9qhwjCudFjwNdaelsKSKrl0hsRhP3OUUIxjHRw3EhURjvKs18ao9'
    'i1ZxGzCjYKmbDAQ4huTMrjmZ4uBiv+Iow26E+AmzhjdN1G6Obp0/PsCxCvBIHi/VMIPmIMvEFbjhRU0AfH48oW6yHkcc3kLfWbjx'
    '2wNmrntEdLb78fw8jidbMBrZ5MYUCDrU3d2bXgQYZ6GfzmBP2rNomJxm+HYLwDWDHZymCbWsPIDRYU81VXAG3gwpoMODQkAHqqim'
    '59kf6axi1u0YptnrblnnXo5MtkW92JfxeJxMsyTbOh9Bq22acm+SohHA1pp/FRmTGBagHKS0B83bl2aHrsK1h//9v/2P/0dgXiGF'
    'k09mJtY5FTEe4jOKbjpPp29m6TQ6JgIIzlBNl+wmsL32Gjg+hTj8sQdmTZSjMoqWZOf4t96KCG3zwpptZLsr7NQa/3xyiKQWaB22'
    'UGDqBoaQqgbRztKjedjYKlah8brS5IntYV86xtEUxjjcHSVjtnS1qUE8AtpbXy+/ZH3U9JUDlN8oNrkeIkBvXMov/nI8YJn08EvY'
    'wHoeaw/DVv7VeCwRrOaiAesNqw//idOF+2J6rbR/8MH1YNj7Zk2Y1xIxDrXoNfkyncWcgmKVRGrEsPUrz+ay7GlGjEu04nMY/RTo'
    '1Slca3vAIZ9Ek4XJ2DVPcWyP0Ij4AepjgKajhADoN9TEWOcJtLKxBX9+5Ebh5507LrraKvlBylKLOFeLv3JCg5PoAkNQ0+9BnIzL'
    'RldIcoDhPL8ox4nS/N0JkGDgDcLfshGwC/GwEIKWaJICuMMx3EU4lCAbAN8BwfdNT0I+Ci538fgUkDF1wTDKjJ0PuIRoncvNVmVY'
    'bnJXnFcF5DZMAFFXTaz7COuKsx6Ga1HcEq3at0R1FWSVd2Sf/LPlAn2bLB+3jKSDf3lijaxErsEyjUxLM5wkI8vLMTwZhogsjLhC'
    'ueBeBjxqauGIkxEhVFy1guZHHeKm7FDxV4nD7FG9dA4V6K2QT+SvL2m+zs1bcXnXZwspTXvJ52nYcYOuTEFu+NRCPo6l+a5t0g0v'
    'SXz/NaDfz/ECmKWxxv9ITaEiIx67zJP9dDrfqs0t+4ndlakkOuNQK5S8xDE9fINU0wm0BtBtjTRZx5lQA4QXZv1gRoyG1ZFphLkz'
    'xA7PhSp4lrgsI3p3W0HpsFhczphUiazvEo0PSyzirFGoxgePK6lDVugNNgyQXgnGBbbeiKoketfJ6XietEVsxGBeYH3z18BrYGVm'
    'QDt9JWrwG0MO6sRBO3mHjwbHUPaxoTccyqf5VUiPL0L9jOi3VZ4rki6V3ATvXh08P3jx9Emwv/v2+ZsDd129kfhTQpwC4A0MYRrg'
    '/zfH0G8WwEHOLAlLuX1IXJqT5YRuZNLENQhaIcH4EshhXbFSIpqX6xhaSh7LGeZljic5onjt4f/3//wPwav4PKDur+3HkiNXuTn0'
    'fec3127PTzwGqHqUzhnBW8Z4N4V5D+aKLuV0rMnERA8jHhh59//yHwGi3YASft7IR0ddJ6wVHKiRvMF7Kp83N8N4RBHGoefyaw//'
    '8l//z8DUXm0QqA5H5768+5G/c//9v/3X/z0gJ6RrTy2+wGC9rrk3T55xi//Lfw6e0rfVvZrg4LfZ6CvXidj8sKmXGvrtSx/ildBD'
    'm4Up2QcM7D/+5yDnmyTiCXMaqrVuV/bcz+azKJnrLcvYau5USGRgfo7iLAPkDDfFZhtum9OTSXAR3G1jQBFoGJBCh1t7YbgJ0wbm'
    '7w7m5ykFk0L9dQyYE9inZHwiWcfgXkXZaxCRJWDQfdD7bWdlxoYm+8iIYgrMzVQmh7zNA0B/91gTIkyOyfB0bO+067E1KzNKJ8mk'
    '6bppY2jFYj1Uz4WhDdrvyj90cfvdiGeryV6paEH4im/pn1lDF/NtSdBKGfnaCRunKFVBWWnn80jJIxwsYeHMr1mHoitEhln/d+lB'
    'iuvUbHcVrpnFZ0l6mlHDa57jpf/JygmNVNHbMbTQQCHzkJV/NpbqX/71/yqcdpJzUrWypjBXKfuD2f27nmxUTVTNE8O9lMzRvV46'
    'Pw/8yuf6f+eRiFBEWrZIGxhq/PE2blPKe5sBTeGRP6eoOoUTP2Z4zpA4gAPfB9YYz3acjYIYiG2h+UI/m6lrCE0DyjKblpSwR6XA'
    'eBAXgeWafjVhOGRGVnAzZcENRnCxawePTnjjzuLqR7H0JDZk8+5UojFPRtMI1CNpQ1z9qcug6UEA1jLnvkSR4qaCue2ug1u4fDmC'
    'GdG3RqGw71JNugwXOJlqSi5B8Wlybjn0ojNP3wFEznaBl2qGYf54lbU3OT1ZM2d2WndGP6mtyoM9j95bMfRbXG2tsKS3Sp9gbFQd'
    '77K2PbXwcFU1CCwe1p5MG6dWpy2mrHHT4Dv/8mohsKC4J/8hLOTkPUpCHTWMpqJ7xtPMUpWnY1On0B/0dZS0LBEf+jnMfXbfoUCg'
    'oKwh5y8o7v01qAykD7rXFaRqaR/g/mvQG80KggP2hRfZyaFsw2WopJge26d9TO1lAt064dPq7LzJL3uQNi8DjJQabFQmlNUgVgay'
    'yfCiFXhKMV5oVJKucsixXAERUtsN+9kGvnMJgdHp4uLLcq2T/ZSov7206gK3NTnX2UvTf48/rz4JCEvuac+S6pGJ1YJtv5tw/lxu'
    'qaS0KcxhB2x0d67lGXgCPyqzyLws2y+Q2mnaQWLc8EA/Zfm1eO3i8uiZ+VH7aYLFuDw1YfjzQcEk67ayXoN71gbuEbqqGIDf94x1'
    'a66D88DgyqKpRGdRQgIX4t31/PDZBrOHB0SI3xSBAaVC+Dk36sIrio7kQYXMu6fKPh9elBSEKYa5XXX74U+A94NHu2w7sNfE7AQ/'
    '6E1go8CS9VdNlABVGTDV7gNyzBEGWda3QHR0RDZ76QToYOaYkwk7htItHjyz7C5y8MCJ+1zuwd67l48/vof1uffDxlbu9R683vx+'
    'gxhDQiJF9snLqGDSWgPR0+5Hw2OioGBTiO5RrtM5uYWthwHm2skgzQt9GF3Cx3TWpAavWkK2PC9YaDBnH1NhFR7n7Dg4S+Lzx+nF'
    '9toGsFyb9+B/aygMAGYGddUYwGWWfsbo83yr7KL1g3nL4XC21zbtCwRKIIS318imwnuNm2beK6/6KdyPwXB77WV3M9jcGP12bb30'
    '44PO/eBu53602eludgP+F0fcDe4Gd198H3R/O27fg6cu/rvZud/Gf/7sGgN68uzY+Mx6YWP8rRpEk7Moo6jIlPsSrrM4hpXHQNzw'
    'Gd+3ebHXyG3YcYwAXhKefsNwf5o1xI0qSOECBwimznW22Fb5HC+G6Tksb3LUZGMeeAOHsfGUcrr//LP3MmiEl/xiOqO/T+Kj6HSM'
    '6qnlnV458OG1Kixe4JZxPjo96U8Aw9gFlA+yhHanBZBuX8rJg9UdxehM4d7tUXR3rq8j/lQfOLzR2hKAzB6HHKLniOe5wG3m4tOT'
    'LUTVUdVdRJ3+7GFZM6sPFzEfwFVWG8Nq34ZCLUCRjmlVoFeoXtNtZku2V0e7UqfPR/0uPoHFxnKJym1y5Y6aHwurbAZ4x9xgAlDt'
    'y8ZP8Xzc8N1dWDV6Q0LlbOJzt9yncilSfotPiTZTeJx1mHldeGGGMC3xSJUouGgC75CJkxOpcBgK3GCiSsGIo7UJBvThpe+55AK0'
    'UUMX/gIDxUfj9Pg0/su//m/qVNPH3LFOJxRGenvtKH4n/nVUTM8vkC0MvD00i+65Nui8BG6in7as3IvMki3KoTMtGGmYAG+Q0exR'
    '4BWNoY3hAiVQqI+hqzsyolMo0oeVbnGrWcpifpT0R0cx6nFmpxPt4QUMGryLx0k0GcQB3d9IiLxHjLbOv/cIlYWOvmBG7ACH6nz+'
    'dCYdHvYyt1VCpWg4giSeMp7nL2V294M5B73F79im4WAam9ZsH4og3TreR00Fck3fHtF/Df/zWzgjyN/C/wRnmx97aii8jdb3JG8m'
    'jz4dHED1+YnlNtl15bgDxBsaZZv1+Zj1n8yicyq4y/bh8bAJw2lh6cpRcFvZbBAY0tSORtmIG4crzJmF2nEEpBTdv9Pz4Mnrl+jx'
    'F8+YU40BbcVmh8Zp+vl0esuTbqrNNZJM8aYl816P7102KYB22KX35seep21PT2eDGIlUnOEEsyJGYwI7PC/4jm7VrVyFPb8Cw6ap'
    'wZeuU8pLF+iIIbWLwpoMA9VaqQdQ5jLoYN0M0Q7fvtpTDAmN0tQn+rBp+v2OG1eFeYBlpfdKSl/4Be3I2txpCOPZVMUXpcX3oDh3'
    'q8rDKRiajWvSVsGWLVrcbsuUN1YYf/lf/6e//f/hQIM3e68PXu/vvX7T3j/46cXT4NnbnZdPg6dPnh+8fhs0X7BP1Z3g2Smck4MU'
    'CJXw72d+fzcjrd0hb0fwjuOMKG3am2B/kc3jk7//mYocOBZrR7jgekG7a+WBPes5iIp1oAXQ0hPlBmMSM37bjfD/MEEeug0Ed1tB'
    'Oo0GyXzRC7pYCxVh+DPAQ0zx4CiSD5SfRFN2mTQdZIAF5v9Mgkz6+RP9BLJJXuKvn8Qs0ngffjhsKY/GD5dkmUm0YSuQ9PQt62SI'
    'hVk8Djv5fEioX26oq8NbxjOQtvc5LgP1BDQJkn/clTy8jODrXfrM19N7mOJvNzda8rgHjxs/0PeMzQdoAm6gyQS4XaQx4iESMqQJ'
    'zHGEBHGnWYxG8kBWAcJF84Q53gBRtpgMKN4CelWgU+YwmeGK89LiXgGpwc245UUv+Fl0vM7ULcZowIrw5lhvC754fXTEKy4PZtGJ'
    '9sN9ttVn+Kiqm1fxXjQZjmOGJKq4sf3qfdDdfhVsbr96Gtzdfh/c234a3N/efx882N4Pvt/ef2orv54lxzwA9/xT7vl97nlPxshv'
    'doC1SWe6DX6jZsJGkeR5QWPNaLPknVk1tJDFE/5f/pX/F/DZR/iCm2c8RRxtP/7V/qdC7Mev4nMaU9NB/nZDzlqDiRihiS6DksPR'
    'I9MTd0SC/BnhLVQOzrQw6pAjSXeVW6WCJOxXWKTcOu2cztN9zMPB0jVm/6xR/D4gI5LGogjTumK2UzcPoUaNScjkOIjOo4WQb0ck'
    '+w1+RK1SnmhbSW8HDfRLNXZEEGr92Afu61B3hFb9wL+dooUB4MiYEzky70qoReCBsSaq+mPjqW01nvQMG604JBwFve4QvJPCz4cs'
    'x1+MB3U81FHcpoY8Tsrzvh0PQh6dcp/fhlY78xR/v3v7otmgL+tT7F0xFEY2zU4HMOsxMJgx2txaBtVpO+FbjUKLR8etY9GOIZiP'
    'kEEmPL/FHyxxbL/sKUUWsX5Urozxq2b7ylg+N46W7prHWNzGj8Ut/MYW+5AcduTcl7GsN99Ds4M+sT4e0Aw2rEeer583kOztOE2x'
    'es9L60v8gW21HvkABByaYtxxGBCfcphwbBZHXDsMSrSRCXRIgtKIBDbKgMKXYze/WzawwIo+gYDeozNGVcoeAIBdwibF7IX1xwgd'
    'fAPR5mLU9zZ0gAdeoTNK7UTBAr8Saiqiukl8ToqxQPChKNidep0+A5akgBT89HA7KPPyUm1X4W7jP6el6Nxoyx90Pm6SrlBUfcPq'
    '7sgKxkuvA/YrxZVuwgyNtAvvPAxx7N8OmKcITbcclLp4eE3rEwUr7gJcwDLpD2pWBv/WLc4Vo4hkqFTtRxgXhijSO3e2hBQ9i8aJ'
    'pB9bBGjcQrcb0ZgEuuSyL9FApsa2kJaBG+zn3YPIHM3N4pF9X4y28WX3pLJhMb2b3gySQAwhYUGUpwG5stViO6sQTGfG8c2CPz1r'
    'EKUXNRbHapy7N7By4GG4mroh39yBgpHvPgUKWwS7uwW7h/wHpHps1oQyRXGheCsovMpMIsIGtoOR8Mj2CrD/plEi8weTgcEYWTTq'
    'gx/CpSMpYvNRAZk5d+oM4dNvX3qLdWWF1gcj1kgHJ7A3ffhtjL+BOLVWhYAKTudsoY0JJtIsYbOsebTIrOLaEQMwDuT6tvRLFPoh'
    '7+d2L5kkczLShPPfuXdPSv+Z33S38MFwYbi3FOeWz+nYetaZ6HlHbC8hHOK2A+ujeB99NHdpDM3QiepxR2Nhl0WbgdEf9fm19yfH'
    '/LPS5Efy5VEu9IquwoLeyrA/+t4l3QLxKjZ2kr6I6bMhL02B4t1MuMUym6uHEML7uhAESLE4twqRnMbFSE5+bCCKzqpWqyB8F8SG'
    '4fm3NavWeGyDIaDJuKWpxYYRyvs0UZkw3d0i7LWJUfe98Mj5aybMV9EDYra2643GkJi+VMQjs+QCawMYG5+KKMuC7HMyNRzVNrk2'
    'oCzDgQ0GxFGKoXlK9ywqJ9hoLBMYpeg/t0w4nXMA4xglVabpnfGYxaTAx6GqaBQDpMOJPk9PgRPA9oNpcgG7ZELAxsHrF09MH9wu'
    'H9o4C5rZHAhv46f35PXLkKL1nM8Sdgw7gU8lA+0D7vgsx6tlmjzNDO3lX5dQXlaX3JQAmkn8k2+WkcxbshUf0gx3ZZRNGzHaKPrI'
    'qttgGOUJS9WcJywsGlznB2ShOAGcbl7GbGby7jkSKSTT47DfR/HeAoY6ByR/Apz+HAXQzxGcm+Y7tqc+cgsoIpSmyc0cvzwbo5NM'
    'ZiMxPsfsETjfN/ttujGDY4wrA2h9fQSQgoM4nQWYwAsg0iUhZaLlVol1O5+1j4MptvwEqVyLRbE/aGKAlvdtXCXc3wGeR7vv5zHZ'
    '5aNQbLgOpcibXk7YLjVpdGX4TLOmmCkHKa2cv25XreD+RrjsRuO+k8lRmr/W2BIMbmh7xVwF/+9/BOrF3lUwvfgkS8kgIPQPxQWQ'
    'vCeT6CwQNbmR1DEu+nhzKusjZfaBqh8NnfWxzG63h7jA1hnMZ0t4Sia0ZPCOxsKaIdUvhgO23AXc+uuwODwyNh6XfvHcPZ5PlvSN'
    'pdBHTdsZfkQz3uVVsZSrSiOWPkPbuxCEIipzbJF1utno3CVbva71PTa9h3YcVY0ANyE7Il4tfmNQSmTV9l5HOgPFxPZ45FhNj4BQ'
    '2k8MpYQEbbBkSbT0RAQKiISWOSrn5Aqx14KEJ4tnK/XdtsUVsW6Gj4I0OyDP+ZiEwXO+K7QBQxNwG2aLMNKzWZyl41MKU4CsJ7cr'
    'MiJfSKQ+l0qKuNPXMjK8DgMkbrCT9EgtWzIhj2O3CniPWrIUidcJ2n6r7hhabBEcVyPq07jZGNsvCJWNVgIKbpSUwERy9SX+zNbc'
    'UmKzrAiHmTJFBrM0y0ZRMisp6YeJAgp9kk0j5GsbRtC5v0+qpuAcr+s+RTEJ+gvvQgz+8m//XnGDih4kDV69PsDbuS0ESHd6QYs7'
    'H0VzusHRk3hkrQ/wtgYyIAEGOTkSv09uahRlkwblqwU2ZWjkAliVZC3AGqIvKRsBFmZrYadRshQWcsQX34JFYZPze5wv6XbZbmG+'
    'iNvmyiImpBoVEWq8YZ02LYwq4pdf5IcLtWfxOCJXLO1O9w7W6Q0HIgsoQHaGrZ4hwciLeIeCnJ2iVnyeng6Aoj1PYPlg6aWaCMGF'
    'ZCy8x5CanzNKNSABz/DWX5ffp1MmROE0xoxdhPqIublxchTPATngCcXtPQbWChtlqCExEcI4AAymUhfZEV/N3IzE88YLmls0eAVX'
    'KpmcAsQN0hmmXhsvtjAJMsmVDNujow8IUPbxmGQaqtKJTAZtVBknyRI8gRdbZSVJG0glX+Iiv4THLVFSwukg/SMg1gQJZFLndNjQ'
    '6p/XfwrgDE/jsKzR0ylDku3+3bS08wFaco1zBbnz1/sBvYC25oCJx3NML9QK4vmgE3KM9DH52k8zr+Fhf0wGf9QmH/on6Sks4C6+'
    'FRxygNCDlyDrT4PP8ZQ3m0zxgj46bCPYETIYQ5HgCK0wfOD0uiV4JKU1dUwd7OPjVrGYW3EqRiteLAVUfKD25d20cF2XcEGXvjII'
    '41YYYJHbDTlKYmTyypbHT5+9fvuURIBohsWeqkM+SoI0n789+Kn97MXO7wLOJtYLns3iGLWnYn2eCbvECQTRISDV8CrGcCJjpUjr'
    'UQWaJuV2y1Hp7DxLsowhiyZHs3QCC0Nx36G5syRSpmwd4ReJB9QnxmDnCK9OMnoDLB1nLSw84FXj9iLh7KQiztHGzZJz2wnex0F0'
    'liZDxhpwCZEXBAVuZSchizykmYRRB+znDC+OgAkMqINNTgK+04EzGHBHaPBAdhK4z9wQcIAAj7AIOGHew4/c+BOk7UKauZpxQrcT'
    '0X2UIyiIL4AshLEJUstBgeLMqRHGRwFGR8GhUGKHr6w/dKX0RBy5VmbT+DW0jk5rdemHxX4GV8yIDoIHZ23rwANrO7D3exOoRYAa'
    'A920rSx10LGp1SQBSnep/m9+E+ReUVZbCnjxm9/kwnvmS34kO0tY0Zo1yhujjgcVhqh6lInL2uApKrdJTVnUUW60oFnWT8IPo5wM'
    'rryGa4wvcxNrBba5QLWnw3znY5BfR2PsN1ACdtsu0Zgre1USUbRCQKNFX05b9/rgaY9Qmr1VZjEFpTGC2Zfv9g84lU05YmfsbHDJ'
    'eMzIBW/laanALWyhPbVG/YxDBccNiXKS5uSMk0tNe57ymQlOoukUe1EEbYQB6ILsPJp2AhhckFKeVZmWoKdoOAwMKjihuDG0B4B7'
    '0uNjODpAzoToG4ASOiLB88OHcXNTR+ZuMWQSJXCKAXWexXQvsd2st96li6fUPl/CkHIg6SoG0vKgQVMu8lDUBpHm7pBYHDLzQWRA'
    'Mi+w2asy2UbAT0Do/O949+zFKRykHbdH11cG/BId1nvfSlcpPr4zKgzFq0ulvYpKe16llS+RMkRfY7YRIAag0ATl6N+WqWDbA4d1'
    'CtYd9C0fdPuT4Wt6hgXbQm/sjS3KwL6xJZRumzjAjAMxf7LhsT9xmvvbl2bFr6YXW9y9e7mHL1UdE+b79iUjMMMiPAoalNGWxEAU'
    '//ZKVzMmW6aaESnllbX+117QhVZk+hZydBAEuEKNgPStkz03E2v2kbe3M5BuDkweRtGPHflMWjJT2sVVy+Lx7tmK4EBlHTzAozlB'
    '7muZkQ9/qYAD/vg1AOHPbcK6vd/afboGQPg8ut4RGqBbeJSWOMzH1qSkonayrhJ23x4QiwzuBI3pRalowC6UxQGmrBoCUZ96S3Eo'
    'J5gxAEBg7rBlmSTMmFJY3CrJQ+tlcEukcLrA8jlXimcKc3YiDZq3k97FF1PgQhNJZ0UiAfR+RZEBGvDM4nWO6eDkAF9RELpUQFM/'
    '+XzpVabPPJ6wkjlujkIgEbckXB05kQFfP2NuBS3BjjNHDRRvdliHmLgbYbg8ji22zJ4xZLFuTsTxld4/Y84IR8R6Kc8yLicWDXHo'
    '2cCKlxze/ROkfKivhuUTSCVp1NV3nN45yNmt+ihV58K4Ie/DdMygaL3FlINS735IDvNGjRUsBPIEtHfKcLGcjhfAoLBZPEAOkmWu'
    'G19iYARxyRxQ2hGJaKzWUGrcUvajg4Ky5Jo3nQ1gTRkpZEU4YDKyRNH4HHHUMUb3g31Nx3CxUFqJwImtb+XZqBu6+lWxQeZsPdEm'
    'vVnPnCOGK7YCTlB45wDLCBJEAPMqnbQ9u2C8iYlfwr1dZ+GekWiIw2eczIKOSwWFchLiCUQGugDuF4jaSap6RQNFkpEcj9Jsvj4k'
    'YZzJbNM/Pc4MKV8lKXB8coHJFaExseNDdmyUI0Wgoth3YiJgr1DZC/c000swatMMDdFo881CZVihVNSG5gYWwYjI6dY1+Pzl3PvX'
    '4ZivdAbhpa6gRmcrPOI+q9wZI4j+vcZr1MkdEDrFXyVBMVzjzNrNszdLBCj+6CieWaNVK/NKMs4PRKJU0cNbD1c7CjrI+XH6Fs0l'
    'MhP2xqz8LJuS35ItPa23cfsoRoLFxCryzQmCc/j/WUxu3cC3ns6cIeV5JFmcNE+z+eXSq82wAlTgUwFVi6srfrIAs5mXsVwVvXlL'
    'l+RKIaPfU3hxe50xHsla5IbUYj0BsP0sxMWDL15PFA91bD1qDGFpza0tXwgvCMbMdciOeHwc8FtYostmkQwS54R0XWEd4MoQMfC+'
    '00/HFEbn+42NoGFNE4XnELyN5ZJ5BFQclpRfqjDi8dTYKVClq9uX3Av8wNr4mcjCn38Ouj8AIR+492QC9xy5BFi0aJJRXr4jyVWM'
    'beN6PgZ4wygvpPUbT0dRP54ng0Z+BV7GEcolcf4YS4Gnz/sxjufQxT5ee5NjL4XzKJq5HMGUaWCf0kQ2CdgpNoCLlvYNFc8ZbAcb'
    'ygubC8Bunw7iZlNADl/SZjK9eYcmduJG26QCBkAxTBuBm470pjumBBvBdxS50s2KI7zl1wSPSdmCwPq3goVeCUqehZYTDeTe0CyO'
    'U2jhrxnuZuOwAyhrfDqMM4TODlXAHMr2AYGCKisoksFtB69OMfUR1cztBg5cG0VfvBf2FMueE9RsqgIRubVheCkeMYW756HKYNBQ'
    'xjazHmzCuFRZnkxZ0R6/sgrebzINMA4ed2SpqFGfnKHt5CXmceIqb0niPIOrr5R4DvblveXGayDYDIV40Xguutd/rloGWaS26qB6'
    'IUoK9+SlPoZm2m6P60+NRWYIvEq8pZcKP7XMZNxamdnd2a47K6ge52XZKhVXq+UU9Elgj1GqzZqT5FidAulptxAjo0bi4tckpsFr'
    'ppR/KEXYrg3G21senOB4ZJkRTtVSG0v0P0xKRjR8r2MgUCRKdNvFxKSJCZPH2PVhCQjqIWGp1pKDjDEmHzDG5OO7rdb7kRuDPdsw'
    'FG+gmNHUe6G8CcxF4mET8zbk+8X07M3Y1gSsqccPE5L4KVS5s3k/5GlaXPtdcI26JQqTsrub4Q3gGm1+m5adPB6n/Wi8gxecIL8q'
    'Lk5/MzwcyYoQLCw7QSSJVTua70j9KVdGz33NfG8xIuQ/C/5zzn9GPp1tWgWqKbwm0Y2U7eb1Se0yupiastSwZPqNmN8pEN7YrqKz'
    'zZzztLI5d571N1qOku0XC06cm5y+GcM8yZqQI1SYE22MkzoCVBZVpxr1FtxtM+KBRhXXjUU5qSBiChO6wAiv62hGz03SwjpuSJGm'
    'C1c4G9zecvzlSOC54CA+kc9thicDC1XUDdchVE/wi7Gyy8Z8x7UL41dj9qIVVy07kfjeurNFyCor7+9SsEJpdzOb0u4N1Nj0S+5S'
    'ENsGu1ts2df/mCYT9V5t8OVFt7Xoti42W4vNK+7AtdiPj5PJG0Cl5gizC6AcfFyGg8U0Vscf2cMGdtjoWSSDur+DtEn9hG5I+Ao7'
    'lVe8hNBP0If79vOW1yLKh1WLXJbkR2b0bfyx2aYeKhrAZYdGPPHTitUHyWwwxjnlbTJmF9tNqh2ub7Zmi+0mN7K+qbAJ9Md5WWPo'
    '7s7sAnq8M1u06IaK+llzdhGqh0XYQjsDevHm+XdLlufKH6ZM8VcbJfa/ZIzRbJaewxj5CO/gE59f2IEA9iIAoAgIKlQjVyYLIvQh'
    'sr9miRS6qHX7VSIx5ITav4vnHCDkjejM+Kow9hJv6epiA9wfJDxH8AHDPh1a6+eMRHxRcJycxRMj9SOLSLJaSC+M4xC8GGD6PD8A'
    'iY1AUghBYoKW43V7zw9wxTxSGz+2KIQVY1R6oaJsmWuBubUNogKxve8YM0l4LVOKUda9MPBLCQv9gTYb5y7/LeTvoYmrErx6L2Wg'
    'gXOA5mKZbvBKFWmVNbMZvHpa7OpOMFrftGXuBu+LzfhF7gXlraie7gf7JQP2yzwI9kt7UkW+D2i3Dg3Is1cOQwWH0zkS+OH4LzbK'
    'Cy//s6cf93ZePXnx9OPuu7f7r9/uI7MP7TUm522u0Gg1JupnbH9jKVfIN9Nq+MUy1VimftpSt2D8+mDsJfMDOMx8OJhBO4GlPFkU'
    'zoacCtZNNDfa34d0LUNpLJxkZOEj3mxSltN3t/gOb3ctKL6FuX+PAffZOkMMcEfJvE1Wf1yNI74NaX1NRAEs7QCa15coxIrzXZUe'
    'VqoKl+HlieW2P4xgEUZw+rdNWdFNMU1pkfAJns4REEY/bsOsfvObwH3BYzpa8BcrrEqMx6Q8t7tlIiOLQ3lOCleJ2OxsiRxXmR0o'
    '6dlZSfJdDhp5trKSbXBmBGWDMy3IZc8XHGYhyd6vjNlEexVlqLJxLs6cp/xWGe3YmB33o+b391pB9x78s7n5AKbe+W1oJa5abNTt'
    '3Devs5iIX+yq+eF+K7h7aJdRU0scTBDAKyyteGiVlnlMwk6tcL3jRP50GqERKDkksEqQNfrXPR7mKFi634B+mVUUHtz7VbFE70W/'
    '3Yg3yxSMI9zpt9gq/32LOyN/bhCalJuDPd40TfLv5lv4vRly4+pBdZHb6G837z+4O/i+lNLfZr/Cwv4tnQxLwtSR3sUzVDjTX3yg'
    '8TyXnNwVj2yebhOZG9vLEFCQ+eCvR6/tkBf47vyi+WVGCAWHch22dYxqlRIbAxvAw0fOv0MPn6zpySyXB/TNuSqWxPEFDrC30Vr0'
    'Nq4cVpt50XwfC6G5S84wtLvaaxFRKrpdoR8HhoG2vz9sHBoHGpiTdaZRVRfLq/6kqv60ZbT5GGD6ZGqMTEkqngJSTSZoux8cp9aD'
    'yPMeIjPb8aLjgmTkTC8GyACJ2o7UmafzlDJXkt9C07gpmcaBBfrLv/37+9YemetGaPI2DDuGdAG+10YlwtGibJPyH/KBZtPo+CKZ'
    's8fFLG6TDD9TvlQon1OOUh3vGmsOEBvMyJstVBSNF3e2OVhQoXk6havJK2Qj5eGtIIHtFLwZdP18Qty6DcThHQlykmA5mQvV4eL8'
    '4tdHHVndIgUA94BngsMuF/RAspnDR0bKJp/4ib+V3/x+FBlKMYMVZQiUypm+aE9Az4SXiQNnvassvbya6GZYqLhYoeJ5QSb/wORz'
    'kvjAlui4+2AjVC1WNqmk467VbrFRLQZDUmXFpp9FJ8nY0Ek1qttCZRZr1Ym4Cn29r1BSk9r53sZGxeRrNNZiIDw7icYlu6iUW06Z'
    'iaO0mi4fXrQ4VCSaK0g/czCndbd+aOhlGha7Y/CLSNJ1/GM3zz/BFJWicHwH6clJMr/mIfZDlJWF5ak2rCuc6jwCoE/LjrpcTNH5'
    '7zGYf/5gc4h/Lxc7FTLlO7BVJ5Ly3qsn2d5dPlb2eiCPrBxiYbtSXDxktjingDHNNUJt16MRtFdoIm1sE2MGMpFkYlgQABa2lHpw'
    'saW690otz/Ora1XOJYFRgjoez2oGirFTChpsBxidJMP82bAg32jA8pZENnSWHMP9TMrf1Rfnb2CyvpkO6itgQwpAChuU85yxVVzk'
    'u0IwIZXz133zunCTNT2UxykqTQ5YKNgqjWcUqsUucfPS2pDLVXflqjo6TwVPUhG6x8dpj1Ej4eO0pl4ib0dSm4/s8oqXWVSIDn+F'
    'lXjSAmEVXlsdo5Xjsq8R7gN6Q0ylzN0LIhBLCVUZNJjsJw19VXkJDo8wnhAuTxvLSqBA73JcLUc06ytVPZUThnAfqthSFuO54Hyd'
    'Tkf3ZVC7r0hUBaLhkJzWEeTiCQb8UnECYETMZm4/lDgV6Fb/ZpZOI05+3QzD2rYo9wy0opXTCtfpQd7wCtBNyL2F1Iy7GEoKeNcE'
    'EjxY2ip7bSgc7LIMrxYw6s1Q51X90kk6Mb0FzkDBphJjHetTTnzsVIsVmcWsQrj8EJPLQtFuId8Z205haFL+MpjPxv8Uk182vziJ'
    '5xG8CL90PGrPr5YvWH98OrOgVttkC9i4dDKQCOfSrvNi0f5S3FtYRsnx3IQ06sm4Wg5CGa2qeMHqBdEBveCbbwTpMmEghdXV38sd'
    'XJMmp+xOc51aP6yOjmXIWMCMoyb0WzUvy4zwn07jbL4zSU4IBXBUWV512ZsjwJ1Zs2jlIyqMHTdykrF6UqPCxVGY6qFPOIRaQp9T'
    'IpRSFhiSMGBTE/jbbvv6BHUl2RvJKBS0lPyBfpUWBOVpiaTcls4JyzeNsPy7Tajoy8g9TvTnn7s/hHd+sKWdmoOCfsEo4FBeoB4j'
    'vbiTEp25oA8L/okfFnfS0TWUHM+SyfAgnTIm3pmr/bIL7eCuKgCkLsLL7l7k138p5aD3/pGLWW4i5QjCNYNTEF8LD7ocD1G9cWOs'
    'g5I83ZKHmB/8l+cVxruuxEhz90VocOY5P+hw+QwKDhYdTIgZrzEJ5W8qZMLC1Fy4mgtTk5SsPCCqqqNJWNlYNW0J63VVEjnBgV6F'
    'EHdfEtciFnobHzW/Eq4wXHgViGi8ueWMBm05CVReDQCP2ALqm4LhWR1AOqs5gq+HQZkBmzmyqwOizBleP8q3BqTSpQnK4DavF5Sw'
    'QsX9rBC95+4UtWFTfLOEfieamQoqyp2ei2LLWXxklGYFOMFSVI2JcyQTOhxoomkjlLXgAoY2XD/4oHkCeO6UXqT4IXeZioGYLA0V'
    'Ueb98dxIYpoJXA8iD8lnHOS8ozUrlAxVWgVTHI6pLc/jlCoEflIqND8sS2Cp7iv2XOcRuk0YcGDNRitHg4TlxREtSdkaqWdFZTGY'
    'KBG7lpcn9orRUcO3tK6QKZY0QRLDthjGN5baa1ct0jidyciLQtul8V558oZxEDYwH9DcQaGNlW3AXVyHV+oG5cON8FHJeWCgoeNg'
    'BMmrjVxkxqs0ykWp2TrPGaPcFvcLTp26dBxUmnSI7GxTO55mieg6JJzIlQtkK0eP1BimOQUWOKbAWUqyuRpSKiIaD3e0iujYw70a'
    't2BTZiSM1M3hgQl5Z0lJvH5QEq/NexsW7mUifOqY0zIMoN+HO2LSiyfmd5K1ju7pbkk/xhWguid9DE1nZfoA7K99X3VXOq8N1Rk0'
    '9cF0duiQYemiyv3tiR2q5Q2rCRqWyzlKBBG1YoglQoiCLO9RRxPu25p/FOGrLuuRLdseJ6kdJ0oWbsn15PXjlJ+lrwvSLCNdqedY'
    'r64R+tw/+QeEO0pP/pce+SVo5RuhMByQljmy6sqkmGuKs+FlVQ8NKgBYkAvm28Rl88p/+TTLZND2RhP8liOnUD4jEhISSZW4rBXi'
    'd/qmHkZNb8bLtiDKEC3hiC+l7K2dC5YCvAF/OpYS1xS9m2ZcKtsqk9JgY76kpibYlXPlKJfnJPY8+s0CRpJB20OLmSy2RNRFsIMB'
    '+JsN1OcBNNTcsNN5mwqFdSkESlGPDCGshgN/1K38oFeAA4qAihFsc/uPG1my++gQRalE4dPFln38CR4XW7wTmfpIaUXp2zWZToVw'
    'UyToEWh4FV18CjHn6naC3VE8+IwVKD4tmdL4BoVGzO/yTWWGABTzdjHM8gNNeNDyUMUcUfGyXpcwkMXaOYEGj8qk/PAtk7lNTsXs'
    '5fFzlfyhcDgkCpDLk7bvsWnSbLzBpCTKWwzW1aQXlcDUTlavv0uuUWsbLNx8rhDlFMVGeOidqjI/qTKLijLvVRljCltRdE8VFXtY'
    'L6LEjvHfxp1Pp+TdQHFXJ/FsPR4ex5iYBIPOHCUXLqYEtx/mfFqgOlqxf/i+9aB1v3Wv1e627rY2W93WxuGHH9p2cQ4PxcL7dELh'
    'nTlaL8ZxHHDgtVyzymA4P2xtYWbiYJNmiS25eOSoC4VzHM0WuYYjhKwPGzDATeVNb8eJJJfZLPRaMwv+889k5tEr2Ulpd7FquwvV'
    '7ujnn8lWuZeLvEr/fbgPa/r90tZ61Q1rzyILIZKmFv3WLyo/I26KfFCsRm+21Crmj350/u2iU8QHBzRbOUFgXs6XQ3ibpQjPOupg'
    '5DeOf/nVbFqViGXpxS+4yplmrHqN+1YJ9iqHBR1SCj3vOndgaT5/6dVu1jznPczyQamhhqnSimnUKV8wyzOCUNCWSA/qAwGTfFj4'
    'nV3bwNZKssTGVqxoc7DXOJ5F/T6ygFueR2uNwrXSyqXSjCUXD6m4k3anmB6r3DhHZhWX2gsgXGvaUTfSKhsjj9rwhM6lFynv2fyF'
    'JWhczi9iU1ta4hxIQSurpjxhlzpZG5dm1+Jeo8EUQCs4791Fk81R7+49kxveJEYymdWMmKJnmfnNe2R7k3E4AQw2gGV6JQJF0wYK'
    'rXqSqJxlTeaJOJ2ekTk5YUUP5Q+muidW6G24LNZHNmbcLX2+cgnTeHFqDI7KE6Opdc1B0cZyG6MaS64yWrtEpL+hCGylCV8OXPEi'
    'HgJf2ghrIvHe3OK/GH5dqI2KMIP44rmJQNVUBqIXoWfVu4DHLtqFdYYqepeX6qzxLQ7rw/Tiw8ZhC/7t0r+bh4cU/eNs++EZrIJY'
    'snYfhB0ggIhybW62GhsYyoUTWjbCurOK9u6cixtXNONAeufp7DOS+RLbrk3MpoCMzXNHobZpwYQPwaD8kyAfm8+IECndL9svYWA1'
    'HdEviPo2yDRGgUhtngYMxeWCaZv4XRyoK5DGONwfJhLhxmDcJobt6ZTs809OM2l6gqnTgdw9jiVf2zRCDxeKEH6eZJhaNohPpvNF'
    'boAY7w3tzfvxBPocsZkTjgKXQ4OdQNBiFVUgg5ar8ZvfuOqKv1cBBu1N/aExjSeNFv47SMbwoz+Dkw9/4xmcyRn8IH/yVuMkmn2m'
    '52TyGf4djKIx/j2PMKsJqwsa2TyZTsexDhVlcuRpuqOU/bEJlfEOzCFuRuYIw80CxrkDkF9MKSme0DCDefDHU1xOAgydHVpDXOF6'
    'FPPLIs67g2cNMIwMVN+IZdixWNtVqMOBNTd9NkrPD1I4ac0GWt364MWQPDTngEPA5MLXeTnbc55Ozj9ofpGz9zYdacFtQZZbDGTj'
    'bpqtUmdHHwMz0KHomXwgNyjCQDdE+31zvZZllM9/8+Nq0YWrP60YIEPW4gMHs2hxBIqWiyPRMjEhWhJ1oSWRDWrgvxT6cYiTaGqy'
    'n+b2xL8I2KfOhX1Wv/cKaVr12tIIlwzjGZR5fDr4HEu4ovpbx8sEyZlEMEUZpcTJvJw4QkIjx4x4RAIeI3o2SRAktmUWSNRIiRJ0'
    '9GJFawjJJijlAQHKz9KoxuZbLraxtoxU4G7JW4+YLlIPDLt+cCU+C7uSWjl+PYVSJicYgMccRQmoIk1P55YNKJ6hrr520fcNzj3h'
    'aSJRM1jTCUaCdfcXe3PgcmO6iMCGcJEEX2kWO5OjD18PtefDxXihX7TgTML54vWdUk4/TmGFAEGxo9v8jAPjq9tE/G/CPbXOd9U6'
    'rcA6L3t4ywsPRbvyTemu2OQN6fxtHv3w3QfYxxHpQE0z7pHnjc59P2BKNBuIS7XSEd5vUfshnVUJkKI8gbVHcTP3bqX1u/Lh4fnk'
    's4GHGeX3ErIlyKaxRDCgEG9sI3WGttlzzi1bAscIBJgMB15+hN8v4KbZp2bIfkxukRJxNab1Wk1cfU2Rs5OxvGXpMbKev1pUl9WF'
    'M+WictFCWkGvDZZcKdauNomqlGibuASSIUBLjXUB6EjkIVbEBoC7EFGIlbPpKi+fv4LPmxsiUT1JJsnJ6YlLrMABgjkLz4WVkT2J'
    'MfEegiAGhLtYX6yfr48o7zfFxT0fJYORDfBBsauBsOYgbWjLNrnQ8yDBNlBgi/xLGSjVOM9/hItyMsq/5MykNMS9dJb8GY2lx/ZY'
    'fIDDe7cV3NdSUMR2XvIspObb5AkskQx6wXuM1zo5jiXmPZYw2eHPtW4f1rKVl7O3A8suBmXzFhrYrzI5L5q3f9hsBfdawfclg8dM'
    'hygqqB82FVl53HfcuJ1o9PdAfqPftLeiQD9v1q4oetXaQe35g+LcrzSkUf2Q9nApHcYsgZbCUmKVSUmEQ4yl8aByKfscOr9qxPx5'
    '5UHfcYOWdWQD120Ahi0xWYXfiy0bX3NyvmUjXk5GDqCfGf7WRKlGmRHcsKecQ/uiu77orl9sri82vQCRVSHuZCBdPZKuGsrFJn2B'
    'CZgBLegNKgYmI29GvsFHlbRkBfeTOr1mmXxCrhG8qf4uLpGVbxMrjF1+m5R6At3gijFgKbeHka87GF14H37aqoFLDBGrARIvEQwi'
    'vyJgKv8Da3beFJgUUX/XxZlWNUYFK/SFqbHI1bDAL5oDC/+sMHBHwNijp/oUGFPzdKQp+V/7HHAEMagRDzGdR49EC0ZFL3oKSggx'
    'wlB6rMCXS/qaIPpNDka/URSQT+YsjUTjK1pMHJo6A4BHxcPgUqFUg7m1A/dMBBKr3SY2ocZIwFNgSW1cx2WKugDD5OR0RaPEDLtE'
    'Y5ngULnpR6xVonAHQ7bZaeSkP8TzOf62KiTXqoIhS0iuREf+EhIVExFYBCghMU3TUyUyUV+JIdtQAZkqhVXloiqWMtXKn6olUDcK'
    '0FoWgbVw0Gg5TQZTYRjVVtgdyIVeJaDLhRa9Ev+/MhESbZfpRoWkKusKAOCiRcTM0iaNZMqPsvUFjQoQmSZNTFPb4p3hBUZhtM3e'
    'GS7w2cbOw8+hfl7Q84Zm50uistYOyZvkLzsiE4G1bjx8rJjPzwVhLV94AZarYhgAym31GMUP+7wUphXszehLzSVlf/1kVaFOkNhS'
    'B9DauNZdbyViiHdTI4TAGJkcqsMaYMky5K8ezY976uyixZVB6V90WxURPF+V1q26LKfrEo033WCbK0tKpbihFzfLCMYKykMqeFen'
    'X/8wrKI8ZENwtm47DGWgSdRS64Kvveh0V9asrB5/7c1ZJi92XlIUI5tOXvBVbj57j7qWmQ1wd6A1x3wrWdJEJjNPUQtKadBESNzk'
    '6Df4+iyJz0NKmj4JrH5VqV5v5fNrlxEJsuDzi8KYVr6XfXUIE2FetHIRK8ZEgrmYeD0MY6cwzcI+/HRVEjvVo1fC4GGwiRS//eyR'
    'LvR5RR0mrViJ/YlsXwdTmADJtxHC47vpFJV/cBWEbDhAJdi/gvSawus45Z9pu9xkRYxWTD1JRXVA7wxGtkUvuj2N7BfqERH+Zo9w'
    'N/xZtLQppI45HQARAaQuSphN+Fz44nroeXFoTE+oS1qUfPoJ7xjX13kvqNgsNLyp2qmWEvSjWY66XSxR1nN3j7GICXImMYFv7qTN'
    'YtwmLFP/VhjH3Fj7W2p4UXZcViPmiZa/XKqoytLT2SBuI4ch1GpePUUDA9B4ico9l5Q7wqjNFABxIprqSSD+l6jrKc0zyKlNM5UU'
    '007m4/DFNXyjTWnUBQ5rdIHDWl0gGnEbHSXqnljNItEbkwng01yuOJwYJvc9nZ3BqDJZCUkJy1lYK673EqTCsjoqdDA6PemXCgl0'
    'JNXgjWh+KIoIZdud4rL+jYq1KM+tDBndHdAme5yhQ6q83GW1sMkebEL6w7UZ0+ruvHgBS93PMHrHZI7tieoL77R1+X065Ugtmag/'
    'E6cge/4E2jqOZkjYZBhBnTNmQl+qLSJXWHvNd7GO/6mSt3K8TuoiDvpweWdQF8BsmJ53eKpWUYZajlmsrNHHCzwt1pycJyDSlhnc'
    '9NgyR8zhPKWdXJxOu4SK+n2NFliiWOdAzSfYf9Dsn87nUA9IPJTFAVF0mm0FyfEECQXWDLD+NZ4PTLLSuCPjOrBniBoj8U7ckRa/'
    '4RSwhRifsm3Xi1FrakEHNhF1HjDyebELBdzAnw8VS6EdbIpBT6m8YyS+8iRmQFADti+fyHy2QI/ZuqL+lIAbG2BK8eZHaOLKnyBN'
    'wSCI3xHOFhAQwGKgFksoMtgzOTwNimtmcazXKyRIPsDUt6hnM1SviVPC8kIxs0Iqm2PbqkOCUcY6XsD5dFDQH+dI7eUiRE2K69YK'
    '0e2lM7e5/lIpNwKmi3PRmGj1xLvMH/qqlU+nlEJBD4VH6Xtong5GbIKJwyxzxMsDcXBVaMCsaH0DZqWCYh6A6swsOnMkJfsWtRZc'
    'gJNNTi2DZTHdjHJPjMmxRllAG6OsSqOHFfMF3SoVlOmGJKGMMgKjt5gjAUb1HQ1+AGwEzaa90bmHJKr/OQNK1X1eta079W3d8doa'
    'YHQvvQ7GQiQfvsg30xIRC7wli1+9O8nJsRCGRLddy5JMZLtcXRqyRsZiZx/NoE2M/yFhj6UtYGYuMFKtyrowp/iDUPsDVzoETvPY'
    'f3Wniy/7uZeb+DLKvbyrgihm0VG8K2GGm+v/8u2HjfZvo/bR4eWDq9vrSQeZkqZbHPRfsk8oKP92g/5TaUuPsKVpNMNIa/Ombd7w'
    'Za27Yav7AA3gjuvK3W3dN+X6deXut76ncubKmM/gej0iwnV+jD8J3837+LNfvFyB7YGrGt3gKF8QLBYaS83JYAfJ7v3YC9VOAe+C'
    '5vSiNV2Q18508Z3btztT8vo5HyVjdsQbfLb5br38JFAfah5yZFcoNE2nvjzqM6V+XEhHjv2WwXVGUdb8TDq26cWPGz//PL14uO3G'
    'Ac8LertQb/fy8bAExLeb+TmE390rYfgJfpLD9nwWPrwLjec+APS158flnzbhUx8/5YdgphMNhzAdfif9wB5uBbZp2Eb7tAlPfft0'
    '93B7875YlcliIgMAS3ynC2t32IJfbfsL/uIx4V/t7qGLnJQXr8iJtaKVfMaFx5qVgT1G85y/CZZgFxOJAKkyTLIpkjZo1xxR1pH+'
    'wiOiKSHWeEwh/ZGiYc8DolDQuUnZSALBg6alGVlHutj+LBDUqLVcmK0l2WNMhQp/WXwgkgUjtKZDYhLkkbAO3uQ8Bd88fcWmmSdp'
    'CjR5BOCEoV7IGGr8i2/CLZeGDS3/e5VGp8pquzx7idJ4FXVexuT6hnkJg6KeqjCOpvduJbtJSSdX3JDd5y/EnzeZTMgXa4x8EBDE'
    'MKrjUfDL7wR6X/Ryeuw/slr1juCwGYB4ipFZ2miGGpI16gNf9vhHVrquVqOw5VYg17UQTVV+uB/eEAx8m1hnQ+s3+CXA8UfY4D/e'
    'HDxy1b18gzkwefz23f4eQck5Mv5ZejQ32JOYa8BZE0BYgF0GX5B0UEEFmyMvPaG8q/e/4KCiaXLn/t/LcX258/afnr6ljRiMEsxM'
    'NE+mwdE4mreCE+BtEsDgQR+olmHw9U6o2MjnTyimcB6+nhryukKIurWiR4AZfeP6R/T+jY+oAMDdSgDgVF8rQUDVrvKdudz6wLkH'
    '7MewwEPCx+aQUSI+2vCA4kRQQuzEGrJXzmyj89vrr+e9cLV5YRJ6IgQK07Nfqma5BBoEtFbBTM9f/RMfByCGkuNZNB0tUFjNaIl8'
    'ANpsa51zAAiWQT36AuRBHqiyeWBWbrSYpnNSzowpNFGb1sE/IuI8YFcaG2gFdzf0dotWBrYbeBmSIWXj9LzF+0/PRxG01Rwnn1Ep'
    'OUn6OY+PnKuCzpgelrsyOM1N/lvhFQLE97if9umuP8fkvOqua3ZZOeU3uB7c2wjD60Jlt9O96SFPzr8Yu3+ls10Hx7t7Oy8Ykocz'
    'pLAHEbqvx8OWUGHoC4yy7F+GCGO/pzy4D2AhvAiAxiznaJyms6Z1E7pft58as2z+oMtpKzJvB22s58/sePM5+JHHAj9dtlAV8QDP'
    '5GeALC6U+0oJ2ghbyWFFWnBeQyc696dCU0hijonGlPN+46ZmFo/YWt8pIhHaBES8xD0K/a8GAG8DAJhZ0d+qxM/qyqGdl5G7XhBf'
    'zNgpm26adBRn/t1SvafdL6S+4GTXn8+/7jl8v3Pw9O3u6xevmcoiSheT4gJP3oc1MFk/Y0wDAhcx0FrxCrSWOmrKtTB/3kYxOSVV'
    'yfEGVoY3sPK7Hzbw/xo+Sp5xBC0rdYN2c/I7v/xxZXkjx/PL9yvLa3meKg8L91bv+A/q+ttFzRuW8IcEa94V0pLtcd7SJvwO9wLT'
    'trBAYsNIJqgL2y3VRrkUyRr35+kUJb5B8Ik8q29fzq5aty+P8Z8+/uOjqKvwU21DnQetVRrqbi5pqFs5og1VMY8oqaGl7rI1CEOt'
    '10ooAymUeM6A3gs223eD7AQlUjOg0uZozDnn7ctyWw7FyV2uDqlzqQqs7ilXFJJUA84jVUOfwSbdAwyarwlbh39o7vmqfSNv8FUY'
    'WB5bLRQ3wgZfpVFZHKXqfAy+w9HdLR3dvTBfD3d7s+4Y9GE7+3wQzM/+TDVDDdzsJHTvaQAubWo1EC4H4s0VLjc3pWvdbnX4ff/g'
    '+Zs3L54ypZXOM0dpBdE4lXylGNAk+No0lnEj/2KmYh5PMy/VpUeVUXPrQdPSEj+EYXhTsmubeyucUKtbsPD7kAQxSkUgzpb0nV3x'
    'sf10dhxNkkEAQ/1cRcVxl/nAhDek4hQHbJu6IRVX0tRwxtim/Dz7lR/4AF9FUdXgrhVODOumWjCwLzwx4kLTc7fAM8D66CtFR2c6'
    'RvIRSa2/GyH6zeVxVwX9ERsesw7FpGH461qa3WIAfPb04+7rl292dg8+Hrx+/eLj796+fvdGUllN40mPrP0arYCl7PaRxKv2iQV8'
    '9hHYdfMbdWvIGtpvjnq1rwSvqSq47D1rhosmXv4TwqB7w8bf6tn/TKbg9hGtVuizSdMggcvMi1tXWxUr82Ln8dMXemXeYPAnuzBv'
    'JAiUWZrHHAvKrs1LCRTCq/Mco4WYpdnloCGoO1ar816FEHFrtC+XQEsW6QWZxMsaoe8PkRHUmFsptHmA+0l9tov2lL1p3LJJWfde'
    '1o/sWdT6UbgaNqTQq/iUf0xpqhxABF5KPCwJBCixBPGUwLqgMhJllugpQctfSMGLh+XZeIFWgxJ93NoK/ek0ni24bjrbAczU6KAh'
    'WXoCuGPePqJKnRSVdaEN2wgVT1F5j39VVgjJZNvg0r5JUn03J4DKPlDSxvhiChg3Hm6voQ3s2qHqtT+3ySvgZ1nGR1MZwyySH0Qj'
    'rAg/7xakeQxIa9rCJmG5eXHiR8WcjM6GgWdfa4fHy0bh+Kh558CIlYtWFOcACq9RZrodfJNbVEmhl5llNQlM87tqejBNGVoh1xxa'
    'CqiWaCkfLVtL3IqGw8MaukYpDGSXt5Gin7OyeslCumDpXLw+VDouIztd+pv58SjeWwDKm+sBPMcVvR6Qc77AD2gQ0cZ+NNDxNz9R'
    'JL/zG202srNjADcvXK9Qi2TAXg8xMktpGUcCW8L+No9KO1JZ27j9sp6TAcvyqQCad03iV+kw1jkgsUjZ9o+S4ZCws9r8wIxvOosx'
    'm2MTK9u0m7mdwTCralvePbcGCdfCCq1Av+H4TP47HlODJfJ23zAn1sPAy1Rl0JMkrQlD5SVFp5RDMhcv8w8EFOaA8YH27JHo1WNE'
    'T3V7fDyb5jCCiyQuWpfyhWl++tbhFGDwsP5V4OB1e+32Jf69Wjs0LJ8Z0aP80TeT1/u5pJCG4ueDdLISJC8FXQeh++N0ThypGXKu'
    'Em42fWxjaQ36aky/+Y1tK7S/OmROsXfw8oU9BVi4A+vIr11Tpve8M/9RdJKMF2Z4zn2DogTakJY9/ZnpJPwuv3oBkUans4aTRXFv'
    'nXkyJ0L80+3LUmqJQQ/t1GiDe0DwIMINbl/ywK7o/adCuzXpkP2+dXhG7Vhbs8Pm4KltroGfq2KGFYX4+2bFb5IW27oU0zBWIDem'
    'GRbUJAUiiX49jpArsmaK1diu7rK+YXhvHdrbC11BFu+UadwQjYMYPTkVfT5LMwDJxNGRc01HmpANLUPf2+Liv1geSVw6dpCqKloA'
    'cMmKlqTGbroMfnS5wRaTyS0bJ2PYUY37sc9+NMN7t3yZ8WLKQZ8JSzwyWZY4LU18QXnM1//l23WW9eP3nJftQMx8RxydHvhRzgaE'
    'cpX4mJjfIDtHo0FnzHu8bG+n7aPjNtdyO3x0DDM6lqVGll9aL+kbR04pwZH2m49g5uwDF0fkKfRtqCzgL55PpkvGA4XanGHcDobr'
    'hVLfJoxCnQMQAphAHWM8tySLIZpPwGkgCSMKSINpAizOzLhkzFOyC6al5NMxpcNDXw9S2h1ae2nrRXwcDRaibxE34aAJwwKGDvgn'
    'iqo8mbtJmiJLVh2ba0tZN1PjhmxaqdwAlEZ8ZxXHhNztPPlEJydT7rPG1mGV/wXfrd+6hSLBj4PpHq07Rb8TidBG++6DDRtUeHQa'
    'm6L7Ed6paDy3ZYt2bcEsAqjmKIxS/vEsofJdr/wQWO4J+qY1N7b75JvVCrrbfdjyz6Gp+UTcYlAg7vzPcx9x5IWPWEOiAOHHywuM'
    'Eb/obVzZEs8nyfwJUK2SkMb4tmsGhMo03UlWtfTp1Y2pgMFWxB8sP6ZYrKEdSnBOy6uNDPlMeIb6QkQzOo29tKgmKCkZFUVjaj2D'
    'G3wqhwQ/wio2R3L55cvb48YGU6oWLnMTP7cEhkrr8/FU1XhnpCL+22H7ne8EvOSl5C/+ToAoNJPZM+MX70d4C0Mvwf/kl1TE/kEe'
    'fPwIubs4kTeUo6wVmDW58mUOFX2JA5XXl0CO6i+s6qRQGNeXS+MvUxwX5xqDIsesZt3sVSSKylPHvfEGGAWVQUh2G2jbbrYP0pu/'
    'EZWzzokKLAibkFnaSXxwVkhBoA/o0NPAocgumlkN3IYJRQONMDiGhaz1mJYelSndTfjhNCnQsq9PS4J1KNMKPo2ycfP2ZYK2iRtX'
    're7Gxj+07m/8g+jUrm6VadSGOjg4RRGyw6Kjkx8gujICZU5KVrkdWdZpJ07OMoL41wNA9aiHsI2UxSJvfHt0dNRY7pLmxoQKmHt5'
    'fzLzGb79YGTwJZ9bpIB1tcsdxhQaGpzxQbre/r/nAtLlHj+5NYB1fIz6PUSZf/m3f0f/IaSLdEhVwdgCv0sg6b0JBkLlC6pbWmJc'
    '5aoyXQs+MKIC7OR3jBqogBwYyZ4Blcd46wZnEtTUOOnauZ2tNrcN0+JZ+dxU4PuNsFFVstvKh8gvndrZ8qmVQYrcPAgrHMtuRWAp'
    'QJq67rg6msDcrzkczjrjbWnw7KIGzT9vWn3W7dz3q9R6iqqeMU8D2nCu1r/esM79sHwoZQPxCbBtCWxT3BF1BfqIm9LYmc14LGFZ'
    'dscIbLTPat0XTL85G1WVVtgeZeBUgcvD6j8B2sHWgb2fhmawREK6ZjgRQHOBNocWqyK2frDhAYNcODlq7xrEHkuHzBVfoIy8Zexc'
    '5F8s7GA4+FQZdtQX6I2X+KJ+iQV32iX+Z7PEGB86/MpbxczHBW8N9SwfmMvw9myrSHLag7986cwXF3Jtghgy2Nt/3E7Q+y4l/hi9'
    '86an/Gz4eM0Wk9k1gPr+43m6F1/IlduylC6aUVv6tkwU8Msy+3899r1w+M2KAOxkraBvFxp9ipkjZP6wa/nDDeEPoQL5ERhOE3lI'
    'upmRhTw6HY8dzz7b/nDYCo4M2JEVjRKRYVdoxqGBHQ6FsW+33rLNEQAW0kj/EKC/e1eD9Qk10g4G+AqJwtlsG0D7+Bj/7fe3N2S1'
    '6D9o6EdqKLjEcoMtLHfBcYZsQEMs093EyMZY5oLKDMrK/EBl+Cv0VNbO5j1T5oLKlLVzd0P1lSvj/WfG7PoS6x7cSLyVkbQ/ajbP'
    '4KI5QZS5ef9+WJuCi5MUI6sacDIvhonZLLS/j4/d736/BJLKhTwGnN6gISudRCTgAOo44RVqti1j6wRIJ56IbVZvaLsu7s3G0LbW'
    'ytYv3K83sfULn1B+VYs3Z63jVh8OwQlZxlgUal7j6cYabSygeqRDxN90iIE5Y2XqY5tj8W4EvQB9OaQkwvRI5ENy8IdoEqYD1Zrq'
    'sG9ctNk8hhHAqV6Hpu7APYcWodD2A2h7I0TYeCCuKhYUTRvHrg08VzPTxmahlik2g2LHptg9V+zK3e/e3W4YbnuhwDJ49wgefl6w'
    'm9/uVpSz+yWSnF36USF6yklvdsOtKikL7vN3StbSYgTHcwzNJ8tB5o4YHqqDqN+cR/2cmrV8Ov10uGBBqE1Niz7vGC9I8j9HfQkf'
    'S4Xw5aOg0R+ng8+k1JrARBtbK3bEl16cFftSHdlCyzqqUBxP29CU0u/MEdXNl+l3GAZQY7xsJtA6q72ivgWEeBz6euaCfojCavhr'
    'GSrRJW6kVlHQGuyOiSAcWwzJcvCeiUVAPhBPXr+ErmmU3m0ZU0hOGJQYEsBquofOAJY0HltdUuirRQbl4yH6lDF2UY2SC/9jvj6b'
    'pSdvSCjeBKKjUBPf1dTEm4Sr8QLsDAbxdI4ZLUZwC81mx8f9foOuiYZ5aDpdCIkeOfSTrwHBCzAac7jG7D2sIhI/6NEBb8mfA/cX'
    'fpv1qfAEYe1QcSVu5eeDOVjd9Dn2kNwqz8ZpNJdlWBEGsXobagBgaeBDPnhXQhvS/Irr+pptQdVQjMFrYTQoAtvYWHlM0s4qw4Kl'
    'bfxDg4I9ecac/ylNT/7mcyqp9cTxNo+iAempcTFZF8ev486fcTrfBVIgtxfvR3E8ppI1wbVK22sC0ozH8+gnuKWRAuh2Nu7jRd35'
    'Lbr/+b2oBv5sQo1xO56raFdxd/dawZ81QhQE/d6/lVWUpe9Mm8VKexWV9rxKlmdDC7cYw7Vh4kuMX4mnBI2c40lGefkoUelglo7H'
    'ESZiw8iSwedJep4FmDSin7DTAIdATFzMzoFtehUFe9sWV6p280pp2/mFXGMsJsX2zXIBjE8vGlulpUVbsu3WyZU2UaoRY3Dgzp1Z'
    'HCG9a65Km+cq8/OYUbnV0wTHypTA1jfzsy9Wml++9CrzkzxqAPSzhdWWTiicpZsNDyxDt2dAQGLw4M969yyrNJkikuDbwrwDbUlh'
    'GnHZyJ3OY7Da7q4yawvnMm8dSbSJeQUpnueRm3v4dYI+FoJTrjAhv+zSzVzxgsDT3p4OlEii9H7w8YXgvC5yvXxrEA57g5EK4AQU'
    'rIJKQkxJQNvgb/wy8eLuGlQ9rIkEbDLcJRfAX5Gay0vDm7VsrmlJcoQW6NGCi1KOaJP++lU6aft1g2Y+8XUYcAx3GAlADnCzJvY3'
    'IegZJd2mOJjcJDSPidICF5J4EJ3i0TsepYSRpwk8cFAFnYEI+p9TqGJ8kxGZ16mMV0w98d0QqODHSRacApGeto1RTm5hHENtllLH'
    'ycZs5GQ1KvHMJ3CZ9IJxB/+2JLL5mKI4t0xGUHwhP1smLxUuDb43EdKx2ZSb7XQ6aSv4mJwc91yAiKtQgobbeZhu/GDRmDVIzZXz'
    'AxGCMTLJEQOShAmXKTopoysgEcEfqkovo4tQt5GNkqMSieu7yTBt+lFS/UZLIgR6a23HaCL22fVHBl+K6q2ANRu3VlhXXMZAp4HA'
    'BEhubQrx0XX4d/9jqzR2ujRUHTi9NGh64STncdS7KZDdQ957kn2hcRQ/cezuXwrvnFLHjDwpal/TC9xJTJRC66xSFMzebGgRM/4U'
    'eKU8zxish19GzLJhWldCKn+cxsct/jmdmF/HyZH8Oo/704ZrMp1wKkMUHml7BJG1J6T/svaB+Jx92DjcEsBMxqUm8RjenchBXOdn'
    'UOgtvXA5N/AJuqZdwY7PVM9LUi/AuS5JvNCg1e1RAnkcFeETSvGOxoyNEMbckgVqFBuUkcoOmc/wQY3RG6E9doPI+W5LMBdFu69T'
    'GyJlUuQ5v1dGCrrNc/+Wti2gcB67w8wIxSLWQojL5Bu9yGn01CDbwTkyo5hraFFVCtNmjriUa9nshMKXkpuAbg51vjJYXsxdhmGp'
    'XWG82cwth4Gpiw37+S/4dpBNbAXZbNAD+taAJlzGwNgZxA//mJAJ57BeLgdEV+V8KGR9MB37Ja6V9WF53ofKzA+SGEhMtxtiQVXv'
    'BUCFQq+B0oQ++SWF86AqYVLAgzRCw186A2hXmc4wvizuEe4aub+RHThQHbN4KgRi8BtOsjlIZxPcZvqIBLg7ZFf6OMGeITrJbZpY'
    'x3vIAf/sZAgn796+aBKiIYrYYS6KX19Gke6O48haiP7NkaIDHB3fCAwblhwtIL3rJNEWUoFKaJTs5UDEEMKAu8cVp7YkrajJhiVD'
    'GVyDASYZbnnGS+KJByG0VzAx6dD6KBMWKCMIFH5pw7OY9rkA6SUAwffFSTSBCeNwg78RnoTHzhdYYpmSArpJhMYp5C8rz11WlVvr'
    'Bpm1qvNqleQAfeTyUZIzjuefULNbzpidId1ITLNxMlRWevzROwfJoUfbWhEDum4ME2RP0I15iPJ0zwaV3lEiC1h1W7Yc8K98Ic4j'
    'c5Qe5WJml54dbd/hHcQ8yRvUJmKrS2HKWNFpDgUB1AxK5lVNTONeIM//JprEY42J0unT8VJjbEYBRlzNm9jwGvl9NL5eIyzzVi28'
    'GVAQDQaJRx7JIgsmMPSNDhLoMsLK1x6svpF+9Egab4Q7MNEwoPmKJYf8t82du3K/R0k+/cnJWXiQIlMpc46mZf99AlezdeQloQ0n'
    'W8k59IbFVznGDg6DYZLRv7ns/Va50OOmqD3Jo3Jf47hdPrZylWMJJPprtjNkcmrZZTkpI8/uMHmWI/Y098A3BM5q0lKZoyr52ioK'
    '8Jqsay4dBxx+yQSVB4rK/ReZgz8YtMA2NICm7WA8k3QeDKkfFpFiPhiq3KjKT+VaR25qEOPQuksY/pxF26rMf3izJUQnC57S+SgZ'
    'jIjTYNSQZMYZB6aZEW4FNNAU7e7RLD0J3uy3ObrJfBZlo4CTHIXFbdlxE/B5eIYGf35/rZ2pzDL2xVuWfMUtWnL7q2XgY8irMGzY'
    '3WWEyeLAZIyYOz0yCYhkcyW/EW97M17EspMoShX/xbCIg9WmIibW+/plVHcByZccgcsgd6J7RshwZRw70GYLkK5PFxHY4uwlnd4U'
    'r2lDLfnqaDU/o5meDuZfb5r+dbodQOOi1q67apgCuBEBsOTSnborN/AF31VZ9dR60Qfkc99NcRgXS0lyIiUxj27pSfGgIXd2heY9'
    'j6Yqk+I/7htpCHz+oC/Plr5K73QPMSXLB/+VV+TwsOqsJ3wXqv6FTVZGLplLV0cRsETLIaoQzhVkfGCjDOn2GexXGg1F3ZGnFRIy'
    'H8m/bcKowyAaI5+/wBRiJA+l5YCxdBS/snMzwsRUf3zd6k1apFAxQDtIk0FLKueu3bvnTzKTudDk3x1F8+D9zn4AM8QbaJKekxZ9'
    'gtn/AK/iapwBVm7DPZVFHRabnu10kiGJdqtHJBLWs8c1RZMtM0KS2ODYm+fcL46DFn3n2cHTt7Qy/OlOVz6Gagdw701TI2C68TYl'
    'tmkb8fAp3KCAhRG3TiWHEKdu+XM7nQ2prINsUrd28nmsb6hOzynUeWd2OpSTYY5xV4glLSjcaR44ZdmQtXF6Hs/WDC+YhC1aK/i6'
    'xrN1n2DJXBO4MjTDXkAtyKJY1fdRMsPI596K2Y9jim8+jdAVfyirZ9p2Ov5kAudt/jhGd3cAvsc0MtHGob4AZ9GnrzRkAD4ZOTeo'
    'ksiiPdcYvnOKUXuBJBOO1JjMA5b9Dy0MMgnvELqPZCrZqopiPSMWRZitaXqlhgvNepE0VNy+XoB27yYdK4KL3QAEkgZgrbMoIROX'
    '5bnYSwkdGxuD9POlFE+BqEEZyRC1pefRbNiovnww1991rp8fc9k4y+6a6sukXbxM2te4TNq/7GXyK94A7fobYCm+bl8PX//aeHHH'
    '4EVGak2AAsKIFl8KQgOgXIavdqieh692HL56rNDTEoTTXg3htH8dhPPXxBqI1RTa8GTb+9GZMcn7G7W9wSQnz3CAxoboxqGItHkO'
    'm8TYVOPAEBasUEoEw/TcQkrHEwiPK1OH+3Gqbioks/2goKygfBkPOvPUaLoaVnPf0FGjLNPwbIxhnCeUE090q5zx+vSkP4FrzbnJ'
    'jaM62wIt5seiomPeVurrLf5gDdScNriQfB7LlXqWlznOky9vmbeyG0dLdx1uXWszmU01Ascy84Sbb6PZRBw8AglbDIwHNgGj3Srx'
    'NEojiqqQ9Tv0E0YPNKGJiJVwFhuYGn2U7NXYB9cDHE4/OnS+iTVPUOQvky375gEWrWEdaJW2YA2Fqo22bma29WWGWznTLfvAZyR0'
    'mBXxzT5SQDS7gxR/W7sOCnClsZFFLoyQXUXegzxapqqctylPxM0wQX023833kEt3jSIRS0ZUjiZQYHulLa2BwTh5mQ6XClAAeAfx'
    'uC01PFNr20ToNViQ3zeOxvFFQXvxT3E8xdGiF6MXNOCvOzZRHeQk6Ek2gE3bJa7GKda9IddBgW6tUAbwzsDLXY7PeEbzu1oJCGUb'
    'e417kDS52tt26VJj5+2YareptFvrE17kk9rV9Q0H0XTAGRe6F0bKJ5rmcu37GAU8754Hf1u0SYEK06JRHPEq9wQWVC6L+OgJSdFd'
    'TcfIbDScsTp2b+7xBMeDQqEY88pORSyIyGfCcgViod7s4/jQlwX1gvkIPKWKqYCklBicp9324xlWKtWteiNjGTKxe3JZFXUd1vkZ'
    '8P+LPml3Lw091ms8EWqqxRi8xzZG+TDbZAbda+xzNM+rD44m43iHphXJFSnDm8cnNUTOMDmz3BGUZPfBV4jBNTuGn5htM5N9FDRE'
    'o0BqSq8N4+CXOE6cHWzQHCmYAa+EBqasbOL13YLxodiBIjCSrSbqJwbp+PRkEqD5dHoKd2Sb7JlcP8XYUVQgHzeqNoIjzw96Qw/U'
    'hrjSaZsToTBDWVTqWIPqJ+njx2/a7eDpAuMjKS2MTKHdfmiKwYIHtMjba/nu14J0QjPATzntyO3L5KrFsbPCtYBCpm6vFbQ+aw+t'
    'wdqP2dlxaUcYlPb2pUcB4m7SNgYSbvlq7Zbnyo8xCB+nF9trG8FG0H0A/1uj4Jzba4gG1yR52PaaaJvIE9G8bRO5ur3W7dy3rxBt'
    'D6Lp9hqZJKhRB0FuaN44YJg/xhzOPhjAaH5YCwYL+jODp/vYwQye78KP9Yc/cmD8fEEcyA9m9GXjlTmtP2x4ffeu1TdlsL7owvNa'
    'sIA/Xfh7scl/F5v42m//yu3bOmychZZ1AJeHtzSIHRg2ZhlQEb/TRg81DRXGz2nIJbkQAtdaeQNrgWzf3c21gJmN7bXNe2sPf1zn'
    'pmqGSmjkDmceXzJYJJLNERj2x/YUAPqHL3wWvSOgplTV3trD25dxNtibn4yFfcW34ZWMtLY+jrndj4bH1Iogbb+mevgkyIHusWiK'
    'Mcl3R8l42ERsIRgEEOJBchJjpH/WYbLImaZGe9pECfu9jdBzwbM2X23f5gvNSLVC117JcvMsVtFYapOlr2Gx9MUGS9tq+L7Nkn1f'
    'KZYqlrie7dJXsVvS4OrsU1YxTAGi4pESr1BAZKGclbRNOMIsPYmb8IBgBH/y9cLQSeBK7rIjorb3xdYDaYtmDUM1YVpgOktPpnBn'
    '8gwZ6HoNXwzO58tMjcrBDMjNYD5LTpqhOHz7FdC21hXZKhH7FWJ3Kz00xqpKape5VG2d84/3dAvXalIrI3xoKDnfinQm5LrsxDB2'
    'zovrv8QO7RvuF6OEoJAm7yPFsioqsyQMIpdhiRi0dneT4yHya5GHwfvNeyKVfE+xEPvHpAm2KeLnhrBHEh5N5FkRsjSeZFV4wnKh'
    'U0WQP3ZN340o90BT5Euw9Wh5YgM+XENItZqEisVThVedQWSSL0jQhxohDczDTWQ6A6r5AAnCN3nvqQH60T4d1yR06FCRNtJ3nMeB'
    'n5E8uH3JKPUg6j8f2pQOLrj1E8sLm24emV85bpldBJfETeHuaTJtJtR1+hObRoMDp6icAoVqDaWV4uEg2ikf2bYxtdyyBQzzwstK'
    'LWIxyj7CUazsJDCeTC7DgRrNSTpEDq5BDevjg+b7E8ryoT2m/FbrpkkNK2mrm6Vid/QO4VWJOxBWroIq7Ty/uOgqC76lVFbAgQ7T'
    'c6mWY8+iI2DvqCpmqfr/yXu75jaSJEHwXb8ixa4uIIsACFCiSgJEcSiKqmI3S5SJVFX3UGwpASTJLAJIdCYgkmJhrR/O5vH2bOb2'
    '1vZs1uae5p7uedfO7O5h7p/UH9j5Cedf8ZUfAFil6uquVnVLicwID48IDw93Dw93HgZzZ0Vq5rW60mpSgz5l4tfQO8tUeevVDB+Z'
    '/p9mlvVdrg7MzV7EyphAUbGQ4IJBmADnfBHTtWXGAqU2QqxRoY2OmK99hT3tLjrbNMDqwEADE+p+gr6Zlscf6NKkhKhJBr57SQ44'
    'eP2ILlJHIC3iyDJKfHHaLO/DrlnggtaWPJQsbzl9IZsfxckw/UZUldGbTDQ75yBPhJWU25Y9H1AZhWEftJMJw4pGXqC+9QEesOuO'
    't3N46N3l21cBVMVUndDLOEzRgIBEm2AEB7f3bVTpZP64D35xXwxDkO6IhW5v9C0bK0b9FDh16P3dGC+BJdMB3SlAtJdJ/vyDM4eK'
    'LIajs69xkC2nESeRju9PUqBGs6IisiG2aistpa1x/7SOBevmehqxElXXN2BUACsqVAg8Y2eiYa64xeXQ321Wi49OXxVzM3VdmfxY'
    'uFbl74ZhPwqErG4q6mCk4smM3VBMl7a3fd+aTENOHYx8fRaNMJrN5xsRrk4bRiPt1gUMiT6kVvw6U/+qLt+Q6OxvNiTrD0tLbS+Y'
    'AntwQEWjuvrYXAJQN76q8/2nNjyjC1YdXjkgc71h7lU/g0WDgR/hnzrorGMMglBn41XaxtuMMJnVe7XWaeKXwZuxPeOk8W0cjaqV'
    'N5IhyXEJKJu+zLTl52ruDAEWSmfR5HceYqxoSxU3VExLGz4NrikxI4Y6B6b1Um0it97gDZ+r2AebH3Ob53Ia3W1k2xbCXsnCVOFe'
    'iN1n2THGxpggAw65QbNTIJ81ua26ylnG3RWMUFHCSJ3inT+zbFAoHBjpILxCajLiwctnz/9yJARGLiMi8CaPWlIAqwJzusjhVpx4'
    'ZwghCUjnUhIGB+azpAW6LYE0JfoYbF4hXlvOCEq0O6NkIG7HQP0c9UqUM6I0WpfIybNCVpFqcthLovHkAJqXIWbFGBd//yt0iLJE'
    '45TK0q26eUoLF6uTW7+knwu6t1Ra7Ka27F9/KcqLhRJSSzmGlhJjF1qsyHxMHkgN/1RazkL2lx+vharQvPEsUIfs4n9dKlFmOSK9'
    'zlmHH5EmgsHgZyOIn3nIjeIAO4u3SwydOXLvPI56infn/ACBv3NhqEZeHc6utNCbASVp3j1KfBluyrwZ2I+FDK2ue8dPhMhwkcsK'
    '3mnD2xF4wsHuGehnixsRbEDRiJUdkJgxu8rkuiFjjM6NKNQMwwBjcvXRvBhPJwhNolsyjH6YXqD/gNY76cbYMLhAALDBhtBPjIM8'
    'wD11gAEPT09D1KoREh6pjbFgP+xFKdkSAbtzznOX1qAw6KRnU84GH42mhCu8x3PsKYyb+t4wQ02+sDsBdB9zqhAl7xPm2biPJF5Y'
    '7+Se5LF1noOS9cEpRd/lUA7oOSbPW3x0jTZ/b2vL029taXwLD4N9ZY43W3OYAN6w72M6F3TJpH+0v5v4t8FLkzUYTyXQLyGgToqm'
    'QB4NgmQVy4vzGsoV+zyGAqco9zTpiZJSkE6RK1R95gYDiSlmFA4KvN3GmHMNnGAzmI0e6gQwoWaTHpEDuO0liW8KkRDxg5s3ew03'
    'LFHP7NEiSCoCjRWIoLQBJJO6IhM6wi1rx0Rb4glwq2rlLDO8pQ2XDK+yCIo6aI0oQcrLQ+20F8PkP/EahA+7VpAjozhEbNpH/s4M'
    '4ee5EN3RJ6DOaPsassZ9douxH8JWWMdNpXTI1VC/xaLKR0dRNE01UX31q4NXu37lVo2/j5IJDhjNQxck8CWw4GIKjcrtGqSGRtNh'
    'HZS+4XhxY6p8cbdv0zI+9ZccaCr745s0O4dZXKCbnSEPXIiEWVNz0dDMSDgzw6ItjS/vaJ7fj/VWnwl516PTHG/RBgsF6+QIVMHM'
    'x+chXTBE9u3eJYZirIItA0/J8QagDc8VCLS6qzH+9FPvrm5OjaflGswrmnZgTjiN5FQT2Zo2SAq3WSk4jpZkjsCaBpjnRW3gLGR4'
    '8RB3/W4SXwIr8F6/2l+TlLQBBfHE+6SgvIYRXquSOGocIlQ5UYD+2PCeSn1lk8a87yJzoO0JbdencoOuIX0X2e/t4fO3Lw9eHWVS'
    'IVtRn2HAkTmlOsh01VJULS3GGr5C+dw52mO4O/iIft4FIEUkwKD/+LfYMdgn8Ik4s7E1o6wu8ll0bS3aRreK8h84/Bk54fEJc+mM'
    'xHALmUFJDWOYTJTH+zxE++L8y2KESCw129s9JxOYxbC1nNDVFtkKUEiuNYew41KgnRulQVgY3//pX4E9bDSbzUwAxSRMx/CAclNw'
    'GWBg8dPtcfQ8nIDgUVkLxtGaSMuwDgGC2dWHIUi4fWA/Lw8Oj6ztXCi7DRJ9RQS3+hGMXQWKogoHPcLxW/s2hUH0ZqYiqllt7zeH'
    'By8wCRvgHZ1eW1KExwuzzfQlaeEx63vQ3TK/Kq9H9Ny3MJITQ/sFkY7zgoY3/+ZrnFeM7tCyv4FkNgyQ0WLb/AMbZ0J9rn9jqM+h'
    'gwj5DB3BLBfDZVPyyyTGkHlt5GqjEH7hAc/X6A1UpQadUjU2GjhQRr3BtB/S4mtrpl1QgumtbUjPlJlZECfsHPYVzOl9pKCs7GKR'
    '0nQw0YSkKKuBM111rlJxya1GfOFbFGWRLuqmTHeSyAPXiGKiincCUz6N4wn6S1ecAI3mypBxX5yco3cvBgrdTZI40SiE+IsmC9s0'
    'WlcQDcK+NpZ4PczwAcoKlvYLFts7p/Z0pG8pt71PbqhWYwi7A2wqs4Z3MA5HuC6VcRu378a7mvfALM+Zyvqj2Po3xM7ZkqCn1Mxc'
    'xp6ydDWtui3i7nhUNyRFRJvUOqaq3mQtMG7pOs4i+3BQRS0TlW3Rqrqp4nqOeG4ws4/jPfKTW3lpUX4dpcY3ZUtsDcZVuqDGwdjL'
    '1xBvwoLiz9JxvnjfmA2ts3TqCZe3Ol9Q589sY7bJIuNGsrTDTHZgsYwc9edKmavGlZbOTLGE3w3nf4ahRK8xGnxabMSuU+0AY18Y'
    'Mhs9dK3ANPxxzenZ08elDKT4z5/FLWiu248mZbL7zJ1WZ2kVFrfiHFmLSorOJIs393PuLBZY9BfZ680a4+bc0fvpl9Of1+ac8yZ3'
    'jdA1b502OWe3WrR8LB2UDvks3uay5orw/bEOFU5qIP60XUqXmmmsVDA7Etddz4fEgXdDr6sMopIwkmMe80sUNRwjpuBIX4suPMNI'
    'zo80b12U4rLuVSkZEaILaqRi63S6eM4IgrVIllbZUn0HvEnkZjcgWn8mI+KiZthafpt2uMatG+oCo8QD5+UaodK3bqOfwNq4TV+o'
    'gtPM4jrUaG+SmfdcNjG2jqig2xzsY7v/bdCDEpp+aCmD6AoLmeH4JnYuLYIMHhYppXU6i8/epl64vj72gs6gqXIYFmNaurQb+aWS'
    't8KTDU+5smTdClh01qd/jvUsHKE+MDf15uWwLqUsO5d7fuLNj+ELEPiixZbFbp692n5+ZInQlGSJ4OjUrfMAss+dDfDBffeGjJMl'
    'bxE4Ke5CXG+Kh9Ll8BCdfBpmtOSpY300A4FP9hfTNXyyvxgstdxsvBdBi1wwquh6NE3rWNLQIf7yqXZm6SnsYb8/eEGOK5eKJpRd'
    'T/v60PXGg+fPtWMne/+T6ADqiyOuL0BSqlgOkkn4XjsoJhi630FTjZ58ZOHlFD4fcg5GHVEUBxP00/u+kwvLqqRGF2VE9UzBJDFt'
    '8vPoKuxX10UKthlF2Zm+OVHM0IO96MmDjBIgB6NrHq54mnqE0LyUq28vh29pjb8V188txzUtS9TVLAUV9ktW1gcVatohSDNospCZ'
    'fG3gRNJmsfo68fjamzdrZ7XKG/hjv63AyxV4tWK3Tp6u3nK+rqnycxVMcsMiQ/wa9qNT7Kin8kag6QI3kETi4J2LqxYWQWaOJIiE'
    'rRspcogtdoetiBmwze7f6vWKShQIEGCxrODVzSu86LZS6azomp7GsM0YdyrWt0k8bnsbzV87Lwfh6ST/lm4BoVmvzY/oclqtQ6ma'
    'h38DDcYTenVvox+e+U5dXD11dg7F+01AEDD5+RKX4jz7qNns2J2kj6fBMBpct9F+Ok0iGAdYFUPWy0ZxClQYOr1W2VGoQUWk2VYp'
    'qW7b+1UrwP+cT5Ryvk5w8QAWD3Wd7+OYLr/X2UuBnYedAh/qFCsRegN/rC/KBZcdcLPut+UOsak4w7oBWkr9auZncp672u0WYkBA'
    'w/8BniWaw/9gDxdzsXZC1+etLJ3dZcUGfcGo60MtfVa2md1YO9rNypJWOjknm59yQJbxtFG+Skncn6rbcbARY8JTcVFSm2Pcp/5R'
    '9Ao0kuCVMyBWimtSozd0yqXfpOH4ELiYfoP6ruk8TwA2W70IJTiMbuMYXmHkxbvuGytH/WQ090gTqtHtR6hlOPrxdv3vT4Cre3QA'
    'VqECQ9hl9jGq3w6oIiBumht8k5GPzVhCL6Os82rXMviyeIV14ZdcxlCDomOluTadPGzCHA9P8KS9Gyap3UxDw3PsXbo5PeK3aw6q'
    '1VOuZzemoRU3pkmgkj/tdTGmUiip/fu//K//6PEvfC8JlCynrtMk/hCOSF6Dsv8kZacjLl0x8o0h3INhNPEIzxLHOuQ6WIjK5BfZ'
    '7Q5ql4t9g0fSPKJF0W/oBm7Oj8s2kYd87GpcluYftYqB/Hocbq5Q5ZUTyS5bFFtH2dewkaxfuolk4NSiMAnERjZXeJt7HyTVOilC'
    '9Xt+x2zJrXvjq84YlFj0NXoIzytP0Medpkd5ycEWPB31GxxDQdtPBSEdvo5+u+Hr5BAsvlzOVAMFVV6eNCW3N4xdKJfCcEvoBIPo'
    'bEQBbtI2ylth0jkLxu1W0+rEg/GVhx2RSzUJ9GGatjfgDWf7acvm3amYVuPREOTkUI7p2UhnsMFTozM6pyRzOY1kOk1OgUet+wVQ'
    'ppTNZT6UihuVCOl9QpsSDWOhLSXmMvZoFca2AbFlpCbfmugWjkABLeDFJb4Dtb5O8//JTbTamsF0I6AnhVBhLtotm4qwpi2oZeU0'
    'I6ZlUfA70J7q/xbFRKj3w16ccA4B4qx4Ujk9O+8osa7Z2OhU2pXKDJHlAbMEajEksl9XOBxjHA4s41dmmT5JTgWJJwLicB32j5WC'
    'sbPp657QlxUAiJmz5lnVyXmU1jwMgeLTcOrpBZYqN3xYxYXXiBTj8eRdpzgwCcy0ZX9ahomJdLFUCLws8jAENR4wzCrwgxlvsfPr'
    'T8E0LXhq/aTHqgMm2wPTQA6PeWtPbbrOykMRw1Xf5s9vx1wHWjvH264qxis767BahxQjXZiOJtHAGyH7oxdy0kzHr4wgfpOZP+RU'
    '4GTVOcfkpngYghmXBq6Xzl2SNrC23vwLjmacjpDQSeHClBmW3JRLWscdAQXb1yMKJsl2g6KdnAMpJ+EpCKznROv5MIVYx974fxTJ'
    'FwnPz9C1+5ly/c4KIEH/PUZ0xEKqDHstWYsBVUJxrLZilBX5Atvn9IOSKuRzqymVYLPMMTAEa4NB117XzQvrLPbt1agBjDTj8dvJ'
    'NLAn6RGkuQYptAen6PVrlZUUvjm/MGW52zkPEmANGNp4ivkEBiAM6BDqsA/HxsMehEf02j8PJ+jilYpPHxARTkowYHjoHYj34ruh'
    'SYAUXqEPVYQQdex14tVe4FFUy77XHQSjC8ZSRtmE4ekpFCvkPKXfj210Kq63oL42QOOTs9CXsC1VS3EuxkTDgnWrn3HBGpojzUCN'
    '0ymsBiv/KulKO4DrZHuyO+prcLqAfX42s/wzn0ejSMIQoNHHS8dh2DtXsc2H8XscwQnnAuFLFlgkuABOrUN2WIRiS6Qi+KFBxxCA'
    'JqXj1snWskOmJ8cdMxe0GST3/aKhykBZNGBHzkDgWMktF9ipOYVTlIojHDkZTkfRpOHt8MWSkAIkMKARlhnIKbm++qF2Asz7FQMr'
    'p6srGBGakw2DDIi7RyCj2JB9Admx3PIgHlDMnomvqKJby1+UsKDDkqL7EdZGXzOun+xzZyZIVfQZK+qbeWnrp6ak26Q7edmpy4Cy'
    'txA+03O4txPmFqCGfWnRcQ6liJeS6UXmRvKfwJsRJXtI3a0je+33YwpKTCrb7jUkzouCvthRgiSXRsPpYBKMQjLzE1GCTua9IIoJ'
    'Bshtg1EM6CcMTmgKl3U3lJEC9kiMOIywHEJF/2zF9lXsMzNsC/a7Aldyi9OogCdur4TnKK7NGFfKAwxbyDCXFoontpm5hVXk1B6o'
    '+SU3Z7d1B7MS73ZHBlio2dIKcBwQCsZNF1S7KJb5hlsQ/yv67DoqJcAo8PomKpZjqzW3VJBEQX0QdMMBln2W7aBwt8tYgkhQyAFb'
    'GkiX6SWWm9dL/G66Yes3+MUOxjC8QBSF7dBGnbMpsHv6MkYFcztNoWUzOquMIy9veizE5L7SKMLno9+/3H27v/10d//w2AT1teGJ'
    'mI/h+wLOYmr7x1ERWLCDAdmjraRynifqb2gc57d7PeA94tzFsqhtPxifk41X75Wgfn+5/Wp7B/Nivdj+ardi7jm2K4p3NRoNtB7a'
    'Qk67UmV+jjehCjpPTBj2pj6xtvG56XlmtPLOUbRkMdgvTWU8wl49JwZPvfHnVmbPEVX5Rqrv4VsZjIzuoR2xSwBehNf9+HJkgg8z'
    'xN/ya4wpaGOlbgfBK/ECs0h1h4T6KtFFjkxZ4l+CSlGIzK8dFMzN94Urv6iYs/QZSedmClKOWW9VSxh2KSzIlMsIxx1HNs6UzTJT'
    'xNJZ/+d+J/dyHBS87EfulBxDgRp0AukYafwkOz/Hgx0sMdjBfOsvoQzIBCeEHrzHjQnDkItUa6tqxwnVS7BegvUSp96hIw5b/M9G'
    'Fpsu/pLwF7XDs3Ki1RnibbDPB5693jgrSujBxpdUUrYPiORYk4x9DI/2L3KK9eQgBWN04V4/CQOSU3vqFkyADheTJPDYSgZzGpwB'
    'cz73gm78PpT8hy8lx5VH9lbBj69psfzAl7RNq1qOHWKGwCkm12tYF9ywSsTrDcPemq1cCUNv+0I5XwZkBa46dbR84bwVARO3lnwg'
    'I7ekDMo3IO1Y5WUyMLUCi/R0jb2C5x5nSOIyPSxfenQ5EA9/8bT/m7D7dRReSqZECdgmuSOxd0qHgiXZpevjZHTkUSJJi+TOc8oh'
    'C/NMslJIgpc1OKhj75zTGcHOuS0a8ykFvCuS6QUAOd3ZLHfnnOrmDDaWpOSaSJSkaFI2iTpwFD+Lh4rQ+HiIRowzMHJct6hIJrfN'
    'MS/CS2+bcq2CaE9PWZMM14dy8LH60xklofyLKUbgf9uLpyPMN4tZN1SOUV1mf0npQ4rOFz9UoYz8URmFl3X0ZywqUySF6AqWKJKt'
    '527gFZAQvD2n4DyhRZVxpBZJkmG+ZmKFYRN4bPt2Er+Kh8GoykPsDM9tpAWp4y8AME9iUCBKhIZyoIulBgs7oTZFUZuUKVsnd6SR'
    'b4OGdhlcp95ZjAwVeS4yleR6cs4BHj3LOO6kpZN2atZ30lRpe/GLsklSg3urbWlLmxqUPiacgjefKuw1YtNgavWt7T0Y9c7jxGXd'
    'SHEGFcwLKouBEDJWAan76acCJZvPz1bdVBHm7GbSZsYp+MZq1N5f3cLE2zXx9kBwGuyBvos8u3oDyt958D5CR6BKOoxB8YTppX0M'
    'X0wCdEZ06cLivewtQtbtF3z4n+M481hs2dpATyXkr+q4newOu7j7khTgHM5m/YyZTICN/jSMcj6nVCKN4uIOebOcgOSNF8cnsGu4'
    'Wc+VSi4syHIS7i/Lb6XofH6rCmX5LbzX/DZbppDfqgoWv83Wy/Db3RfPvIPnuBad0vOYripTzHTV1wzTNe2U8l5V8za8V+r4CwDM'
    '470KRAnvLQe6mPda2IlgTRyBTF1Eb3e8EnahkVIV+30QvvFirEjm9oLTgptKk02SOIysR9yC0hZzZfT8ZIBVEyKkLsYmKCX7NcXI'
    'ZekvNZ6jHpX2rWiyV3yMtsw60IXnrwRTLLsW+KSwuEzhWuAK1krI18ushb0XR4213d8dNbz9g53to72DF17de7b9+0zteWvDlCo0'
    'pJjPtyFyXcv3FwGZR+gGTAmpzwO8mNgzWBbTtYXDHZuV3GYLxEswOYytLXDe/rbLIgTuBEtsc2rJwB6Hdus0f4PGEsk/7r7mNa0g'
    'MD/EH0GWMp5RiYdWBnfV9ZHjLkrG3ePjVrNW+V3lpHb8qFbZo4eNWuVr/Pc+vKCHFjxUOHU1Hvok2oWIsqWJzeJ9LT3BAQe4vnIH'
    'GGGqNLzwAHVWN7204428Orxh0Ui6nGSOxw8dhvftdDgW9RcaE80M/0CF/fAs6F3DpEfDOw4EE6O0DzUn+UN2SYf4jL5m01TCbP3Y'
    'hA4c19W54ph2uTV9IfidFXKV/m5/ciNwZu/m+tqk3Tr0S93ty+6/3Iw1CJVlgA3TsxyodwLq+z/9s6BGaVhm3//pv24thWE67ebx'
    '24NtiuPcgsqSTC7j5AJUCc5pwZYd3vKAzC9S7zIaDPC0aIyuyyMAMbgW3/N+Y6mOyVSjc1XZWC0DJ6Qo15JjcynXpn6GuJ7+EAqT'
    'C6tIaD5RmnohYOZQnA4CEg9gsPb6Ogh8RDqRbi3T8gAVHkPdeKZlYJiQs5mIxoSbVU4dfuWKWW2JN+kTr0n5AuT1ca5A3WudICom'
    'vu5sUWZajvxBjZqE4EV4mzSjmYS1KheXdXqX5Sr9SqGy+yL2MNybJ6OLu8tZTGnHURoUPUNukv3IbA5umoIbFV8748OrXufvY4pr'
    'utZr08to0jvnvI20PTvReheMBu+jTuctF2xiz//pf/nz/w8b9o6+3P1q16s+2371Ww/2jb0vvjzyfz6MTBTXcHJ0DpNcRXt1mHE3'
    'Uw9CBkVBIqhahTwEJJ0WSGByfw1fUZol+Ndk/hj1ccbEGMxl2CScelX4dLFGcUwp8pk/jykCN6335SoJR5Urv/cgqFAueAri11kE'
    'mZC4JWiqw7Ap/hbeGQgGwhVw8PYm4RAI+jQ7aiqaEEi7N/adn6DVwlMJDD0Dqwy9CS3nLRB03mIBLPl6jzFQ01rx7W98i8eKrs84'
    'w/AP4qB/p6pqOXLl2/fBIOoTbVCyYB64mnSyVjmHf+nOeQKLEX6n4TgK8N/4dFLv4kVp6/bLWxKQj4QgnGE5yw0Ley5Tc5afHZpa'
    'LJQaErAqrVqwfeDidlNtC8wPImocOJ/sOj8r78BIUntfYcw+0Bm297znB6++2j462nvxxc+K18/S8E82yAfPn+/vvdilwT4CxdyD'
    '/6MPwcEr7/067Syv4u4UhaVoFCToUx+M8OIrVYYdd+fZixpuPtsv9+hfumQxAsXfeznF7UhClZHP6tMphmjGFc1u/mmDoIBkBYzz'
    '7LpNwL3t/X2vez3BbBiweQ5T5ZsFGGLArlO8hEoXnengDfZkAtKLh2QxDfvit0VHnD2JFcBNxknKUaTDoHeODlWNX9Z8OhnL/3r/'
    'x0RxtPvSa7W9XZnGALQRJggmjgAJSqZTqENI9Bc0Cs9BHZG1EP5xGo56dKr6GtbYQ1pQNaXKk5c2xgGst35JRIAspP6bQzp4P0/i'
    'Ebo7Ptt9vr99tLv2YRB1yWeK132cUI1Xz3e81qONFoicXA7tTfKy6VWpknhD+kxnFmjkdh/CJPYoDHCNnzUHe7mX1sgJnR1zz4PR'
    'WeMXNNh/kzQDe9zHJhshFId2+iGaZ2H9RmH6i6EZY+aUTbmaJj2WpdFYCT9e4oXIprJedtHrxX4xeopv5AUMygHH9+qylEDqO44f'
    'uhNx8r4a7QJJSHkeenRuQjcEvXdQ551qZnpKYTzQsGw4ZZUjuARXiKSyb3zmPah5D1uP1n0d2TOeThTWjNQXeI81zmE2nKKyl3LL'
    '+moLWmbVqCDulCHPt/IVEPhV6o73eBMBCi5uvLNs0Sfexvr99YcPMU12Nn5rZY9Hv62wnMSxN0Bbp1d9stH86qmPchk6P5MkxHuo'
    '67o36s4ZL4MjjNd6zbPxWvUebGzce6A8JkddVCuoRjrt0g6N2X+xhiqCswNtdbX3lRXXIugjQShjub7axmTy2Bu5KYOIvp5semY+'
    '543NdBRejdnRbvfguYmS22USrNK/3xHUY4S8unriPX7MJOr73pMnT5hMqZuE0Oqm99DOICTx7tDYh58/9arVFoHw0Y6mui9rgNtD'
    'qCMHOIOuwwg5Do/v88NFkbGfhb0q9z117+DAxO2HGHpBvjaSsD/thdVqUPO6dLak55fe1DSGXP/ocO/vdxFR6gJDs7+n1yCXq1W2'
    'N5q0HjDVUD2fcj9X6y5IwCQtWphchZabOdyZjmhaBPq9dS4qvVrVyFrHIAM8AtFjgQQyQAOnL8COByerqw7N95aAjxyhpziUNIfv'
    '0NW11YF/YA3L4HjR6irF8cTZ7QEMaTeqt058HEQoP+odkztpTxLKWhBhQKkdenisp01OlfAtgXfCTA/M/B5DgRM7sPRA3cySBDeh'
    '+khd4ojCgI4ZFTlhoshamtKdDjepw95Ad5ULV/Ef7J+P64dAf4oDyK0AbdNQzRzM00k4VsQ1yDX2rYcW7fcdeHjMlIiPeIwF1cja'
    'CtR3/C2OJDx1iLL450A1NLNXD1eoUbmaWhqz/JICweDweliFf0o4EHxpcPUCVvTY4UQmmPcP4TB5HpOxdqu8kSCN4r1HvLxD0Tdx'
    'a2ImKG4KojLhNeOLCMSXvrpXNojjMQ45/jABzkv55xivZWK4GeUhZvRtD41HhqPOcjwx6l/luKI9lPUM8+G1gCVooiO5zm3I3pPP'
    'NPHmM00FLZ8m2tL0EijvVTfoe1/Cpj7EIAfXw26sfdrzjHpQzKgHDqNGenTuWmK4MNUCuTKkXlULm//2f95rrDceGHeP53u/e7u/'
    'd/R2f/fFYZ5TggDg68NftSo9tS5b9+/LyrShMMN5mKvGpaHa+saD0mqPctW4NFZ72Cyt9nm+2sOmqvZwPpJmHJ7tHZYNxL112WI2'
    '/E527HDS9N5oN+LnwWeL6ibta0n7aBTb9I6bNfe/lvy3Lv/dk//uy38b8l/TMgjvP93G7hzfo+8Pap/XHtYe1VoADCDdq7U2aq3P'
    'a61HtfV7tfXPa/datXsbtfv3ahut2saj2gMofc9OXsB/HgEArAilWw8AxqON2jpUXt94aDX8LNMJhbhCeIPQQYQQJUSK0WLM4H/r'
    '9D8Af8+GKt1pESSE8jnWu4e9WN+o3YN3gPZG7RF0ah0+PIJubUC/HkJzUOrzB4/y3Wk1oWZr4x5AaELte83PAUoTIDxo3d+oPUQY'
    'rfX1h4+wswBn/f7G559zEjHLGZKW91P0ZakOoglML94SSfEhw9nRaSi7rWr2g5sBV3dyNjCLgZVgc3mS9ltW8gUQdI9R8EU2v6n4'
    'QiYLErW0uZmFRT5gpWxf3YTj2J4AoQ71P+9kv8MWB9+R4I4HsLxWjXyNBI3v/GydfqQ4K22DMmD5UhRUCef+uO9CRirDd1YdGhdA'
    'xnqFTIHMdpusS9QJpPlOVz3x++PFzBsPd+taIbSTX2AQgnh8Tdazeve6Tla0Saxy5A6uxfmO0tEPJFtgNZmO6kYhO03vWIlO8pKQ'
    'FvvcycZf2AH4ld8U80rPs+sRk6orwp8D6XkkCcnobqBNQk+1FJLZcAu1nCK9AWkCugjFLr1vF9k5ePXMo4X8gBjQQ+AQD2ktP0AW'
    'sIEc4D4yAFz/sNZb95GBbDi7cm+wH47SPK9uPfILhGcZQcJNxpABHCMusB+c2Bjfcy+vDYAsbdbNNV0VIhiU4EPDusoDZ0n5kRF7'
    'hTUQfnbhLJswS4UwsnkE/amiyNiClU15pLl3kbADIxAbZsC3BR5wMgD2IBnbo7CO83avYymaGiroGN99B2OqxzjZbHaSxwCgk+DY'
    '2s1vvi9v/HNsPEKx0xp7btWp4v7JVvmcaLDlyuIOU9ZTJ4g55gIcdB800vJCXMLc4CKzz2k0oiiMTSsqzl1+q6ZOykicV42vK312'
    'xRvWGncjXnZ1nJCmoQc64I8TccTg0wmMWMbnUD3kQsBjusEkGrpWB5gxxwaWY99KVzhxFIcWKQ4gC7KNDYZ+3a094hV/69rYQ2TW'
    'IKY3r07hj09eSNXqf0CIvnk9jy3TWXu/zpcCxXA0jNIhnvQbBp3bF8hoFE7IPKcnGjGsCZ4IyxdjkqrEtqhN5sSqOwNlqrB2WjNv'
    'LUt1s0lSRMWaFg79OUDWrdAjDgd36tzcWaRVyR3LvlyhJPj3KpnMR6JaFFrVXA/OX8ip33obYwKlfKanwmaJImsOcmEvR3dOMmqu'
    '6oDHBOWbOLkgj/wkuKT1CEqX2QJ8YpNBrzdNgt71L84aT6HnxdPykAbtKY5AlcaB6ZZko9F7usQbe5xjjgYF65Ic5I56iqfs3vbh'
    'zt5ePQ1OQ98NxL/JY3wU7+P94pa0ZMVaw8CNnOwXm77BSjXvquZd1zwVY13z8QnaCoC8KeI4/HuKNVvryj4/GMr3wfCaOShApNtr'
    'wGCSCM9Ao7NoJKWj0dMjc3HGYB1fsGxAD9C6M1xVjk9o7mCogtocd+dOsTijrYB20pKxrn4cnYiMwu5+GCDekioCoPjK06NK20jC'
    'jL4JEUHc5IobnEj/ZUQ6ekSK9QgGv1sAXl8rytUSI6UkEH16ZFsTF/TjaFhpW0oLpQuBEQLpxsFKi2tkGJ7C2MtI1R+coAiQe72R'
    'V1t6uUL3sW4/9/pevm6YK7SOdU9zr1t2XR6Q9EXwAi9qULo2+nHq22qcTFUoU3WqpipUU3XascqitSgeSUoKUEeS+Coa6mi7Q0Xe'
    'aS+gmP5uN+itSlOQ/jGZVIPPAuCK3c+6vt0IR5TFsmQap7VFv02hWYka6s5uH2ZXHp8VTvR6yUSTKTA/4P3rZQccg1OaEe9fZ4Yc'
    'hxhkgP4VDzI+XneyUwKFZFKgzG27/pnTX2ykvokj+ZnXaqxby1SBN00uBf60YDifOGKLNe0f5o6aM27pBxo3qIJu3/z0mFJQCRl8'
    'uO1AfFs48a2SiRd1Ke6HR4jsnIlOCTsJ5+rz7qETPVOO2RR2jzaMK+wg8I+1i7SxLzN/mZFeqawoEl758TO6YJ6W6vvH7/1y8/ib'
    'W80jyJ/WhgY9yKxS/I4ZYJPkuHnCAUiPK3NogsSVo9+wcg61/rzEoC0yyo8K4bu3SXB9idwkhQjl54M4AG3Fz0bVLRUoLCdjLX8c'
    '66td2v5g9D/OSmPLHJZlYmDOoGDnwLMdzl5B0ZazZgxS6T4lcGhqfwxz4sGcROrsT1MvQZVhyoYLktodIxP0OCB55dcYJRPR6MXD'
    'Id/hno8AUQVmvzAoeJmDylm+mapqBrR/UAIGIrhap5f9cIxB0r1WjUirUqnRWWJkTGIaq28NVlzria3Ri7s5oovnioTumwoW/hZh'
    'ueMvGXBxr1E1VuUJlG05ulzv5E5i7fWZaw47S4iZASoo5dOQULl6vcNhRXkMxELhfQv1ZUZBLTUNWujmzJSeEndpnQEqmL4Fr236'
    'eGEFKfXbzuLpelxxD0l58tH8YD5T4KKoN3Fsw32eQTVzFgfOzF0dZgLnLzt3BQP1uKLp79sMCn0cITVHMwuI1vsdSE+KID1hSDgH'
    'pZC+tWfSfLWHmtZ7Ooh6YTWCAfDLRttYGHAAz8MrdynwMOYov4j2Vdfuql44WM7BbbWlsaM28hiW0cWxmniyZBSv3o+2aoF2pTWx'
    '9vNApTqsqoWDxmOdkbjQnbMKCCIXFiLrefqzMLkw/AMxucgyA4dQCuoRI1i3Z6WwmE/FgACdYhduPbspHOKLWzKl46WY0okqZWNj'
    '0VURk1mW8oWeYD6VIQidnjkFyxpekdUGfYBuJVwo34ue4F5IGkXl+KTqP35yM/t1xVyzkWJo8YwvNM+MNM+k3mP2dqc38KLjWu/4'
    'c/aeqiMSWtFq6ZfUNLlA4C3KVJospACD2edNUW6pQlEZTiDkesvcVrVhPM7C+DK8gvrFlS1s8n2QisCJtIHpZUAxOChaGoswggEU'
    'Uv6Ev/bWifPA6kEmBqNbaVaURJS6l92zJ0caSodPH9ZdswtZ4a08jFhe01e0uo4ebw/srLOsJWE1mGvaHXkoKc46BovegX7ydzW1'
    'FOccg0+8Pnpebz14uquuuuoLtoAWy689AbA9qTb5OnHz6vlu7ltLf3uus7xAv6cWJbt+FR1mk+h8lB0OWWXTsq5UnZYjn08FvO9c'
    'jKLVViYe5jRD2RmizsnziiBYcVg59rzql+FgEPtefb3pVb+Jk0Hf97yTldy8q9CBHOUB6jtUmZOcrTVOdTK+WCWfcQ7o93zJ2IVo'
    'aRKcCFfqGzm1RCqdJEvIpVn0Src6brdEQi0aA5H9JhQUQtdeVY+3ElfdxkvlVbfYjxBYHaQLZFZas0W8EGrq7SR7pOPO3OPMzN1m'
    'knQ/i0QpCzdhlVxdONJqy97zTIOZcyQMIU87HWb3SvASnk8njqj95XWuLIKmr3rL02/uiqyUe/cYY0jq1TArWvm/tNOne230+Z+O'
    '+WyDzy4oUPr7CGOaShzU7rX3e1gicdLHnGjhL+4UKUjTcNgdhEcScD+t0kgYGYUtMW5eMhWe90RdnjiME9yK9eEdpubiU3F4eY1r'
    'HyOOULgZtCmN0bGUgwFhWENfbnJeYZPUXArwLB92c68iaHATe/0rItyu+a3RssvU7RKGkZP9POimAO+aylz7sFrWNYguvYaPzo4Y'
    'NBjglcrWdMeOV+7aeXrTRMLaqZAaXPL3b48OMGrEPTrQolxleMQ5AD6Gt/4oACDG80KId9wAQDg0HL5fT5CSaeCNzqdrfmlrWuY0'
    'h6MkCYJQgyq44ypfrbfffadZtB49qogjpYrTMFIXrXMiPRJmb7puc6PXZNOjx6uavQVwo+0MajXLTUvZ/qiE+mkKjDFYW9s71oNx'
    'orYR7QaPc8ZyvKDol3HjQzUjxIYxqStlovHICIfDifkMwgrGdD4Lxq6DBwbLHPV/55kxBQHYU002CE/JE6ujS3mf6cI6N/VnXrPx'
    'wHf9P84owhQPH8yCaqvjjry0QT3FGk+8DUwARUG7DOW0zbPfKbSZ8oANgzFeOnjiVXmA2Dg7yHbEJHNOVzHFJ4pbQo88SVdYSWb0'
    'Gp+va3fcmR1kptUii4GhCVqKvgqrQ5gNGpZBleSpX+QGdr/t7WDgjuj0WgXtxiRjSRiOKGiShA9PqcbrFL5f1ZX7BEZ7wgyLKEUE'
    'o2BwnUZ8v3EYoesKZmfiDDYKGPw/nk5+cdtfTwbwUPeUN0EaT7MJMunP2wR5QTIVUrI5rmKTpa22ojMFk6nZlNb+8Ka/+skavE0n'
    '1Qmd4mkiBoXlnm7SOsgnVV8XsnYwq4yyTIh3wcxEL1boLtGzK9zedHnNBGAJ+3q35s06qHctp4o/Njeg4lV6TJvG6QAkqepVavhc'
    's9Hc8CmwpHUq8sdHiyo9kkobTasa5bDc9KpYvY4t+7kiV8+TgG5uXbmX45o1eQb2BUJ69UoBWCOovr3ZJ2E6HUyc3X6chO+P2J2Q'
    't3t356atA3ZuNX5+nhZUmFfhkZbBYpK92yU9Id8F6g+RJ0yE4zxLW0N1QnOKcX1e451mSaqMpCXZlxW1OfdyzlGc27SoDwbRuNCq'
    'KKKSG8oSKtb+UN17cfTd7u+O/DddQ8gwCfzlTQO/wd/4jNFB6eca1tmD3/6bVFcy8kM+aKmj2QHk59vPdmGbgRa+O3h99N3Rgf/d'
    'zusjeHN08N2zvcPDg/2vd/nX4Vfbh1/CI3z+7qvtox31/M3eSylx9CU+7L54hjjuvsKPR3tH+/Dys/Z3h69f7r7CJ38tKkd0AqIc'
    'c9kibN9UG5+98d1lXjX0k89Y534zyTbyDetvhXKMunKZUNAqe4P+7E31+A/+CaAFz5+swWat92rbYxRJCg1ZRB3wABQIe2tjfUN+'
    'PIYfD8nl4O7acePuVq2jyAsbpY7iQ9ZoZr8DNnffsX6orpkhKbhe8YOGz+pB82FRk5nRzJx0MBPQJ9RQpyai0ESfRVtcQSXQsaNy'
    'EgSSTKz43sMxjO5zTjLHwdfTKoWh5Jw1lmMfBQeWWMSToGvsaLj7rK7Cqx28mRomVpSpoEuZhCKMnWMBBTn5pEbx/vo6W3w/SiZ4'
    '0A67Ro2C6bVVhGFJHgTAlBk86OrgyoIWtiTyh9367lL5cqigG9sYXlXMJxVzmLrKwRb5g5MwmXMaq+y/QZfDeWLGXtBGv5wMBzyw'
    'vkobnCtPidCsPMD0+yjoVtHYPal9chP1MQPw//efBQBH7JTsTi+T+NuwNzlCvLiDhKIMvNVPAY/cWhJhMd+H/YACmRZm/tDoIR+g'
    'YG3BhFCL+hhvbW78N5y4ug6DC0vdDipMOGVnsxfz5VHFQjiP9hIpw6CgO4/0qo7kVDEl1HTSrz0zp9zcdSKXO55h6Akfu/Mc9tjf'
    'h0FStZpxpx4TpMtMcpNobVjhzND5jzQl9Q/xSBVRCbGdUhQZe+XJERbOZJrmS7kFMOnDivc+GEzDzZVPbujtbMVO/bO5crjzau/l'
    'kUf7zIpngl1vrtBaRAokOJsr8WgHgRMKOxiYJqwSFdYoOWWDmvFXvLV5iHVhrPv1eJRB4im+Rl9qdqwF6R9YUJgAE/z+T/9qg8yN'
    '3mWCSYVH9e71ypNv+NnrXnM6+Tl4BNMJ7CRqhBxcfh9PEw8n2UO60Y1rkPwwP0AuJpfN0Da1m6VtCRdKYQjvmHxYo3ApVkUFC8Ow'
    'MwiJo2iK6lDsGLNaUzp/KyVhDRJomG5h1zkNKVKU4mXcEu8cFGEQhM1hxZ+tPLEhEbs3i1+gATI2KOAhWI0G+QcONXWIhzrLnawo'
    '/BSe7VRtdmzzWi7wd7Qwj4XoX3GyC42Qpcq1JBoz2Za2k9mhWZxEhCo5Km6cXA+3dRxlEYItgd1N6zvI52/I2ueUfAGz0LCMUixV'
    'tE17SsDI1tfyxsxodwWpS2TI+Ms3cdIn8aAkzLsVhdMGFbzPBeJ0P5fUxsPIIxDKLnA6CwFYJUpgIMovYQUQ2iVQnDI5OIf7fNgx'
    'HfXDUxjoPrv4qI+NFLhufzoI92EhUYDSbCMFZTj46J1fXrxI2ZQ4Fqd3+PvDo92vfmFRFCVIAPXwUOzTyDWVm2wE0jCzUVj1UBh+'
    '/fu//NP/8z/++39UyRbhzfO9/a8wPzJwf/wFpb01z5iTKjXJZ8S2OJC0RZGt6dzKlsJSM1pHLZODsWbrlbXKKAbNqnIi0FHMf0HM'
    '4YZju7dN5mZ+sF5YeURNa1YGUVUwd2U/m03Uqm1wa6v+eYSiBufNGCDqJde9AQzWxxkKGQKaDhheuqYqQ3C4s/ti1/vy2RfWKGzv'
    'YC4SdxR0NtWiPluZVfe29w++eL2b6e7Rq+0Xh3sMdeGQvdx+tfvi6Mvdo72d7X0zRi8OjnYPZYjor8l7hwgn7x0S/L8t+jv62lDf'
    'EZDZ+yg1s2eTXQ+EqzoGWebx5nw1OJbBGcY1/mmJ0mrdEIiFhnkJ6Ogf+eH8gdRdAChP73+R5G3PVRGpOwO7c7D/zDt4ufsiO7iY'
    'Kurpq93t36oBPtr+Yt7wfpSV82OXzg9dO8G0H8XO8qE39gr6n/+Ly8S3Xz/bOzDraBvLe8+SYBj8tfDvv14KX8TArSE4fP472Fyf'
    '7b3a/blp8euDvZ1dxKQxhxBx/3fokAUCiwz/L4sGX+5v/96Q4OEE3SNeFksQmJbOsOwUi9Y5NOWtJqGcBqGyIQOZjFwzXu5V2265'
    'YBAXSR65JhZPhAVHpoF7VUit7riVjFJ+ON1xK6JXGi/M+1fLkm7BGB0C81W0M3+QLJIuJOCPwzPvzDgBAGclEX2cDoNBTQrwqGsS'
    'k1zsTfHA2LuMPmCKCwwMh2lJ0jt4KOSYHzZFbEa4n5msU2JoAbr+EMfDP99BsvfZGuHIZpS/jykkUauBoV/tRCGH+nP1AyvwTgV9'
    'Prje2KhZJ4eNezX7ptiHxiSmcHDVdd93shUOrq30NDgMnIuJTILq9yC6YCeTbjw5p9v4K8rsskKjdid7FdjGEcNeoGtHxWt776hA'
    '9ZMbU2Dmu3ac8gRoiE3NaxjTacXXppTxmTGkjM8kURNxUqQc+6LxTPf+NWnnFNWXpr4bJLKA8J4yDQi+WvVMEh56kZ7jELBDFOUl'
    'ZOL0F/QC26iPQf6hShbuoXUQHw4ydhma0iSejvpVa1A/81p4d3YVr7+pTlGfJDda1DdWw95kboIhHluFXEWbJ+CHj5V/ED50nxzT'
    'kGMyFx5d6rXxSfgwmIcVJftjpGS0FFpQ0cfaPwAtTMfGFhn8+DRIvgatpBsNosm1GEwsvmCmnLCvpiFmqgdyAWUmBBQ+IgPQTZUz'
    'ga7DALIVfigTyK3aDODilesUktUrQYhkxIRtwCLhHQZ2j2jQTzBz/an3q0xKq0Vrv3vLpa4CLFmRBfKlDug4gc7w4rHXIzFDjlQp'
    'PMkQVJcUZxvDlOCmJa5G5Nx2iW6hBL7vYW5ME/7THb/H9n1s2zcO8IlPT2Fevwwp7dJnXrXl1TPD78PrerOxoQyxuhPDIAHcn3I6'
    'Y4fyzzAHIxD7+Kr4sL0MhLrdMdOcROzM3bmLFKYmzzagjo8V56xPd5TcNeoksCxdrNZt5rQrEsJtkqhtFR5f6rRohkuFi4FTTsN6'
    '2I+gEcxdBcIYwM9kCtw0uQLdY286r6a8fxOk6onKLJnNIaoWKrI2jdNd3Xl0b9DIovk46G418ECTm5YjcstdiN/AsC67N8DGZyZZ'
    '1/YNoFxyRAfZLek/pocaxeQyY03hIjy6RTh0uf1uUdvVwpHxS9CgC2MgANKAQSNtSoSGyU6stH1eFePYG1LiuPYkjKwZackEJxq/'
    'X9Arys+MkN1+UT2fq/+IMZ2eAQ+mNEf7ASyo83D+CJvisOFyeXshWN+33wfRQNIiO+jASOs0dOi/CDrGaLI7wqJ9PWl5tPwiXPMd'
    'L0KgYADkGK2wOLoJ6fc7xPMbaKPC65OYYO7QVHqJJ4VVOujOxFjgoEOsUlRPhxPQraIB8zgubu5Rig3/GEqd2Md4Ga0EPnfsFPe8'
    '7l3eEFBmTjyLK+EPdA1BvfPN58ZpYTPP4YWNnlkGGFHJyrINrw+66DJCU3o2qlrfat5zTsydZkVqjP0tDXeD/plKNkiaxnl8KehJ'
    'EZMQFYvuwbM3XzTESnUqXEejhU2n9HZfkoUvByIjX2okfM8g5GxmOHQNbNipQo36FgKZDfA55dBtAD1Hk2plreIfN0/UUSnmpP7+'
    'f/t/K5lRlBFkigsTNWoprrAFUhPMaT29rOOhbLmiMSfBouUTAKCI4uBf39WfDmEq187xIrsMaDoOe9Fp1FOJJiXF5BK4diejNIdo'
    'OMgn3KVl7neWBEkPeKMAkV8CekWpUdg1ND2kGCpyOub9AH1nj74m9RhNYPaaTV+dzSM4LFFPzir2UoUqvlTNb19q0PGMBU/09W8y'
    '1vlKKHf3sF3KKwcMzRuzm5d3EYbj1MMYnyCmyiw1Sseu+q5hu4kcKy+MetRHRwyL5cxWTjxbK3+HEk8+pSM3COTEtGP0hBC9ECVs'
    'svepF16N45RyY3bjPo/zzuGhl0wHYbo4r6fbipXW06O8nrqvCNtQtcMW9bZBrNy3Et7ySqcVesjrkC6WI03xiqZPgkIuHA+uKubz'
    'UjlxZdfLZTidWv8On5uMlmVwhujuQnt4FQsq5xNGR+nBmOO2XhYwBjrK0YC4rBUB6KW6wIFODHTHTtZ+DVgB5nSliLQ8dEiTQJIw'
    '23W+yWE5tqCMAthhf56irhCNznYGEXTrFRCozs18qbQ5UN0oBQhMLWkyq959V/9BExfFwiUsvBC3IlBB+0k8RsWN70u53xhvCycs'
    '/A3edr/fdBPKnNJWoLXth5azftJgoHWuXYOGRtAg+1J9E/UpuzUDrnsP/WzHCPYmN2F3R0WgxsViHDMtZ+i7OHlKn1GumhyxDoc1'
    '/8l2MXYmXqWKNhMvJxaK5LjALvqcYoUQ/Z8q5DOKByCIYjYnh3QynBxFwxB06WqV8NcQg35/LrgaKIomsTRMbVUWMUidQCR9kNfJ'
    'MQrEdnaMQ0noDv7hzGhW2PPTJEzPgaYwSBZxsbRqyW0yWW8Pn7/F9K+cbAYJ261xfALcRpYR9ZH4lE3NYYrafnAZALmnp9vj6HmI'
    'nKmyFoyjtYSA1ZmLptDLm2E4OY/77crLg8Ojysy5/IBsS4NCuI1vU8wdbBy8sESDA3fkUaWP0hKygOMTSWFus8rZHWuE8jCkum2D'
    'xts3FGqhEaUcckEX2tJF2nIjRY0q9xsEzXOsfkNkIWX1Di1wapxZUvyPCwAc0/cTrYk0xgHGoJgVyqPoucld8sQNmsyTwaBh3ZhN'
    '5xpLZc6oVh0LW3YPCtKOfzsek6pncpVADwtdVqqmNUxP42fvYfVt3+K0QR5w2+5tGLJBbXoSh1ILBH1givu4UYZYV0IQVMJR/Yun'
    'SGH94LpdGUHfkqhXqQ2BHZy3K3R1olK7DkHx1R9d8jvFfZE9SZU7ZkpjLfLs2vHamzcna35jHI+rmYgdjs+oQ/Qknoqzp3yA0UBR'
    'A/6ZrZhzJFKvbV9Qbty3yxDn3Fzp0i3vehL0o2nafjC+6vCbdmt85aXxANQnMgLyiVSnN03SOGnTjecw6bBdrM7bSfs+1LYOYzHb'
    'wxmZsLxmo7We1qStXjwAgYVedSyE4tEwnqYh2gc2V8gRmpm7AbNZeR8k1Xo9nSanQS9c9ysduxxB30HgqiC/gnIFzaAjdkkr5WCt'
    'oXBhyt0Ck6UcdJsbQMIbbxYtQ0td4Nd7mBYpOq2O/RtMd25zEnjXmaFZ8galLP6yD2UkOjkCJMvKKSLfgAU268z8KvbAX3HcvWXG'
    'RWpuoyWgQ3IG0VXaZqtu5ywYt1tNmMoxbDCwHOiH11rHNzztdbo5kbZRmO7oNpS3vTSDt37rGB63vY7AVp78+7/80//kOty7eCE+'
    '7VYHxIH6Je747aYNO1NWA2/dA+D085Jsw228KEgU1mYa4KvQFG2xTje9AW3MDdpBQjsdxJdt0Mj64aiDBev6ZTgYROM0Agp9Yi8j'
    'fdfEcoufgxwsohwy9Xu+WjcgkLXXaXA+uUEGNfM+HXXTceff/hv/WzCip8EwGly3gRXF1JuO1VpTQCnuo6/EuNhmfxbPWg73AB2Q'
    'fWiA5N7v/+EfM7cnDFTL23zm68vkqH657vAgtNRHwft6OBxPrlcUCjRGRJeKIhUh3oOx8pAqXsR8zUnpbal3HU64Va3cbQ/S2AP2'
    'Oh2oDQ2PujE3tbBOpfPx+kRlCgtdhgMoF8qlabPTyfv9BRveZfRBsWZ3u7Pq6xBH5tVyWyDHn2nWvHt+yXa41IY4Z0s8tEf1J9kf'
    'C3bIOTtjR6dtkK1R2cWux7h30Y8VRVDW2M/fKA2/zvHaImZNm0GeXfsrc/bZ7PIKkiioM6MBCk+mYQk/tO8rWf3BrCQrT8q+4jgW'
    'sCmyg8gwF1+Ps2CALB0YNvRv/80z4PIwlsQadaFydsGzx2xiLqOwIDKnwPXPLxwG0NAcQFQeLZ4jIo5w/hUKpI5pgUTUJURZWYvq'
    '4EqbCui3bSVgSTlnMdOHWsVKlWsQIT3up0Vc8C7BVsxls5xKmBdSAhW3rEQlZGW2SILZCUYov5AhDmkNAzjpXNzoD9HwXg5CjH6d'
    'TJlJ98P0Ao0ZoMg2Ko70rG7n3k61xN7IACFXExJ11EvlpXUeBiAOpu2bipiq63g3uNKukFLdoxQAa6hrVmaqCtrR2t5vDg9eNDie'
    'aXR6Xb3BAZv5QvsdF1UOTDBHeZV7y/EFmirkhyQByZ6giyZMzZNvQzVTXl8Op0vLR0H3eRIPgdsHpAXX0I8znia9EJlhW9+YRqkT'
    '72XjvxZvLyNYp8A35HpmXhrrYeX7f/4nDxmGZGdCsyEr45qjVUQXrfilgX6eYzwULRJjyNEYQ/t4lL0n8UIkO6vpLEFqviZ9pfJs'
    'TQagbwloxZL9trx3ghORr2m5/Wb0Cc/zm9Gb0R7mecY8du9DrwuyhYf2IMKuH6IHXr/xzgLa9t7txNNB39NLQ1hdGzizgxiOyevR'
    'xQjtc/SmMlOA7BtllulizlKMQQ7hFU6g2jQDYWMYpike+K4K4Ap2SBblMLgAcQlzzeLShGWgxjlKccFi4DtZpC5TLkJA2tHX4+lY'
    'IWDJsM8oCcPjPIDmTCG8AjGKI5Mt4oS02glWlhkqIL4Gp+x6lilZWl7mXqkU5Rvupc3bJZkD99L0iFP1VFSon/YpOiJ1ohEIIaAZ'
    'faiTJaf9qAnqziKN7tsp9OX0ui4rXr02Km87OesGVck22vjcp09obq1zrJN2dzBNqqDe+x0HW+eq652sHmTBd/R2P29i4O8YU6Xj'
    'GiRI7bxj+cWyJrD+EKryX6j0DIMr0Rnv029+ftT8NUC7qqfnAexF7aa3Dj3wHqI26/T3od/5cYqyawVp3Sc1bEmt+Pv//f/4H//9'
    'PxZLVHmdbCOj7D4oVHZXnjDreAGsg6QvYU+lChv8GJeo1jntdd3voNW4fs4YtBoPHOV6nIR1Uq/dQVlXuqmscBO45PHaWa3y6WDS'
    'qaB8OV44EVlixpf1cNSn6XiYGXpRF1Q0CCDo7mRkyf+3ZxWaIYBg+1stxM7VgdVqKbfXhyZghDppoP1GavoahOZGsue6Z3X21W1V'
    '1RUotYbgZMhQkVeteG+f0qwEw3HHjgJnzZV5+YRenrkvV+jlH6cxvtZx234pl05L79s+O9j57e4z7/D1F1/sHuItlENvZ/fF0atd'
    '/HiIISFgoGveWRIMYX3QyXgvCU4n3tk06lPoyAF6LGAcQox5PwFhk7PFU/h7zIPXhYlFYJQt3gR2w0PlBi123APxI0cuAEkBlnJK'
    'b9jlzksCEoYm5wGl3yOHLFVJTgX+BiYr66bF7k1yfZjZPFlQvgrGHOsQZTAVVoeWDmXOPIR5IQc4+TBzHJE1dAw7AGzFBBUgJYmi'
    'CijDwoCK+F7BS+0OCvQSD6t+YxLLkr33wBer0Lod9r0AhssHgBUZ5y0Kq2ChhT+3GhfhtYlDijC2GlEq8iHGPjP6Vs5HTKK/hhMO'
    'LQqQON6CoIhHZTnXsZzmGwZWod+iU9cF/MVoWkHZjjX0E1wpxbjYYVYZJQBFHJZhlvSA5fIqtGDlB1gGe0wUOrEKPY+TbeUMIsp7'
    'SZPU7+otBmoMIrbtiFf9cSNk4mXsWJE7LBogBQ41tUYmCEnFTcsbDuLRWXoUb1v+easO3C07ikrWR8/EqXsfDEh8vltCiagB51sz'
    'qjLXNxEiCEqUfs1gM6EhdCw28qDJNC2VqsZnxqu+9a1yHK3RzaOMC4q+L09lTsKGKB1GaWotVixnmX84JEoZbBAkNGC9tu21a8XV'
    'oD7Go2fcYm5o3M9Mosv1aDlCRvvJ9UftJ7Ivu2/UAscOsfpljYUu9PF7dxYfxR+1c1vzefIPcZknWtB+8HctP3hffCp5eX0Nn6v6'
    'E41U1kdF2K1asOhKEQ8Ge6NJTJVvYMWeB+8jMjCkwzienIMUTFmV4YXcLtFmJQOGbjkpuxFJmjtBgm50u9A5XYyXUc0r7ou35T1o'
    'em0VTjjjwpGfR2uayNluSadwEr/qWMN2Qxt8BNdy9U4i6NwOEPBrqGWDI0RvBYu7ZgEioqTBQYFB99H+wQ3gG9OeE+gpv4/lMxKz'
    '6wymRamWLBUKnZZW7btaPemaHQGfAr7amGV8j6mOjug1t4QCU+ADeB6kbDBAjyzCgoNY32GTsFKWduSuV9WOhTU1hlyxb+HJxzI2'
    'J4+LZqKZWdNHnyt2UbdrFTxdNeWlZE7BpKoFtncd/b84aJeKa5v0l+sMlizrC7trW+WUQMHinadFPSc9Ilrwl2sbS85tu44lHF9D'
    'cn4tB472Fx1lDP3kS6H3dNzZKOtPLx2jptD4+/0//6uDg/R+GRywaCkO+LFilSvAga/zquQDPNR65JhaqohnjQVtZx6UTXmpqVBm'
    'ozJc5XvFLV2AsXxyMOHAFOlymEjhUkzkuzMjZ/Ec2GxCUuDP4gWQK7qcCnErAMx7dzl//w//2fpGxyjw9ovYusaOu6Yp4zqm08k1'
    '3/moFVUzeJfbt1goyMhASjf0MwNrM5mz2LcCU+eFuTL5XeaVyyw58h6XXzD8XKjiVimcCf0xMx3//E/ZAjInpl/7allVOOBAL05U'
    '4Am36pypWgpapuuLZjAro2ensHgSqZbvZASUo0mlaiw5Q1J+0QxJsYpbqXCO9MfsHP2nbAG1bpR6ZJrNlJy3egoqZ7q2aAby+uAy'
    'y0hqaf6Le6VwZ+TUNcUwVYye1C/Z9LGmvtSUv7qRvxAYJ73QFqFzIVkXCpofT3wm0YoRsEXTvNqUnuPxiVzvEKZDPWF+043jQQh7'
    'KGgS/Lbt3S28J2lBZDPhXLy5SMXkdbDQwAsJhU3QHU0BToX4ufC6dg9UsGCchn0TdT4H0zVrYvcTlbBAppi/VMUfXkdvv+tiW47s'
    '/BaXRyyTPkM6vrW450X9uFOk7sdyv0d3LBMqOH/hp2YVtgILF7AEdgWDCmLItYaPF/IcvUJfOsw0pqsUtBdeASp9GADdYmmDitVZ'
    'E7rlVXboEg0GicazAls/QHctKlX0sZOjZTXD5XYTPaUldmXMo6QSECo3jqwBIu0FI7ZWPJMFZ+uWN+hVEZ1ei9keuFnNazr5khxH'
    'hbmw4rESHm9mNqebH/m4yPaSD4Hs5JiX5GSWEqzLz4kBxDLaPHuWNjkb1KfhPkYw4vS5Wd0NI4+rbPf59BOrpeknVFI2qJ5NHmG/'
    'w+QRD2VaMcHJHyjDCf7VrD/yGr/6tPKm/v2f/svJZyr5Blb2TYW7KknJFmcp2cIsIt7RQfs7TDCiM4l8t3Pw4mjvxevdZ+2t7746'
    'eLXrf6KygRBAYgsFIajpDMe5Z2PngGEZwzl+ycaYtvUCHt5cdOmC7DF4rm+bS+RWbFn4ACe2AIWilw/6aBxH6tjE8LSiqDmpT06s'
    '3MrQET8rYqch8Ug8KTsMJ8alyzp/GJKlHLZQohj6hRRKmWuC+ocT+bcCk1o/uVmvzdbOnGt24qycxOTcQ/WPmyedzPdBfElLjcqR'
    '0/KlSpTjZjhFjBvnQVqlGpTWRo/UNA2Tr+Ne0LUK+AWpVQkGiGpSxG3g8OXu/v7bZ3s7R8f0+YSvx9LpL0hRY6EgQrSG93rJXYpQ'
    'zVWVYr5fmqd9ORKQA2f5BF3CxARf8Muq2EwtuhwZupQrY5jl1M6hrVOxqLCSmAKG2QYl4fZtQiNw8O+xHecvG4/PEBoWd5ZPjup0'
    'cgNmQ1r5cE41DQWBdNz23vHlx/YnN8XHsrO2XgN16Mk7E5YPTRcYQlpdm1ahHiUUnn4vASF3KpyPxQAQ6Rpw+P5P//zJjcJ+9v2f'
    '/itOEbBfTB7pdTEPjEYCh7NhYWFUOWwjHmGgJay1UxCrUU6q2qI05PlRdupKOBA7oQi6GVQUcDtVcUFDRUl/SOGRBCs8iDgR270e'
    'jJMKWTQwmRwLYA8kYoUVXKNhRg65rQm6aAMpCKif3Yn1pGWD6csCVMMwczVad1VYCYpcysVkQlE8TTOrq65Xl1WwF4LA9vR6Z0qp'
    '0aWiva6OXba91OJScNwFZieIuus0bXPisvW19AqLk/F5MKorRN/ZoS9vucru5laZtc5A0eYWRIjFpaV6hblss8vMicG53OIpiNk7'
    'y3FpJ01fKaf20U12B92ADkHSXHT4nz3XmCMlK8FSRNQGC712tAYGsuW9++SGHmcWOHnlRrWrpJUZOze/82hy8OKHhBAFKh65Rwe2'
    'T4qcmPzSsiyUuoLRXr734gvbGewOZ0xJdZg/bYmjDYCuNsS9CyBSa+Yp2l4S0nWt8L1Ei0BJBaGdRqMoPUcHr+sx6l6BdxknfXTu'
    'QpEovkg9ikUaeGj/Ef+zvwX3LuXfpYQucezCsPpdDCOs/bhwebcp3WNNcwBxr6PgCBKwmb3j9KQojxOYNbypjzJaBojAUMMOU0oT'
    'Uw2v8ApiD3Uo1OGoERSWKP5FMQyhEg0CK9dJDgbecUfbDsM+5k0RtzUSxmsIITobxZjLFCVyhIaGFJLGsUO44VLwjrcYlghV6ERw'
    'yHiylQuwhLh22H8GAgXeWalT2CrOqUzE6gWDJAz61wZbSnalyBWeDDIkpqvWGm73SDIvEPL9vBlPO88Vb0emILq6bXrv1PqADYyr'
    'zuCpoKnZO1M1THvBGFAT7YRLa634uPHZ6tYfPrmZVf3vjt+c4MVGTKL85s0nn4qdz3RTSNO2bJmPRIoUpROf3G+sGXmqdfcjh1XB'
    'j/RE0dQKdnF0Ebtj7cJqKCpWlGxk9+5r2Yq3n+6ocnpDNiIvJzjzSPIlBEnsBW5HbwgrfKNEXVvMffeKB9JTNTn+jKolNTL7NVL/'
    'q/Bs92pcfffmTZeuMeopmsGbdzADEdomUNfPCr6+hUXbPvXYo1gpNADPo6uiJcA1tYeUql1KyKg/FhFyrcC8jqvTrD/HzMTMrdys'
    'jLXqWMoYwfGXTzVLb/wtoEyyGSmLmylpuEiRc9fiIXRdY9lKjxNU4uQE/EZRCPHrADlbrzdNOE4WMLl3BP4dXijUHB1nmytX6cI3'
    'MyDhUni7gMw4fby+FAwug2v4BzVOIKyAOSjHwDCBK0usOIIhTPaFh1dhLgOYdQ7CPupnN4dJfEGBndQVQLGpCCEDx+jiRazbsBcM'
    'hITV4IXEUUNvShyjvf4VgK+3at6Q4syc46W1ahU90JKwEV6FPVbhffKbwt3At+oNG6Sy6DAu6sMmgrRnpyBnGlmA9C12qYqYMpta'
    'tQsowKrXbB5kq3rG80uz84zOxrcOdgIaYdptZQegNIZanhKZqYtSbZBc0701zGkX9i1/ZDSYWASMFnTjzb2QDoqNeIDcAcbJA2Ub'
    '+HHCF/JdUlSydV9hSeNC6gviSXdu1saIpW+dkqUTtArIgB/ToIp1VSmahNDa8Zu0Ubu71Wn7KsevqutnEd29mqDC5FlLBpbFZZAy'
    'niKHAn5EyV40HIagIk1C6F43PI3ldqAaY2vxYPE0RxtASjogwJv0DWD5BtB8U33jn6yuOSeC6QTZKQIgSMf8T2F/dWFgLOrZJMe+'
    '53RZwF/ihKqiOauikTMkQXB1runXz0KQS44XwMIBQZp1EG+0qAQ7hCsmkYoQJd57tFFm1cqM8fLSz7BK1UxGALuF2OXAZKBHCTFM'
    'FS6K0KSgUNakwzDEsDTHNbrvAprvNQ1cmLwPKD4nbuoMzVxoMaExMfJAWkM1Hf4Oul20X9At65SzaaAeRfdoYKUgdaUN1635m4NX'
    'z97u7x0evT3cPSrKHOgUKBo7lQ6yLDe1+41N6vn3llE9C1zOOND2/Ym1DnHgOe36MRrH39Sb9Ucn2e/ZCWk1YKniQmWzO2x8xqh8'
    'J2+gvjxx3QyNRso2p2Lb9OVJTa8KFYuvQENQRWoW2GKPQUB8veHt4U2nzIRFkwosCHGxJ/LCe+GjmMSXjzvTjMe9hvd8+uHDtQwg'
    'tkbBTEmhIWmLtZokBMRIm4OPIDRJmEGjazA4+FMN3scRbP2jOEqvCUTq0c2NeAwLfgREm6fscNJr+C55FFFGnottlHj3n2KfvqIu'
    'FTtN5eJWo7ynK8FIYdiZjuu9M8Era6kbbZoi09BEofEMI0Wl55MwGhGESyLZoiNezbFhnjTk4+aJmJ/gbdW8bvFrPbs4FM7XJ14r'
    'd2hQTtoWFtBijrRvTdz6CPlvxNS1/frooP5qd+fg691XvzdJRu+QfOOhjHXttZr1NISJwEw5vYsaxggA5h2lcjeRhXYdz4VjBh8c'
    'HmEwXjSyACiK1HEOQvikGwaThncE1V5eT84p4wcFHEAHhBCFN7rTiA7WnOQc9k2gjgtcdCjXITAGsXeqYxb0koDsaFUVeOQiQrGx'
    '5h0cAsBuHE9q3m8OYcH3wrFEQInHoKvhrsU7aAOvL6BQRmFI2Q/tAsOj5hECWoPNErd6rbeko2AMZMZ3L2HU6MyMfTJq3HUSQesK'
    'ltcHqRAD39DoIfI0Zpeo9pxyn8Vl5m/I3KcHh619mlj20DAOW4iybXl0F9Yxd3ne3ouj3Vdfb++//eqw7W28bTabNTHCJeHZdIB5'
    'jILTcHKtpwo1kZBi7ip7omW4w3MWDJInV7fHZJ1NoXhKvjbp5BC+fgnTZtn8oBpvNVAM2aNccUdpf3RGZ/eqg6JaqLpIhBOy8pEK'
    'weTABIKaA2ZhgJGYjjNGPUmC/EqAHsYYZKY0hg8yWdX+4fl0ggGBX4V/BLkse/fINg5o2tcjLocC2de4ixgvHhyCL9X01TxEYfcV'
    'BeB/sbPbGOAVeTkY2sJAw3ihp7XebJqr5pKViLnMBxZEYcSiJM9rYKlgdBzYjdClND0PQGSDpYlqJLehkhfZKYYE7g7DkgALVeda'
    '/XyvH0C8O40GfalKAXduzAALjbXJAc+bYVAsnOtMbgWFhppCNDaQTujYiD5SjoSbrCM2IoieaYh7Vt6yUyq8VQVVr/ACzQBkJun7'
    '13hrp2pDq6Ezlbgd0lXMhfm/D/fR9IV13ZYnmAT0MN++KZ+7zznL9rPbX9jDbn9u3xiC1SsbOlD4YvhSaH4rUki3MzN+typOGlMA'
    '4dDg4C6KEPLkyqThsy8HyXVSFAi10WgUkO8EaactNFUrp2bziaNKYQWMnfRSwkpV8Paf5bQr2CsjkFphvCL0ggsmE9jeBSPk+WcJ'
    'uhKIRylwu2GA1wvjYSO9oDgHl2q56G1VDNnwiFs6MJWaeEyPoQWModg2cRVRnd87PBB/SmU5pjlTOMBY6EncaozVW4qcJX3CtBb6'
    'A8NQn4oswQrR59BmmIyh6QkFyCowRGUijnE0ryrdBqd7cmSe5mhXxxXTQ7QYsp+E/JDokfgYqUG1XQroMuuWJY23GT5A9rXh8Ry3'
    'pE2vefWw1eo96vcoTRd5ieHXCD914J/HnmWtgherq4rvEIA/iJ0IFfCduB9uT6qRuqzFDVCghGg4HVTxRQ0abLZgK289umfd4Sdq'
    'oQLekyd4Kc9EVGg9yO8hGENsFBpxAncMkTz/bNkv8//LhuRztswl9/GGCDD29p0NnScB5ObtNZanIpVGdQyDtul1SzpAVW24QHby'
    'yEEElOrHTr0ZP0eYCBST2AJrqeMZGQmW2TQY4O0WFpa8NKJwKgHZoihpjuoQBtMrXh6OfisEVbrgTKe55KYp27AFvEx/skPv+NiX'
    'xCfUlJePTugVhyfEnOJugEIvH6HQy4QoxJdOQMLC/gDC2GE7Hv5bK7XFnjpaVjHgpiOyplNGKaVtwWuggC68Q8PKdEJ+45RhAicY'
    'uUiDwJ+i49ngWruM54ZOn0jNMosWBV57xZKI+TOu1qVXMSKultgyy1mTFw+/HTdTmcp4LkDnviCTmVngJeRGONRFrS0nuVsTm5BZ'
    '5WZWscjMjaVh54cgRULpbkaTyKl1rkaR+8yahYaTUS10PUv/01mNFOu3jzPSGCMSKjmMAgWmaOQYOe4O/ThM0RUChTw3QkKmfdBa'
    'cmrLAQfAGanY1GRabEucSKPlcrBUNqrHY7YlYKxmWmJCXri7lmptZgGZCGGj/jOOrnrI819VprJXRrnOJm4rI8k7KlrpElrjPCQV'
    'gxQbpZGBc7htzdeJ2lpkdEH9hrcEDXkruzuoLxScWGXsfcprLUXxkNL0BBS9K2HMkdqjkE6Pk3h6dg6k8+C+99unDe85BvLySIm9'
    'I8YC2g1rNIUj9HQcmFk2TEydC53Hg74yHaFNWOMteNHeCNTDMQPwUBRtTrHmyxFsjOi4p0YPbWx0hEIWbKK8wbUJfU6vn3LsC2fA'
    '8DqX9du6wfEAiLp5h4Oj2kXucGjTzOAWzOLNzEO20r0Otc5ATglZVgU9zTGqop3RsCoVwXQhw1J7Y+V39UNSF+ovBc+6QhTqFeBe'
    'aZGnZFOYXO2O2WH1UIq3jaIZ7iTHy+ctVZyrWfx3ZLxd2MnOwlHvWjVZXW4l5hbPIomOr/VpwrcCfi2WT8q3isUD74xY2TqsLT14'
    'd2RM8ldr+YxyOsIojxiF8T15KTzRo2kN5ovto72vd98efrm7v29bQu5KKGq6Hrc9hoX8nq9egDYtngig+qWgK6bxMET9GUSo7SkM'
    'DuhayufIL5vXosjW2OrtgIv+O68J6npDbJbPwtNgOpi43xgJsjNYCZBFlapUFHb57QPnAP5fOgkYuRDdhvQVZzX6MrLPohRvHR+M'
    'aIj9ghZU1lHP3Ea93QDlQSJBGYilnbK27B1ST1ChZeurZt9KppuOvZ9HoiTFaQeRugXDMIL17SKpu4cUlR8Y2NyOak7nMv2PGOc8'
    'expzbfyTEEbHjQxOJTiIuaX1aco3qtssow9ZlgYZS1dBweNk9scVQuG41n9Zykk2WHd2NG6Zh4CqL0qdYEX+Rq0NFs9wrB2WzdGL'
    'mLrSuU0O6xqEk51ZwKBILtPeMAYwbb4Qw5c+SU9tiQfrKho0a6Q4AYtdRRHQJBd1Yp/OAbFNDrtucq8oE6MKeO9SGXlQcAIHc1kc'
    'vUsr4rlZyeoXr1FDocASsLJWZF694bUEdlnxfjY6kzPLV9o6fI2bc47YVHj2vX5q3T6lsw3LTK3s11awsyTEm1ECPlTWa9IktG0q'
    'w+34YK3I3q7F9htjMOHi+hL9OwrWb7/jcP303K/MvKrGxX+XgcGzsumRsb2aeQ1gbtCOToDa2YZnzvasPsqdZiv/IRvFxalprl0c'
    'Sd9NXehY+LSY4dr91K3p3OgWjG/J3Ki6c/JUKCDZXBUVE0NwZserKJngMgRsa9/t257dyTaFIok5ibOPYO5adE3+STYF29X1wErF'
    'G/cEhQQ0etWPEgobR/sUveHEWSZYqW+0dAu+Omih0wtODeoUOC4oTc6WiC7pCCCDiAhG7okSUrPwyNk6wikA655/9GOpq0Wxj7EH'
    'OVlw8kldLT56JyNvlEkTendj1mVtblmBSl3km8f6RIzKJ08xV/neYeoUTbuevtAny6f8Nl+AJlqmil48jsL0na+TAe8MlNO7Y3Ty'
    'RiS8BBN2z6NsJoisxBcgu90rbTcfhNWsPTkveim7TLnR2ZQos5F2yvKcSHIZraOfBoBUP5PcxC8wI7sbJRuVKW3TiveXJZ9Jhise'
    'VLoviByKpH5ZIUuvia35C8AraEuc7TOKh3gQZ7SOP9tKXYrcFtrCVdW1IOmdR+/DuniPLGUWX8bWUWwUL6ZbTAPnXYTjibrQor/w'
    'PFRcgzolrpi3DgheT6cZwgAE3Eu1NhBAZn0sXqDly9NZW9vphTolQge9Qtv2z6Qx5/nXUha2hcREgC1fg5/yMC+bb8yxpeaPX0Sb'
    'cGYoQ11/YbqpfbLBCO7CXxH5I2MG7fz3VzRTzzGItCbXfKkd3kG/kUSgquA8XvsDWRtf7F6cSnBeL0w2ePIzkYbytXK90hWd2FHV'
    'yq8uScBgrBomnb19kFME0s8c0haVaaBb0cQ58Z5bfF7gtArCqGimVKj/GuxV0tEknWwrH3Cukuk+h4dsAzusHsMGRgEaTnwbSDjC'
    'ZGccYULNghP1XO1ShaHoGCUKvySF1KfimbTc2C3styQU+o3yMz2kAOvOWYmYpMiKmUVZydx0ULU9iobESJ4nwTCs5gpnQ7znCqjg'
    'aSalpbM2GnKKXwi5KN1lfmXddi0VyTA/ESlbcQjnlmc0Ssg5pyniEj+SRFDl63+JZW5c5BZxwjJ6yNK2jVwuE4f9sRGfngLZvKRQ'
    'NNZdUqeME9KftPPlGZOnwsNu2WBmhcJoCW1afHuwILVzltRMfmcxKoKaO01vA4Fr2DBEB5wPhIpoKQIzmhmyHlB+6UE2pXTFBGKk'
    'Nn3BNmeCBCUOHWsSS0KEHfX7P/1rJWMm8PX1AsUlLbY+LwXsYiS02HEeYQt0ITd4DyobuRCJ5IvZsfhir5MMdtlcsHj/sPwUQwv9'
    'Zo7nHGIgrNxBxl2dotUHfBPQl9FKyVkuc+k7i3o8Hek+V/wi/mKkHdcup6DzZ/TMdN+A3n9shXKbOxeFLYpd5o7Ofoo2zvJyM0NN'
    '8wsa2wTqJWSfYPLTIYfuqNyoFc4AbdMoqC6hRSaYD7piTQcvDEMYJaNp4jzi2+t8oEfL/IMERKXss4MtY/bPfvNz9nzsCRZ1JtuN'
    'A0b2XBIxGJz8Bqo5NmbkE84HL0bnJzrNH73wVWZtkJkySdhVGLWy8NscuFpXop9u9G3D0nDK3IJOdtDHEV2658TtmNwzXqGrvfDD'
    'BrHCrsN2TnXud9T3ZytAQBwvjTxFiVLwvBGvAKDFdYaJHcn9c3OFPZjVwnrFvOop7ReYu9HNtOlmRXcQqtMYYuZKHvnZ3OTnblWV'
    'U93tCVuJ/UySdcRWvePQdFJc7Hc6gUrLt2x6C0oWWPvyDXBSLqnTzBPpjCPVubnf3+mpJmHbChFOc+9Y3VXYvZLJKDdZ3GKrEB7g'
    '2DLYIqm4QJH9Q/RaxxxYYPKwZdS5XbGkiZTklrA/R9OiFXFctAhO2oquLdlAcpn+YNGA6/sCx9627ypkiwUnDrwtRQqteR+zs+x1'
    'JADn+aXfZhtnB5+PY7Cbb2XBQEQKe05H5C2b5X2BHEHhcLI+EAtFiyPbdp+398WUa90VcRYcSJR7WNjHFHkD8bInGHIe96MPMJY3'
    'gyqpewk+YJkvaXmQrEFl2RF3nETvg951Ha+KYniKs1GcTqLeR7Jk5lKLglhBv5+D1JJPoO7cBhJ2rrLu0CUrPx/ShBwd8IqNvt5T'
    'UQK2uI5WKPJApowjrWonIokaz+6T6GpNWls04Ugg0xQN2OMgSpTnNN4JAIamIy6njUoJTg3gM4WIUOQBPqa1ETkE8uAwJXh8BRSD'
    'AK4o3ATd4Z9Q6B2UvKkq6kDoFHsWRKNSHMb9U7bkZD/gz0LkMJJ8xbfQAj0c2qSoZgGbnb3WRvP7P/3TvWbT648jij3f8dSh1QhG'
    'DuSbPl50hxWHUan6wTDA6y7oRpd6w+BarWx0FcbpKEUfY1JNx4V4nsaDPmbNsCbyPMaZpBg+VM/jMjxE7D1MHnByKogaDGI5FwNc'
    's4XtG/8xgwGlGPgyHIy97//hH3OmaQk3I4SDQS4r1qly5QhK0t0TCUeGSMukxxm4OP0wGS+FFCPMN+QSpHMDNxhFk+gDGrVkqR9B'
    'V6pyv+5GLr+5S5B3hS1kYbTksm4rUgwP643LCAyFdhZQYj496Fj63rpc1EyhB9VqUPO6pLd0zfF8oM715f6nciJQAG8UphyMieIv'
    'sQ4hKsSxvjONb08qOhG5VY9hmyBlEua9/ebN8R/eJG9GK5WTVYpTdkxrcRxMzgFQptabtepWG09f0+/O0SL3Zs2uHC2oLdkCGm9/'
    'vVo/Wf079ROe3zR0qB0BEw6BbxUg0BXEoeLb+snN/WZt9qbLeBOTB62NQk2dOFFu3ShWD5rNguubSd9QSynX5vsfm2UEZm9MnDsC'
    'y9viktl8ODwUb1KN8TQ9x4u60TCcc5XVxG9kPCTbfCFIFPqK2+JxqLfWF/hhU3HbAbt4lNgR2d7AXo/Cq7EEOTCCGu/HlPSitMnp'
    'CPko7PZJ+K3kwlqyfeCrKRrgLTzsD4KXQC9BK3fgGA9QYjQN7o043nXkRGQosajlvQ8Xi8aWaJI1CiwjmdrOumTiylKAHOxuKtuT'
    '1Z7jxOiZu4NeOZAbJXtsKyFDZ26xI+5o2wzo3dEglSggdJ+6P+1NMIApSSIVHeTza3XPu7jprYYpQ16hJcrNMTrp1KFsXS6On6BN'
    '2tJVtySgvuEvfxCwb9LVtYiSpRDlTEcXo/hSXT5Z/tq53IEhDxUun+uR+iRxSsdhEqCcc3gNa2JYPgKZgoSlXHzioPThpWA7pivR'
    'C4fUKUbgUGLpqVMEAdZXDvfZeX/K2beyi4HjRhW3mCUeOovgWwNy3R86gft+G22ZApisV99E/cn57Mp9+WVoh5/lmHVUkx8bl6qS'
    '/D53ykus1UM0sbTlgl+jHyKCL6OrcPAKV71EtkWd+au4j1f/FOWpB1H8C88Y09P6JJ72zito/K3wIypLMqYywiD9DOdB1lEMsRzN'
    'Uz9ILtRchwlxqFEvPIowis5CMJkaBBAjdgFQNefGTQe1uLYnZqqyaXWLs/XKhO8VrotOmt+IIDp3mRdVICHNXZLKtfU5ib+LIReX'
    'LwCM6Qlg1GjnbJfsqDV1oCvSxkGXLtGLYb8qfI+NwdVjE+nhBAVBagWoFF7P2qBeS/gRlkbJAzgmcJX87UcqU5NgQ+u+CvAwQ4O8'
    'Eg3fjCqFB28oX4swzcL1oiNdUQLrCZUuOtEtPNsXXjTPPmYGta44lxag5IWv4GQtjTu8RdM9dQ0GVqjep9UZmaN08xY6f3tfEgNO'
    'dJM7Lv/IQ5s9LJ8VyCrj63mCitP/W02Fs2NSXqYlRy/rdzUK3kdnAezM0LFo3I0x3SXFhiPRmcLw5mzCaHt6VjixbFTqV/KX1e0U'
    'wiD9zTlIwTaxiE4iDM9iHZSZNVVzSTexMChaVIdNi0oM03UwaPNOPATu2q/y6ZmqIBP6wzucUXffF1Kckrv4/gi714iAspAYrVpI'
    'AzwqyjylE6GpmJPGovZjqatSsc/dSe3f9N6xhKjVf+7lm9Gb0TOrc1XKtMK5ZPC2v99+M/rkxu4+wn8RU9yl9xHmXZwRjMLx5sqm'
    'Z1DUyjDQHcRduePyFB6rx4zrSc0jDg7bOvZrDWSKaNTBuDiw2W5OJ6f1h5WZG6T4Yg6BCmViqcZ5Ep5C0dev9qUUbzPwu4rImIJ4'
    'TR9Nwmbc6jJudR63+ic3ZWKrVpJbTX/WmFxN3mmw5G9dzXodsRsKIgUzCoq3QUojDXpri6Mp5ChdzadMNFmLhb/98sMjqow0O7sv'
    'dr3D/ddf7O+92D30Xu2i4Py30X1HHKH8Xw7/SpOnGMxMvevM20QpwHNmC83nUTgdhFcV5+4+bdf5pn9kO5KvwWHSyRfhhBpKqx89'
    'Iym7jsixH7Uh7raSXyCizGoUzovLLZmhVBsjKUeDdrcQeKur5kSsJCEXx93O3gpOgstFCTZNauok5Xtg+EDj92VI7lBVgGJiAVOn'
    'lR1tNAXVWV6JmXXVa9Ww3ZpArOlBcfwybashA8jOokOS9mmrGnZnojuuI5s3NylIkvNe48O1BZWYJKmoqjvF0XQE1exoVDwJib7q'
    'Vd1vd9VRHicRtlNfO+WcZL9537bH/ei9RwtjcwWExThpvw+Sar2OaNXv+Z1TQK1O39ugfcHm0hmDBoFhW9eb4ysg1JUnL2JGko6C'
    'I0zsRA5H7GyGQfKJVBuP16CpJ5XCEOYlPnfSE0XdaT6bbv9MZQ9I+Vi1D2Amu1foS5R5Y9vH185quQM8vaneM3FqnIbyjRgvLseR'
    'BSabK6gH2Mo1qjN0asnAmTWUZ0iuZTyhLpc8YES1f1t86XoXaZKDLxVTxnEsulPghgP1YGEylvCgcZOy0pVZWVVo3ekhvkCJLm3A'
    'sp5lYeliaFM/OH0WXBeNJn50gOrSM2fgGKl3prN52zXJR064DH207mwvimPBBv+b6XCMt2yYyKOREHQmPvpttgcrZDzC3B2kyDw0'
    'jK0FDJ8tpuwNRgBWTiqObVlDxSv38nxMs0nXTO20lAWfsSlQG/dGk/hrkP7x9kt4Dloh8AagqmEcT85hALsYsRu9DEmcr1gJHIuB'
    'Or7KOsujRby8O3N+IKTfcRyNTOLTnKsUVLE9li3Wv3tF94xRXb0N51c3xmH6yBGcbihnZ87yK6QZe69zvjtX09WOPuGDPTpqnMSv'
    'AX1hNpRgaFQsVL4ZIbt3ZH92KsOf2vuRALzhlNjYzCoM2WaFDuHwwtiDpluknJVKZZoqE8rTh6XWJ4t49V4NtiHOidTwyL+D1jKD'
    'r3T0fqywYPwBmRwuDrJHMewnghe7jeQ2P6lRossBIFTkvJwmp4hRrAuLNbdgKbUtsHU2Ptq1Tk3/wMedJ3gyWnkrJxIcApvHrm7x'
    'F9TZKgxTKWyF2hkjlqPwlxRI8+ckbr05pUZoQcNpqm2ljyfJk8eTvpItlNRwH4SG1jr8dZ+kBxY5fvXgwQORNKIPYbvVGl91bN9P'
    'ok0fd6JJX/aOxaAJ3iUdH7Q/b+qmNjY27KaauaZcMYJtKbPbtQzqS7tVDNbZDpeBqxF/+PDh/DHK7aQ27vBX8sQ2OVd0nEY5JJeJ'
    'h41OrkV5vzs8NAQmpfpHQh5V273CWgePn3AiNVs+vozQpiXHNahEQvNQ5G13EIwuuCB81KcfbG+svnt8Dh178hjFSiAlbA5lAAeR'
    'GYXpJHoXcxN0lEreYekEB/QJWgVvaOxOg2E0uG5XduJpggcpL/AAbhiPYorY0RkGV3U6gUKKgQEeBslZNGrfR1E3mE5iNRetAP/r'
    '8CZ23rqx5uW+rlbvxpNJPMRZ7MzGN+WkLq00vaaHQrWApbOOG8am1Wz+utONkz7mV4e9ORinYVs9dGaTpD2anGOiQtgYce78G3Q0'
    'OktQDm//6vQR/idg/46CcXoUi/eGBkaa56ax0Npnf91GDV5Phy/2Xr7cPfL2956+2n71e375V90v77M1VJZ+lY4ikCQmKRs2vAb/'
    'c+MxrXgbD3AmPaRlPj1tew+b78876vS07SGD6tDfdU6mTGfOQE/ToUSPbWAbpOcCXOJnXqtD6ThOB/FlHWDQcvBcSveI+i0AqL3c'
    '2Ce3qm3QJM9Gdcq23fZYhOx4Z8EYUB1fscSnmKD3OTPWjicLQDcG79MYU1uxysqfRaI0S4w4s7rOpNFq4/17XjEYKtOFjHYhuxsq'
    'xyB3xVpaquUz0JQ9XuDyKsDTVz/TE9wiPrd6glc5pjAA1Dsb45YaBJtpeYZPYd7JSVinH4juZRKMYTJgJoQGPm9m+4xSkqilN9kR'
    'eqTbl/3Sww0TJViYF2qF0G827iu8yDxAWdnQEt/2pijaYm7ljtvbBwW9vaeALDWQyhBR2GW3h3hsZlFrHkzLNzTc9vj6aIf7Yl5j'
    'gspxGqUlg2za64eDAopg2uEuq1+FHWIln9SdtifKTidHt+5w3p83nCZJXptbhAlrrac1Cz1+4w4bdKN9TuLhjUL0V2FzA+Ukp2PJ'
    'WTeorq/frz3cwP8BJN8eDUCzfLnTyiZaKFz4xIlweNuemlZPdXMSj8uXuhodKbXOfI9YEr25n10FCkvyDqllXvL54IJVrma2GKV1'
    'v4Tu7C6pmdtw5hd+EfMrYl0ZRlCheNwgQoEwlNYxFO2p6iZtDnVQkgzTUvvCo6ZizlYhXDPwx1o2Fhdp3S+qgvY2qqJKtZou1z8H'
    'Ws4zGS5VvhQyW8lDM3Ugj3wJbGlAeW7RA1ksMJySmLI2yZaossGmuFUiOsZowqiFV+Ng1K+fDjDqSn6imcZb67XWg4e1B58jka/7'
    '3l32aw84NIS70Jy1dS/VFs1fjBh1tP10f9d7tbv9zFvzjo4OfzlyFMwPReP00nPg+Uwxv5okGamK+qskq4d5yerh+/NOEcsrka5c'
    'gaBZtB9luIQjvgB6fOFKeWfq3QFVlHVWGHnlYfvpOYj5F231Ls/T0mlyCtubX9DA+ToscdENPNRNclLK53rZm1pjL1Ordb+Ip5Xs'
    '8f8/e+/a28a1JQp+z6/YdnJC8pikSD1sRYpsyLKc+Ma23JISd1pR20WyJFVMsdhVlGQdhY2e+dDAHQy6ge4GLnDRwJkH0Pdi7gAD'
    'zEXjzuf7U/IHpn/CrMd+164iJTnn5CQTRxJZtffa7/Xa6zGV67KPJ4wum3tRJs8ytDHRj2/NVJK4vqgEdwc9z8dfBqY3QMYk+trf'
    'lZ6DmGARXXfQ3HXEGXzbQKnQ2dCkZ4E+Qg2TxRe3SJYM4tzMBJa/ql7TRYfoVBAsedvgr8dimGjdL0zlfZzEZYdQBamX4i1XOp0w'
    '8zM3oXNRcASHV/M1opJP5JnT7E7p3AW50Ma6DaQNEvRppI2niqCkBKB5qm6360xoSFxwiO/9jsNt0+62eCZ7Su/zlAa6p8fK/i9A'
    'sChd/CjO83q33VkND0qG0Zlji5VLPRXDDHdVNjrf6tj1k3464hPhbUrG1mZKOy4i0sIqYn0ZgeSqIIcFR1jc0XY7K/cZMh/+lyAw'
    'w1mO3qH9IyZwjTNDbEb2yyubEcJMqErMru6Tc1znxon6xAbFnGuISUZpJrqrWu7ksb/K0uMM9pqLx8fyKSFLlaJMziVRhzLmu4h1'
    '1fJpkNiQC5GUZ4qE48fSs1pALVQJkMtKTrxmlNlj2xvH8YAuaPXAcnx0E61Ht1OkUIqir4dp+S2UIaXbZ1oYB7ue011jhsEhDm1R'
    'IerjIMKYTC1MFsHmGvZQP2WdkMXV+U4WIrZi99UKbEXKYkOvQB/VOnyBqUSQcu2VnutVxBb3LWZgaoMbJGiGmN1Cb7I6h96kXDJy'
    'urkq1QA3YoBCw1pbi44menTSHX0NYyDLewx1kLreySxsNAWdU+cobYLH4lm6b0e/QQzZql5d3cubHKbFwmFaVcA9bmY1pDyxZDpH'
    'XWJ1aTaRWrSI1CjKMrJW5dGIFHfGBEbSfrCy7sKOzqOJxmDysLAUrtAZf/NVCYDXHG5vUeGDMPaYZy6/P8snyREGmpD5kuWLyvki'
    'fZNF+fGJPYHReSvBC5xomAdUBEslBwpwr5a4umXarnZgqdBSuES50fFmnm7m5ukS4aRyJc8tyak/gvysF+hVt1yGsvVf3Q9E468x'
    '4+cpZsi68nedLkTvgZUfzsNc3kDZVi61zFC1dZVor0hUpzO38i0kyhQGvEYmMHj8zya4o4vDMrST6dvTNJ3EFt90xN+vSkTZ9fl0'
    'pnPgg8LRpzrxaDCfHoF7j0ZQsLOU4m5wlnF0PI6SV1TQIbMgX86jmet8VtTMBWa2WHFxtVgxrFOX0vvmME8pY5aYTHLdR0xXhGER'
    '0uGABgUCWno2CI3LqjSXyrFz04GtzD+wjz76xWgoN7e2tvf2nj1+9vzZ/re/KPWkjJaDym+B1oQZ8rt/9ODRvMXXMkBG0hIRnVw3'
    '7uJRJ4yB3bx7KPc6im5rwvz3cUepfzTWWFNvIvznvVzkt0Z9YtQA6g0bY6jWJMmQmabokKysNNUPyHIrDbesbCFU9kFHl0XaYsbx'
    '8dHRkf2mpYCIj+NV/Oe8XNIve72eekPIXkP8OPrss/sGJr1s5ekRtUk9697/rNld6cieLZqecdljotjBskurZsTHS9Zi2JPaO152'
    '3vTxn3qZJb0e6lh4JZ0lBBECRG756uPOCv5TuHP2HlGIEiPwBJAjTrON0rQyDXoQQHVI1qIBzkOH/gG2UxPrlb5e7+ie6aqs8TmB'
    'fcyT2Jyv8CTqwbTOWVgugjFkkD0N7f7GDbquLUyctZHHdZ42r9kQXT2o2caTNm91pUr3eioxxOyeLlv62hu0G5QKP16M8N/csNIx'
    'po9mU8+bzvjSNWeceH50iroq8iadJv1rr65YnKlKxBePk0gsiNdRdvpzyXBQRp5y7Gs5WQJ0t9Ito0yLy/i6hDIt9hcXu1EJcVpa'
    'Xlxd7FQRp26n2V2Fn2Wc5G41cXLKLq6UEad4ddDvr5bQpx7sodUy+nQ/XomXV0tI1Gr0oGNIlE9K4u6qmT+PmizeX+yYKfKoCZzN'
    'xc5qCUEBsPe7nXKUrVbVJSQeEVkB7nt1DryngQXxndwEwdPnLEz56fMacPCcXLRZNUtQnNyEszuHu0a3KffCnG2G0Zvc4dceR9TT'
    't0zhea4G8DFf2Eiy52D7pU7cWS3iKmCmxGP0j6/Hl7HIAQMmo4b44+Ml6FerB/2qYJnj7spiGW7qLnfjxX4Z1xwt3l+6X4KbFjuL'
    '8XIVboJzCdIlsJGLhJuWq3CTW3ZxuQw39VcHq0edEty0GkWdfqcEN6107ncedEpw02e91QfluGmx219cLeV0F1eXVss43X53ebGM'
    '2e12uqsMdjpzZSvxU+do+SiaBz/ZAIM4Sm6GEBpwF6gCRxUbcfCUXMB5apeyY7QpZ3fSUvCprXGNZku4Md70NxpOKcpS0z4bSDna'
    '6qzCMS+irSeX+TB+D1wWKiHJRoRDc4tzePY5hm94iD6J7CUh5sRCaPcv4651u5ctBL1xF5qJRwONhVyl53N6iV4bRfVnQLaqbsCV'
    'q6pa0ybPBWmveMnWWYpPpbYbNpb9prvCb+bvmTym1+mVv3C78eAMSrxIiZP/mbDFZvQZda91St3buNuFwf+2ObPE2hoHi52npH2t'
    'aN8doE10YTkjlTcn+B4XTjquYKinozjLZaMD2Spm8cXvyrf1t02rs1ZvKntS1QsxtVTbKm89O6sOXUX3H21J+ZpM9YPXwT5qfAHR'
    'vFYd9tsFdDOXSv7BvApoS6NdstyVXZxbazPnkOeGN3M6UARfXG52O4sszRVG5mwguiKRiEr8fIRnb65kBzfujjDq0hCmxNeMuRe0'
    'aEjhn5wykFk8jN7HRaLggiTr1nlBDjHaNnayGuRyAaSzNJzfaxxl0XEWjU/EIDk9/QOtkr8ItOda0IHi8bSNCfBma93Bb/IVvsn9'
    'OasAqjZ5c94K5mZT9aVbWC2Y2SfJqYgG30doR8B5UYCK5/k1hquP3z3n8fwdxbzg94IgG+5UrqxUbQ6Me29h/Po+xaXcBRbsJxMo'
    'zS0wcTcnw5CuzsHGSyuNgp2I61LUIQOBIuMi85idDYFi/kxQ0sfErXGXPHMg8rHiK/FU7fyj5H08UIwiXqIAh5/xwZfSnMYDxjac'
    '7+5b5Pyc23B/16LMSehH2QmY0gcJYZUTU+Dq1rO2Lpr1VdSxjzzmmujAYYflpCxvcNKO0uFQGSm6OICmk0+JM79mbinKR2GHfP2M'
    'Y1Tm/Wj4R6ZcPvI4S1rYK5S6TpEGBOx5pyUVTgfFCktVFYbHxQorVRXeD4sVHgRO4BbGhIBNw5bB0rhEkFvVH24mKTAF9yCESFG2'
    'DpsOitq//f6f/qeafySjHmzks0msD2KLbVbobGj7Ncs2kj4Oo0n8bb0F7wO2rGQJZyHt5ZX10lM8nX9waEeuu40MCor8hUXa7Pcx'
    'bngvGSKJHUejeIiC+A7FsPyg2bcl6qcTSjxq6zhLBj4axGfr9Ls1iU/HOHEtdjrKcRQUiWW5KbpHaANkHDJtc7H7lpWo1ZpxNnHM'
    '60POqJa/7yyPk2qvgiq/2E7QJK/cjSXoP+EYMDoGi+Qzaz5fz//Smzejg6pw+ii1n/aAWcqn60IrMXknC4NAY/kFBerVLp6LjgXq'
    'aokXsuX3hfbVQiNPBs22r2q/Fg1PbRveVW9retZ6ygzcBs35GK+01XLB+njRGWgeH3snyLgqL/nnAAr/IVyulhrX8YEqDxhQ8LTS'
    '53ZZucWU+SOXO2aVulwVpulDbHoJ6qfc8r8cC7j9Z/vPt8WrzS+2xf72i1fPN/e3fzF+unKVvsB8xdkl551X7lPjYeuYn1c47d4v'
    'cdot+oNoo12Ee0MKu9S0CCx7mDkG2XZcDmynH2VameSb7heMnQPOC7YvcTiiRAWhWwFCpxkui9gFfJLDDln+SOY6+SUsHgxbu0xI'
    'cPOd/nloG0JUSQ6c3cHOYRH62k5a5KQBtGxhed27oVs9un+06HO0hjUsTJg9MZjJ1nZNXJU4WFhxE7AcOyAUvZ2K/hDhyCYaEMZS'
    '9wB15vMXWAwII6+/2BR7MteIqA/io+hsOFFqDqWVMNNLny+Oo8IlJ09hYTlUeaWsLwgTe1u7z17tM477bvO7TfFaJvDrXcKXzbPJ'
    'CexlDHpaC7g6QCPrHjlVob9eZQnUsYJ/+UT1QXjyA8ykTc61sZl/QdU1eoaiSKSFIKmuoI+hg0KiULN1X8tDvqge7p63po8fbwmO'
    'TVi9jr1ev2hMg/80LuLuLmuUpYfvtfgiwauVYXVzp7LQVcEIVBrjuVIy5RWEIc4C27cK+qCjI3n76166Rtm7hZdpklUDHmGJEltD'
    '3/pkcjZI0mpwOZcJWQcU7oX/tP5nZoQiT1KyTUyBpGmoFd+gTrmE5OU238mMhw3JyvwJjtuY8jtYFG/x+5R7c9AUxNE3xSg+g0M+'
    'FHX0KZFYFp6mAs5zFpEyNodC8QBV1RqsfZDRNABOIx9+hIxeuxRKMWtS/YGAHRVnrHnnLUhBPum2+0BN98ZdOPXaCsBI/EixkJXi'
    'T92OL0VIxFXABCFJw0QrqOiAfEfhHFu/S0kv4zgqsiMTxqhdvx4wjv40X41elMeDFtttz1E8InrELciUoAob4wTN3VGZpbbVu9Sj'
    'zuPh0Y0GPciiI+lIW+LZdT14StK+8eCsVXD5FNYzhCjnLNBlqkg4ILX1cpLLfuhSIbl0v9Lhz/b3KyiVHT7hMyV3+yNZstiwj6Mo'
    'skmzppBwjo8xWHl6ljMzQ+yJLf8TXhhgnk0OITPzREvCqk91kLwGB137Mh6ex5OkHzkT4IcqcFDCdI5+hA43y0yr1atdAkJupvLV'
    'qxqIvQPvByJNGonMuL74S7t87bG7qOLWPbcCLV1oV/FANIJFW0Vra8fn7LaNma7d6eLBCR2R63XIRm/mvq1leetcaz9RGH4QBuWm'
    'LIcoY1DYXCgc3e2zLB1j2l9OUdWUYZWjCSKcpuBFF0PMO0Eks+rYWoxrydFl9tWLdTDzGLpwA0eRAFaSCifwImtYCoEmrtt24STI'
    'I7kaRLCFPVy4PF0qSiXX3m3B7oaPQNWu5puu8uAfthC+dLP1K0MnNnZww5KWSKhztlsqsJfQW30PT4Ok9eNlkvtXqev8+D8WH6n9'
    '4pPhqWDxDE4cZla1ajTJMEMoA66q84XyW/hgoWOk8QTrxP14uczJEJX8AResbqMp43kzw+z6UjWqJ1p2rPR0eD1zN361X1jhdC2X'
    '7deb9VDbAgX7JHWHGQbhHJ9l42HcWL9RK2sUb/6EEsNaxunLy8vzw3N4bG1nrvxh5oEQOHNVA51zSsiX91o7xO7HB5kaJfVY9TFw'
    '/bXrl3VmaWlpfmDVBD6wzU1Yu7mhK2HE2QbzHqvuzZr7IJMzk1257fyoBv5gM+Q0+EHmSAmsqjLFttZh3KRmDnUymBwdSmVjlKxi'
    'aQUQD2SgMyuIXbBR1t+VcGpSi2fZ3nXE/ZmUXoGsIra+Bti52dBGuYuhqOuaLwoH1psxzDLGMaAz6qyXqm5u0JaNb4tKiAJxm082'
    'XywIfi1PpX+tngZIQ7Griudh66f5gVvo+TpKGB/MLZVMPrgPoGfyQd5E1eTD8DCk3p1L9u6c/nKsAXZebrfQFmBXfLH9cnt3c39n'
    '9xeU/AQWEde7Kkz3g2IClM861wvTXR2iW51VILIqGnc4Enc4CpqpNjvG9ko4/JwH5wNE3UZoaB8ZDrZYCKJpz8V8uRrsyGAkCpLR'
    'AZNTaJu+Ocu4yGqFULiyilCe3WUZy9O9eJBUsKpv3A8ZekNhnj9SyE+1ljSajhO+Tqs3lq8ftzw4yLWjJLNy4diqCGunHSWx/Vo3'
    'ZmwYdCFtiTefAYLPv3gtLBUbUNk79AOEFWVxZD9zsnk4PNHtQg6Gbfca69UhBx84hndhG4+ZFn9ZzHVg96NmdbjO6ojkd9SE3gZo'
    'FG171wUidtp2QOinltu7w51TGbj3RG930hc4Dl/tleAKSee7AMziG14tpTyYK4A445Jd7sMQ70GUhY9GKvKBHWe6PBxwkTsmEcdB'
    '7NeiIaGoqtY0q85Zsa+cbWrFolwxbftXN4EA8ze/yFnBmw6MXk6fQhovxEeLBX3WUsMqG9iO7gbqFC1htCmVPT/HLSl3XVXbzXTW'
    'Zzn5PKhUKurmWFVfVEAvhhXQIQliFsrXiH2VEPty4DCpQEPk59WD0/IOo/bDH/L88rrMtwxl2XaCMo4jwHvIdo4EX94K8X1GSdxc'
    'R/fkNWVH2mZYbpxtPSFla+fNpQdsmB774QUKEX05r7mQic11bxcXF1XSYWdh7q8UE96tFkahaCuyZsXWV+fjHxbn5x4+/uyzzwr9'
    'ul/olsXblQUSZqWKN+gHpWMumtq1OK7wXBu3h5ZO1d0hNc38ayBCi+o2qkTB6kRlS4U8Yg6PKdncVY/98pjfj+MO/lsvywrj9QjG'
    'bPvdVRMW6uWizRd5kCh/ejkD9vGDBw/K606yFCPVlq8LXY44tceXhHdL2GUdbarX86yhzbVYqcWiEwOZ5IRgDOTOtWIgly49Hc/y'
    '6Mc3yqr00ecLnIb28wUK0sKZafE8Pvz8pPvwk6tAfnCZ1zaYHxzAdCWQMdSekSh8Kv77fxOfXDm5taecstl7Ku5sbIiueCRqeU2g'
    'anH6+cJYNkTJaKExzPiMCYXp6+cLPIgFytP7tpjHtz9McTDq+ZjTVofztb968hQzWpvs1iSXLiz8aWst5tLawCCf7G4+3RevN/e3'
    'd19s7n4lFsTWzvOdr3fF3rd7+9svfh3zwMmiaSre4PB398SGOPgIdRsJnK0akRsQi5Ayk+Aqaq/xkajvAPpJRtGwwW9PkMWvScMm'
    'eIQYZouRUE1yDzUxbRrIGJyJq2rIHCmuCx3aBTY9h62KwCXk3lJ/EC8VIS9GSx7kMWAKD/IreCTqi6NBCPJRr7ccxT7kpUCfL2N0'
    '6ybYCvK39EjUlzKC3ebpMLMR9wp9xtCknY4L+TiL45E7z1/gI1FfBixhAJvZiBeLkDsI2evzMV7jjLJ0UGtqyOqRqK8Y6LrPA2CP'
    'in3uFvrcO6OVdlYQHon6fbfLejZW4vv91Xkg59HwNB0587xHj0T9gQNb97m3FAXmuVOA3D+Js+zSgbxFj0R9NQQ5Xn0QrUYByJ2u'
    'B3kSyfUzkPeBI6h/5k2GgjxY7C2v9gOzsSL7fLj+0UfAowpS8e9N0Gp7Q12oPcOst2fDYROkuPOXZxyXrwbV1k0VgvkNbPYeJY8/'
    'ioYoSRgqMLg43bsc9akEOVQ/pnR5dQ7npAnKcTzZHsb48fHls0G91puM5K0D9aR1zi3UGo+A9kR5/jzJJ0AVj4+Hcb3GzkQwyEKP'
    'fJIUT574RerpqCnyZIjiqOy/7FtgeHfupKQYnWB6ODFEmrw3STOQ89sA+9kkPq3X8iPZc9XnQL+QFneJFndqSA9FH91y69gysl+l'
    'k7bOLzfH4+Hlfvpk5wU/SuA43OExNER+kl7sp1E+qQebVaiJlvgsE6qX2Bn/HWuCa94s8rQXJ5KnjfpSbPnTT8Uds8facn81dBQx'
    'JcLQFSjg5jw6jwcw4/9ub+dlexxlwG44033sT3etIX74QdSupjXJBYrSPU2wVRewVmGTcwn9gCADxaCtj5D9BZvedOBmsQBDYHgj'
    'EXG31RKQCretxoRtoPF/eiTyiwR6sEtRLfejntgAHq+m1ggmw3tfr2VycRWsdByPaBFfQ78y4N7fUdLUekOpJCdnmb4RCZ6cO7PO'
    'W2kTNHqz6HLJb7XcpYtdvdCli1w4k2WoCs5jC4C0RgSl1mifR8hhbFg9CjQiT/JujI4bX2TJQB/uV6w9lN9LWyUUA03TNRm0SpJI'
    'W4o+AvcCSDQ1XA+9HMS1l6/HLdpCZbTbljc2aoCXmRxwN2a1xmgfy/IC46d2MhrF2Zf7L55jmzSFNk/ZPkqz7QiWrC82Hjo7Cz38'
    'rRb7WQzjl40CrSHkqvYR+qYTiUHPQ2zH7g+8rIl7ol480HT++m0YGuBYqfSOByxuWZDtEbz9nKR5amzjLjfD8RnuCprhjbuWBPrJ'
    'VZz3vwR5rN5vA3FvTNfvgoCGEB4SnId2AeINGlP5/q1pPx1RgBRoHdYEZ0mEhkIDWS/sT3d3KlxIKxOBhDsabOFNUx3aYQG54e8I'
    'XdnaDmh6s1F9upQ+HYryXHJNeDqrZvFcrn8kwgdzA+EZ4HyDsuFtsGQ04N1FK41LHkDtiiLT94a2GcrksbGSqm1wM7ie614p1T4X'
    '0NybKcaPSI+Bq4mToXBLA7ZoTexuf/Ns79nOS0EaB4H7loHR5mjD2U1g89drjYPOYXuSJaekZ7BUFYwFY2CIqsdQ83K41srGUnPu'
    'B2tlY6m9TF0aqE8TUyN3TxEvJHdUNUMGjBiRl5wUKMnRpXWMG2WsVTnO/GB7xfAADEhzDDZlpbkC1PLEmRhiU8Q+EGoBswHsm6A6'
    'GK7oG7wvm6QEXSTAQhAEiuH0d/9ZEJg12hSy1Uf27sByhNMbhTO8NYxhFS0WeX6hQVSJDN7qZfFpeh77NH+uYkZYWL8BLz2TKAe2'
    'n6xOc4IKHXYR3RlhvlIUr6FDZ9FwTS4b8LWI9NhxRAArF59jAAyOU8VetPP43WrE91dnUH2PzkiabQ6H9ZoT7LjNk4KfGYNqOtnD'
    '3dmTc1hvND489sO9XGQSlYZ+vgFYHabxaNpOc709ArwTU742ensS5frOUV8s2lndYApkbWLYx4QqCE2p0g0ReIh4ScGtrTuiikfB'
    'PO5ikJwbiQSRXYC50Gtjl/Mx7ZZDETTJsAv/7hlGM0S4iw4ovv7ccPiWIkvqkQ2kGh7RUDBpfpJRHmeTx2S9WseURvyYBBZiBOSo'
    'p9atvj4bpAoWW3t7ay6q70VAUvyTQeplODVzHw3UTtCMbA/n5TSpeM2Sprm6ltOK0Lx1tgDo4nRMRKCddfcA4O2Bw0Kp1tdt2ZJP'
    'FKzWndCR0m16xLS2rkQ5FuSCpd5Sf2Qgbppufcbso+gZKzsGy3c/uarcXVO9s+6u69rzxbhQG9ncxnxypU/BVF9DqYeaWZqaypWR'
    'QoQXKuRmlmH6Zte5v1pic0F1o90is1T+TeGUW11jAcJrDb/fIpWBw7Ib5xOcbnNEMqTzmCfgo7oralHBgmANMIhei2h0KeL3ST5B'
    'VGiDg4Obi6MsPRVAwljbcB3kfE3qQj3ytUxJLhLaRPAsGg6BEmL4xXTUSkfDy7bYlLogB0+cnsl+ArxRzNEncNdGAm/NzgAz1XLG'
    'F2cAd8jc0EObQ8qlHmsAM9o2GoQy5uTafMcMzkOID6b5gCn4CnOY8jTxBDUFSLUCJ1AxgOLiBDiR+D2w/X0gB7AdRnjXN1C8Ylsr'
    'mIzGBKi3+YKXiDXk7GoNff4dBjDXerciV+VJEtbOtAeLzY9SAYJawgNRpHpO1pAPkKu5mTawB7+a+0ZNvvd3N7e+evbyi1/HyJHi'
    'KwUnyGfBqwg+77tWKYkvvYp37O+OEg5vxQP3D6o86seQnNj1q7V4eM3h1q6+4ChANrKjMwgQFH/857//f/+fvzfIFqEj8WB3KNQB'
    'IU0gSyqQElGuBSTh3gJwlaMjPFySCXE6YIjM5mDAQDG2McECmBhLUgo1FMdiXrqChS06Ql20mH6K7Q7kdRvjAOM0YUiNeo2a5ynC'
    '5AsUadnlQG0E9IG6wajo2j1xlOR2sXpsXaK4c2308Yg6L/tDlWHjx7/9BwHTQX/7J9HomB8NYEwT/ojFtGjH4xAgsJ1lGfR7HziT'
    'eGKJfkBd4T0ND11v8njSVsqlmik2wjDhKPTXarBloH3MIIR/6PoTe4EP5Cd4xt3BZ/ITKwUOoLlDxXQjTLWpCu1vUJPFheRh+sUV'
    '44x78esRUUbfPgVfqa1OlyrW1MvUAbgu9syr65eGtofSxby+YqmyvpbUKu/yr4V2yYCAXz7b29/Z/ZYwVT6KxoDjkJVRahKYGLyw'
    'HQC/eUmJ20CKODr6NRnS4AS9+Wr72zevdrefPvtzlPKADzoBBNSCE2qVebH550og2RBLIIYQ8qCE90OMoLDU0ROcY+Q2ia6tQ4JA'
    '92QRR21PhoWwg1EjAfgDN3O+pZ7VmWDtRz1LIXRHV7GPlIJ2riBRLLkncCwKQLio0mVQFanZQNz09Yg+DywcxdGTNsTBoXzGzV8D'
    '5xuET7Da47P8pH5Fp3tNDPXpxe9sYrGG05gjKRhw9DacmH14UR82pJKdCINdW2NXRR70lHGj0ogP9W0dM3V6lO9ivILz98Q9nigA'
    'Tm7W9YWDv4xav+u0PjtcOE6atTdSl4qKElxePUts2aCezRJKoG2WRg4Oi3YMTKqexIMznK1BOqrxtT4ODY7tiDxdkFGgvag2olm9'
    'iLceShb47oB+q9loie6hWemTKD+RRCtvn0bj+nDj4ZCW5V5trXaP1R2N9vdpMqrXfjBqHt0GSDrqc5uBwWzjB2fCuQdqE+RrZJ7Z'
    'HqUXuKrUeJO7YpbQ6fRDfSwbeoq5QA7UP657I9SFZ5icwCoUrjYIVKOwJlPvbH8R8/H2zvZPcRpxn4ob71QePq/FbbalAgG73ePD'
    '0FjhywT1KJf2rTjO0uOzZDjY4xyhM+7lTxjCzGv5GSBa6ji0ktFRCnAKWr2ZENLhoIXJK6Cyc2/++SA5V5fOVDA+HU8u7z5khCgi'
    'dEIj9p+0QqgyH0Kpzxeg2sM5mh2R41OxWaqKJZ6n0WCLec9XUM67UqH7tsAy3HzCtW2Cu/PdNbV2vzqY7vGwqQr8qlIr0zRgKYlj'
    'UZIrTkUBOUj8rsiNX6ls2V6mQk6BuARi8nkveyinD3VcrBNCLwdMf9gn9RrzUZPkNBaX6Rmj5Eu6TiSK1baW2jcDQiYN1UmwyDHM'
    'glIXHrTbbRrLIRKzGM+lIaI0yqZIGr5VRjyc79okHrp3JjR6dL6r6feKlCaD9xqlGkIBP8m61fCAhAlpXI+F25PctOWYaEhhjyZf'
    '2mRYySrQecLPRtFYv/vwG3mCPrnyupJMeXJtsPaa4qhauDJ3H35yNSgx+7ff7ENZ+ebgsCmuTmAd12qLrUFyDNJ88zQZnU1i82Da'
    'uE4HaGpsHmTKRM4C8VZPm29ZQpwjoRQ8QXXC1s9gZd3VAroZDxvrZs/btyDyzbRRPL0FJHJj1pTrIMaaeaYNagvxtFcExD/pzuVL'
    'qMANOVNHGyG3dXI+34GCj4ETxclOh63cRFzHgjaP6+sFlJTLJV0SVcoHo0wtWWFj1HjHA9AgiM5UfTrq5eN1lX0KZ9LeK1C8dLNY'
    '2xC2HO04dVX/pU71p4xMZtysG+RjFiPBlUgsvZ2881B6O777UGiMSkSDgXltMfOziA++F5ojhtEcmhtLeBQQD0qR3Wzuge58fd6D'
    'pr+mMBwZkCDWvSe6fH+sro3D2IuKuK+vjcJuyzwV0Bp1ih7U1qXUAnMvpIJMipFoP0CKhtugGQnyeVgwfXRNydSGxlLJTOGz0VAj'
    'JP6HRgR8SHI6Bsb9+dYeByBiJSG+a+iuw4ZQ3bYmkGQt7IsUscxQCTJrHnBNnsDXuoLRdLpu738o8WoeVGyYW2xR1gqgVuyFnrSB'
    'wZh4YgYSp+G9FiE9FBnsh3yMreuua+LZKkzLZqTFxsh8FLCw+rrGX6l/Dlh3Tw/ou1HS3hSvmrkMIVd5v6b30G4M/URbKX1WiI5e'
    'JJMTXn+dSTW3FMcXr65PbGWtD73CqLD+wywvtqTWlj7/wRdWTeE8C0tMPnr/CjaOnolxsSxZRwcEMI1U8TYchYx0OBS9eHKBpnG4'
    'xLmUDPH9Hr2uB6i4wiCbWYZJFS7grybje4zAXlxi/njqgEFhlr1wfjacaLSLuq9ko9MU32901m2cCGhQkB+srvkCKnHLkmI0xUsm'
    'q+aRJSD2EUnCm+iyjTJ0/YpLrL241502642Nh0iP6X395b0uIPUERtxhLgHJTJ1uMzdetLrr2UPoXNZqmRsH+bq/8RJe9/F137zm'
    'vcFdPcgOYedxHw/6hw3sFzyDjxv06V4XPsOve121Q+iqwpR6EU1OAMG/r5vih031Gr7aOweZEOiKnMoL2FxxPfn8Be7b7z9/2bDO'
    'JD799FN8in9kVxOrq98fmtHwkkmNG2ld+Rw3SdeqK8PGFcm9e+vfw49tbIDtyYbqycMN6g4OIDk8+B4G8JAmIsGRQaOVrdIFFzWq'
    'e4mN+g1WQJAIvaTnzkxKFRUDCbCz1jGxxB46Sbi756WczbkxMJ0Xgm+kevwKUj2IcAbnElcOneEjrn0MHPSaTk6IZSJwB92W4mH1'
    '5sX37Tc5DBJYQvuqQLegXuI9W3amjba4Jje+n45lG+ZBGQzLxmdaJkJIA6tNb85nsevMBaJO0iYpDpdnyxRtIxFILG8AkImf8RYr'
    'autQF4PaTlvg5F4gf06zIUVwA9QRxT0pYz4hQ0nB0PxpvbbLOlxWJymeQNoAEFcwgbGqLj8S3waLEXVQmqtcmnQpHRcm17nUXnFO'
    'V5AOqOtCBVTaK7JuGZZbURp9pWXxnh/wSkuK80VuxWKdA5dMzg09oBzsgt1wU/ClBrEDkfT0M0I0idaugQL1YJ/v6plFt8/aENV1'
    'jdBd+1DdSBvOoHAzLcTZeICyHcaaeBmd28+2TqJsP4v67+LMfvw6zYC7PI630jMOGCFCCl/XsKX24+//b2UJOcDrovOQ7Bk4s1vA'
    'k+xJqb6AKa8pYchzEQ/xIF0ko0F6gdUYfKKM+kinC2XQbg7E/UmqxF4lfcnFGUXnyXEEAwLuMRn3UsyISPmcSFhzq0Ldk3hUd1Gp'
    'PTv/6d8LGCnm1kLRewwPY7SnTG2drqhvTbLhvW8a2k6u0eY7kUq4tHH6BLxWbktTxEp5Cuww8a3JiG4Q+PTSfR9NvkJWyhjGN9La'
    '1wmuLDMtYFzZuHjivEWLrZJX8xhvmRrKfKsE2GxLLlN+hhlXVQszXMutNkrhzPAuN+tVUf/H//k/o/mYWQhlQEZwC4/ZSIxPQBlU'
    'OBWOXY15LbkZ+63ncu4XNaiOyWRJk2gsP/SMeAwOGCp9JuEg3L/GtHmEmi+N5+l7CZBd3PHMawxxWzxGE3U4ulvDBHYHvnVvj0Yx'
    '1VBtV9QAgsbWWWtME/JkkqNzxPLib+TlHHtJUNPmSpaq7BwdwbZR/UKYbY61JX4rOu3lRb9HxDGpTlFxBN6yqk+Yg5KYkJbhSTyc'
    'RKYSwWg5HVCM41CyYY8v8eYcIzhZEJpApk8AJVJwivw0BUaupriwX4vt09Odra/3xIudJ9u/jiF7CP8pHv0Qrj9SLxw0r58WcI5+'
    'oz13KA7CJqFetHMHLEpnXBE0QspQE2Mk+DzedA76QQ0WSIfpxkyqYQGYk2q4wGcQDCocrF1JJmbOq9LncGDX36WAjui+wGJkj35X'
    '6X7FA8ea6qbBsLJQtYH1PW0YqSTIB6jOq/gX2O5vMa4qXS38hnVNRoeFzMe//f7v/i/RiwbHaOk85ojRTZD6YAaSCQbUFZxhcAmY'
    'Nuj4ILcjB1C1mYOgYnb/6YHhxemr1Iyl6DA0Ic1Y13gSoi8E3oRAd7hy+w32EB9llvug+wJltHiiqimP/pLGOjVY46ZY6sBcGc7e'
    'TNW7+JI4UWDWUHCSiRIomamcLZ6mZXt+qOzM6YnfJ5MWFrWnCL+bGcJvc08QFQ7Mj/c8PD3hluTsLPuzQ5vR5lps6136HHCU/zB7'
    'p2ohZ+wX2fkPtUYVc1a9LtYkvkFvLHLDYnU8Wt5c4m9LAf9mEGOQyksUER+jR2Be12v7pofK2eKbqZIhfi2cAvAJ+zsvxFfb3z7e'
    '2dx9Iva+3Nnd3/p6f+/X4+mT97eiMbDirL9Dn7R1RGPJALlhEG+ySf8MdT/4PouBoFLe5I+kafRXj9/s7rxWIQgPam9rTUA0zdoi'
    '/CzBzzL8rMDPffh5AD+r8PMZ/HTgpwU/G7Xm1XANJKT/UmterNUu0BR9sTY9xDBtB/gGGAjzprtSmzZrfwX1LuAH6HgNY3ZP4OcS'
    'fs7gJ4GfFH7G8HMAP4fw8913NQMPBpv7ACMoBA9rA/g5gp9j+DmBn+/h5x38DOFnvda8W7vbrP34t/9qQds7STAWhu45DBWYjzXU'
    'pALc30G99/DTh59z+IGR1Ebwcwo/+K8NPwt23ybZ0OmbBQzfbw4nVa/Nuwc1q4JbiNvQzw45ap1juLknFz23bQbRT/brHGRG9VKq'
    'lvoc4AG5LPfJV5IEzrDxVDssnyP4kmfZGOwnbudRPx7ypo5v33rA5NEdtKUMI3PGCuqQ9y1bRin8qR6wotSb3hJ7R11JKz7zQpwm'
    'jN4819UrFHQvXqGX8Iw0gg5yAFKTm6hM/VZfvXIiMyE4owkXso5559u25f09zHek1otKNyTnySOBpTEGHlIx2G/3YSM36B1fDfHO'
    'bjhlcjyeTiE+sG6paOiWwVPTsG0cgZt7ojcEVCAvASS838F/dBONf9bkKz/wjwuI+AsaTruNaXnypgX+kGxAYG6UTaEb1grmHMqi'
    'NeE7HY6KCipr/EDp1nh4lt99eE+Wr6kO4VIErTM9EFCOJQoyYpTRsFTrFXVUR9WI56gSD5LJ3Yc//vPf2UXfltgzZir5YyN8Ng36'
    'sc7nu96M06n4dl7/d72wgeGMY2vffw/T9N3ZeI0M9uuUzxjD0jfIlZCwhU1kaW5zkLOiCbrdo0RVp5se2uu28f8LulO6ms6LDN7p'
    'jUumYhd2WCqplmOoB+8OG0J/tE6dfsaHRO0EvQbwR/ICuhuEgQpIaXs4N1raHhYQ07se4SaDTlRjdCb9+9Ek3+l9Lz0IYaL1uU17'
    '38f9iRd6hoM1bchKj7B0G4M3wV+3IKUbEbrkp59S0QtZ5YKQ4brXDyBRhRpw+t1i8PAZFeOoYoGVsu9C4QMUVeuCVQ9RR4sL5pSd'
    '1zS8aBzO8w2giRbwsBH31+7xZ8L6dHFE48NXMKbkKImzmnkp+6rsA8luJ8pbats6xKNoNO7H45OrhKtImPfHv/tXhOAG6SvgwV6L'
    'e3HXgqT6xahTLIhaw4/yJ/U2zgAa2EXlqkNEh0we7+lFs5A/G3HCUcf3bntNYcbMWz1gra2uiAgVedhve1iC/xxymgwMW2S4fKbH'
    '80m0mtDHlkSrFNcF7MeBrXIi7CqwVTKYwYSZFlBDVbAxfbsrxQ7s/F2LCt3lW7osztXNNp7wfnraS0YRzsaPf/Mvb9lVRovcIe+h'
    'IhML+Jt90MlICKDa/S/6y0OBQXqB0aRhb0WjwTCW898ko4rCEjlllJ86tPnseIQ37OoQUdAWbJ2GSKZduB8Pajg3WYpiiRRAmNOv'
    'vYgnUe0QDlB/eAbifz1GjN+w71riNgaAhM4/iY+isyFlEEC1SDp+laXj6DhSF7C2jeFX5BUZG75H0NGjKD94+OIwYZE2KudxliUD'
    'jmqHcbetrUi8z5psoklkDqHhX3pA/Bs+oQ/0CJg1fAB/sFdTbayAjjeqKd22jtKzQWFs9gylhF1K8b3qZ7hVz9RWtfqmL6w0kIfk'
    'U+QAOlAvkVSq5tlAHei32ybRTVWGRSXodEGmKpNh5pO03H3mgQlgApL37c0djMIwe3/fCpsY7Vj4oEoRrDgHPuMHMod0ZLEDaNuL'
    'ah0FZ3UCO2Q4gaGb7XEnsD2CC/gB149GZOyk/B4zb/bhO+HaLvzzPwrTaIY9QsORAeOPvPbrulr84vnO483nWk8onjzbe7W5v/Xl'
    '9i7RIul3mwOHkw366SAeCDIW+VLEk377V3YbiScYb8HU7rEDstyGhtmu+gHSc30ShfRGcBwXpjzIR8ftU+jJV8z8K6EPOkrlFD2y'
    'rBOHE8EwmDQRIicLY80rgQTiMku2Ka/UaHDoa/yAdk9Sg8GkiT7xU2wMn+FffhKeBfLdtqKEPaG4AZMsOT6OM2wWMQqFb7scIz1I'
    'RgL4ZkpLuaAzWwIB7MdjZVNIFvl5w5EwJtGxjfP5klWi/UdteIsChc1R16kGLtOzl6++3idXAv1of/vP9zd3tzdBeqDovUGw1t2u'
    'NBHM1WW0dO9pkO1gMjI2rQHeR5lq9duRZXrm+ur+Gq9Fnu98/UTsfftyS3wqHm9uffX1q1/P2NPTU4poNIqO40HrCDPvZGIEOzin'
    'ENBncHbwPp7iPfbfnY1zeRVCk/bm6c7zJ9u7b7589nLfJGbC2iDl7oziJxnbHwBiPMnXxIH9TH8WLfEqznKM4Fg7VClrJIwnwKb3'
    '0veYmkbDUM/8sl+k6TGIqYU2vefyO3/1YSRbw/RsQJlwdH1+pqvzV2HVL1wpUAk0cbBV9ShkpdFAWifnaBoRymRxjeQlfeqrH9NR'
    '2130VS9eRajAId9Pivo9lt8tz6BipW0Z41FVUjEfoZK2ei/YfZQywv28ha22CNlaiS7CnV2fAUr2pcV2LgCufxL331FnSwcyL8xR'
    'OokLMnn59ADV3XlJSp2dp09ZY5p/zbbNUEFd8fdzZjufxBOyKX5KxyyfcV1DjbXQ2+D6t0XBLXirlgI3Q6XDspTQlGZ5o3LquXVG'
    'PXlNaSRex7C7RjIQqURDdCbXyTSHaDnGchXShQCfnhrJLD2NHwNrQFqrte++Q5Ehx3uLe6JubKgRyOYxdkszYLXXCebAgXX9zdd7'
    '27svN19s/4bW968dXRB3SGolD+gMXem8Wv/2+3/8H4RCb999xx61ucRJa06HTCPffVeswdipAFpiQBvyDNCFGiWQbVw5f8fDtbgJ'
    'EtpwEziKTmv+6BIoV5dAbz9nt0GlzoTtwRsDXQQ/uSpBbsQxMl5Dhau0e+OElXeVjw/fxCFItjXHmvXaJ1dc0QQRqi0cN+/CVrnb'
    'AJxK90D6Goj7RtdQ6hJK+DmuHPAIedbZK0GNY4kIy4asC0CDgKH5wMcTVM/Mg3WKaMofBI8AuuPZVfr9gBIzuhFoKcrJAtC09xjT'
    'iMbcRVudIT0m3uw9fYOJTgPZr7iOGCfoMgKc7F+dJRlyL4Ak4EC/Q2Nk6HstmJwqmOTHc7LiRT+w9o/b17uHRq+DCWzQ/Goy8sMu'
    '/fg3/1JbpxeAUxVpJR806ojPB6AFWnQRJYBqjjbHydMY6WxtIRonCzhQeSjgZF4JENxOUszw92pnb7+mdegmhgPDydrf54blZx/n'
    '9B2lWWibbepEOJ13qzIAfWej944EvF50EXlMvKSQ7GYemyjMxv3yzqDdJ50OzFUj4GcCPEmWcVh7DMs+HIgRRnsckxrb2hJlAZ6d'
    'DGrV9anuUcIxxo0UW77a94przVyTka6svb9PfIxkKeqYRiJ84AxPxrkEb8zPQKshxmXuAyz9LUe4e8J4QS0YAIUnL1OZlMwfeaBF'
    'Lw59qXVyX3LqXvS6K+2qiRQr3LmmEpF5jtbKp7opr6UaRXbXHYg7Qxb/Ew9ncD851ZF3QdptxPUZcT1V/E6quY4LGRw2VfQuKbyR'
    't8164eazZpmhljRlr2mxnZepOcrsNcfBolVewp5z3KNeqjOhVHXF8WyMyNaoWhZqYSliYx3fRnhYiNRgh7bR3q1U0r6b9Yb5PCLb'
    '3D7ZOJSGoim/YIaOybiGBbfvYmO7cTS4pGlUazfi0Mkoj9XK2qi5/uDAR/POVEASGD8qvjLK7lhGAUPOBkZG8Mgd4jnfLznrtbCl'
    '6wlSyIHWOM/UP/6PBVFD4xEdueEd+SeeJkgFmN5Ll8WjZEihyfERSQfHMnUSTQGxiZTSgPwLU2Lnx5hvPMdsV5aLFrE35SKq9O8y'
    'B8NxZ5wU9r3luhiIjrcv9ZQRh9VDj9k4Y+sY7OerS6DyI+4uykVoMYPR12n0VAJH3ZY3JMyD1/V1VTUWtc5N0wpMaruSzgEEZ0KK'
    'CqVkw2MBYFFgemAYeJiIC5e55YD9brTH6bjeKDCmzDr8RTI2O2ErHbJLuw4bLxOT2D22HdCohBO31g2RgQEpRPK5M2AZqwNjLvjY'
    '5J2Pmd7Fl/WkYeuAidF6B3Qqgm32OkHJAyZOqnBrVgQJofqngsWyZuqdlk/sek02OlHOhzD7OqlOOLppQ7OHOmNMSI/DKnruRijG'
    'pLWMgPqlRktNPOX2gzXFzQ/LG9rwts0Y7HcOwYKEXPTO8L5VYC4npbjHu1i0x0WP/nZ+xGfKYC6usFHgA5SzN+CTbhvzheNeXDNY'
    'H7f3s70dtcObegDTpsxCt2gJ/L1h2pM04zF8rB9wuxh1TMZ0rgGiAAGBTAoWkNVWrDgDOONLl693n0ujpB2yyoLvdYRtR35gXV2Z'
    'DVPEExq1T7JYhckC4PxMzxWQAsaPLT4vLTxhZWOXMYQ7zW5Hbic5yzWGSoIPH2Dsfxafp++s/kPr/uEGDP4vQjL5qk/sCc73CsiY'
    'tCR2BCbhHbMLEbL60lfIhGxnXC2BSWEvyYEc2lgBASJutkTHclozk2v9IOhyXoRZ0pWAh3soEgLnSdAB1nDn3jai5QU0UJ3+DEu0'
    '+ti+ZF9rTkDM4xnZ0yjlU7E6y/vcOLpfM6ACH+wEzuTiPu+EU5SvCfQyYiB+AZw/KPDXHSfMph4CiNRZQrGY7OmViTTzI6Zr24ME'
    'lvYFF3Vjbdi1GjJ7Zn7ECQdLq3krkCunRYyj1GmqPsEum0RDGqA2vn02GpzlSMZQpXZKaO6vFzsdCUZG54/jEalyKbVV/TR5j0eN'
    '9tXCIImG6TGwCs4aOh3oNm0PSga8IKAR3uuVy4Coh2pobtnmlKsXiBkD+PyrsrvY+nJzd3Nrf3uXczFt7/7KbClG0fnLNDuNhsnv'
    'KB4M7NM4QxGnPtGJXmSoK7mVTKi7RjAjsVHvfpf/9rt6+7ePvmvAp08WmlYV/x4ljqBReVegu6Hjvub+rUp1CM42IIWsBSNr6dCG'
    'gai8MqiEHw42VLcQt0a+KXa5jjykpAqzB7X+QcIaEQbndkPxjarn6gBdaihgycbdvuoj6llLohhTCqDSPUNz6gQ8RGaW++bNNwXX'
    'DU22ZXyMAoK+QnoiUecWXrop12E2M3S2M5emeEdP04yiM2HTTWFTMxlakDJaFgOMDM6iYUuh6hZeqfDdLxbTofNEnWsDi8Mf0JDP'
    'a0PK7vjaDP1RmWWJBuXFcyZXXBxPTa2wLGbNtBOsWQ2LS1Fm9vQsl4zBXtKD5o7X3Th2Nc4Ry5Kz4NbcXV9YiKf2vtcDbwrrCLBe'
    'bgR9c0PpUpimeCTZfJDg9Vn4QJu2fzb3noWi7pa9o7esbaujcy6fnWK/sZa3YeCdksAo+CNIVglyL76PGcOwJFu7oBWRkssFpmIt'
    '76ewLx6KsjlRWxenJJzZkU4WRxzDkeDH4vbA/+RWxwKPZttGwQ7WwjX9RxUD23kcoTHtSUzpDshMq6SgGooruKtEZJUVrIllCX+k'
    'gh+rWKs0foJTPgFTK86ABVAHs5XNFX2EJgxeFSg9rBKdK7KK5wKz22jIDT+8IpVA9KlLaBUlnzSlz8A1WdMd4NxHTT7bayWYsn/m'
    'IsqpG1GMfkuMIRtzkURMjPfLAqoYXmLoAYN4j+hBpb4eSYPGwVzeCC/8XaND/kqhWQuA/RTQsRWSj0vLDNDBFq1SjvZ3VuGTZDAg'
    'BKeCX8rnaHc9gYnrnU0wbEyWRDKuCnBHGi8Js4mtqkX3kFPA6jFlYIbq7PXqhHqooJ2NOSADKDLEyvsn8eBsWFxWAlcNiOJW4Nw0'
    'hYeR76hpVagEswsNYakGHE8L9n11w3VrT5a2bzwMvOYtr5PtvB+NCWEg2NLNa1pzww3Z/lNyX1rHRG1N+5SofPVlTXGdpohG/ZM0'
    's2lpxnHM+MXsQGbsTqeEy2RUX7oP8q286CcrkddUoiUWl+34Z/HRxK5lZNPFJnWhTfF5QGBcbYTBXci/XVuzBxA45KsDz67+JUc/'
    'a6n1TCk+mX4qoamjRHZTsq/05x4Qlve1QpGJ1WhwNBxFDcfCXWxoSI7bxEl6UbZivCDM+xQ4zbnPpJkqjcZmINT1AJd1PUbNmi0p'
    'uNFOBvLseGudxNGAOO6ZDp9csgpbcolaMUHZTNichKwCNBWomaKurmMkzcUVL3c2mszTKhWsapUK1ExRz83wkytFmFWGnnwcx/0T'
    '/zlhoy7ez9HdXJzXphybE3NEEZv11ppgRjt1GmeTG3ZQoYWVuIZJEHzHbbfhZnzClFVzJn3ColUTQwVqduHidbbmoDAkpPKMpDFr'
    '1p6SZkkwgeER5LIAT37ojPLRUCiAisFQhA05Fjl/OtA2RTxuwmoN4veBeNrS0q68G1zAeO7yd5XPR7323lZNPPbHL1/Be7z9IiUj'
    'dNqX4pMrGgjG7J2uCd6mvHTTt57DOHGTVezWOLKGRaWr+q0ET7u4u2W4L/RmPchvz9URLFyJR9BGxCkc6oUdqlnOsTyV1D/muP01'
    'Lc+K7Yb5FbIR0k1wIM5no0lK4RGvAsE4myzuY2pnZgmtC0gHlhUQTYVtm8X22B7jgZgZPDLPszxwULGijtnoM8ra1l2+UKKdwQIG'
    'gV+TgfLdH6u5yuvT7GodlRXermqmm6K73GkEDMyrpanbMBe3FL7KRJ25NJ/Twm2bE478GsGPqLMTrmiFQSJCRzsukMn4NkHkr2Yk'
    'fqSzT1pNk/1Rb+IcaZlK3hi6EMOSdhSWn0qRy7pVwn3X0OdacV2KKjKeKO7/Ab4+bAjnK7TVkdo0+zGn1pg6Yf7hPfKyfPXdlvS2'
    'Lqs12nmaTer1qNkjlNk76B62ogOZ7YR0bFjfN6j4idatJJYWd0FzCAdKNAA+7fCDpdmkve+m2ZzAxiXqrScbAzs7pB9oCTlYuVxH'
    'oZjLIXxyhSOYNoEfoEFMUXMoP5POlDjXXPoCtMUOmvdq5o4m6a1pSbH8CiyZJcwJ+UtKfYxJBjBSpVawva0axkmUj9Px2RiHzTVq'
    'JdlEnRgven5b2Es7ygtt/2BcGFOHdlSOtXhcbhAYaHgulY6Jvjrj2sm2/i4jGvGwKKS6dLu8W9fQB5WAUXGOfz4D6w3PMlc59CGo'
    'pKfjenRbJdeMQWgGMnbmNRh/xYlMJU1Zbk1jFFjLL304Qr90duq2eFoZ+6Wa6owCNEer/a0rRcDooxuzxlhXscKiBxj3nYqEq5X+'
    '8+W8/dVEv3/28on4VOxuv3q+ufUriYDP2/Xp7iuKMnSKtptoLIM5UGX2ojXR6jbJhpieU+Qgx0X5KcjSMuVSIcFNdeh1qNiSOrnZ'
    'yS5kAgffl5Q2vqVqO0oqm8zGLWxW3jsk5oDAZ3Y4YBwCBfeAyQfGJiSx/CRDliMuGacO5QM920L5w7ezgDVsy/Xj+1h6olJQbcAq'
    'rssysJLeXfXsIOEwb2xlZwUKt8KEc/BvT/flqZcBBpnp7sbH8Xtn2rLoYr5FYzcxvUegnr4hU/GYJHsNkvVeTB611WOCcsbp27pX'
    'OAEO0jOeDdWnci4AlDvG0QSwMBIB6KKxFzpo//beo7/85Gpab/xw8N3hd98dLhw3MQbqJ5+aGSWQDQsEvO9Jo3Z6co+fmKwLagaA'
    'V4S53X6Pec6paNPMA/CXHG32OPHTLDgz6LlVhTYbLZzeSVoAOHWvn07bfAX+krI12N8cNXzdkwkw2RMWgvo2iQQEZF1P3VTItWTc'
    'm2Q75wzDI0XTpW2uf6a86VNYhKbmFmfXuiE7JtnHO04f4jDfIdi4JWYf7aBof0u1w6xWO+wREGj8Q2Suv4iG70I3QPtZHL+md9LO'
    'CvfnU4py1t77cuf1G4y743jKTuQmtg1jSB0hc8Voq5P6iHPKcNNkpEGbvwFsswYibTs408pHSl/Lr9R41JNSKw1VoI1wvlFY1BIG'
    'sugYx2x3mTst3eU6Jr4P7JE2PvWkcC5+6hnWIF6QdeL3cZ+tLqUNkjYwN9zvaZs18w8F+9rpfvEslGEL0mCz6wHWA3TBcBoNWw0s'
    'L2mzdxW6CHxdsyrhd1clgcfHmPN5Jd0de3rQOTQFrFOuLFiwTpPzatnKbINdqRx+tN56c+K9leulJvIedcJKD2zYf6ns1NCkNumh'
    'cc6x/R7F53xPoK7UbrYygQVBQMUFeSK/PpXN1IMToPb/EW58fOwaK9iN6RNQRomwelMX832b7HjNM/CUvc46dm/gIca4ZYRG6Y8U'
    'cpMNBCrwyni0obNOZEbml9VRHAOUvFCmhJLXT5sisQTtU2f/JySf2n145J2JlnxBwyqelmnDHqICgjFC0T5Ud+fAequTMYff3ub2'
    'aPqhmGDT+eKahXaJPfp7XY54vEAODkUoBa7iJabotEJbFKvgRrGFGCcjr7uDnHXANKbiN8E+iPBG8/v2KovPf5q+tUQ3OD237LAr'
    'yfkb83PYl2iAXrYx/bsXiVOAxs7aS7KkLdY4JCrcomadqBT2jAiPzW1XzK5Xdj5e3AypwZoAnYjXAoX734du8crB1L2lUrZZFRPE'
    '9Sab6YMtibKlMdjS2mTa1zdQADftOrx5SJg6abVcY5TCUieWITW9LE5r40Ou4vTnKU/5spAlYVXIRj+JHoOXHtGznEGm0T9JHmov'
    'fLA8AwMiC6YfaZ+HjxFa7+EyhO6RGlp5qyIUm3wZuGNRh4XaTpks/YSiUw9E77IYfrbBcTYI2Oski/26FMQH3Wjh85OdF+hSm2HI'
    'iY8qIr9DOTnFz9mh1740ub4qjzjZRJ2toyTQIocaahpkoew4kkqzWu/OwTetJV4CcZCJbQuLYMjgmiHX6w7fXWqf6ygXHet0g9CS'
    'uRGZmpwMJiebb6TX6Z6rkenPp2+zalzMqWHTKKcP3eiHrojIT7awvFTnAupczFuH/WBlqncr5zPlmHZiPJBkVBZFxk7DzdPYtXIM'
    'lmcRVzYmTvQsL+sruZb5KcMb67NiblVlByeQMthdSZCrqTc1PT/wFkVdCgQgI+/nDxmF1ASv6ufBaKLVoUv7eShuaaWf/xwRzfzA'
    'No/KI9nYXkT1uQHOHRmHo9/MWEUKIEuRLzVVUCkW8rKsdST+/mocp3eeP998vLO7uf9s56XY+3Zvf/vFr+lOkMeP14LIl8Q5BkB5'
    'NlgjxzKMaUKGQaN3a9oVTj1Fo5VXF2v2Uw6iji8wFB7gHPThJ4sYZHhGxDmQR0kf9+DlV5jbxK55f7mF1/G6AMWwL1TH+HSsl8XG'
    'a9FwWGuSLSWIf2gh6PQ9nwCLcrrZg+295j/djQGFWU9RcUWkg8bfIaBn+UkRKD59NnpKuo41Rkfq8Z+dxWcxTZ9+jP3N9fwdUDpL'
    'uv37JskTwDoWBPRw5Qg0+B/1AGPEXALG3Y1P04kpi9ez9gK+gT87uxRRu/bxSu+z3gCzin48WI5WlzHP6MfL/ejoQcTPVpeW6dNn'
    'vQfxYJmefbZytIKpPT9e6kVLq1ENxBNzFwozG/U2z6NJlG2lw9T2Dkd56EQphx0JCcUgkKqxqBsJCYvXT8RvxRKK+fQeV30LqNvm'
    'pJ40AG+Kzvsj+Z/lguSM9IDcX6JeXie9gPNOtke3NN4ono2SSQJTWPe9e8cYZgl7RsaESDA2TWAAjjG18F1+b8H2iapTJa0C2hCL'
    'wBPSs4POIfxPt3n4rUvf1niwKnTOYqPhp0KUVhj/9Dfwv3ilDlCEoW+OkZch6xdRR4miRb9ewn8NWeGD/2/N3SlGy/kiHr26cEM1'
    'y6gjHM64tnnaQ3uv2ubvzjJMPrsVDyL8DoJRTt85AGNtC3gCTGyxlYEIAn+fxMMJbsjtCINzcwTF2rYE9nQIk4Z/0+yY/mZpjnkw'
    'vjiRf5G5wb8Zxghs1r4EUQ2TyD47T7NLBez52Yh68iIaYwu1l2mP/u704wgL72S9BIG9AvYQe/YqGab0HdYfy/3ZWSLRDADblS3s'
    'JgPq0S5wUwh8N72kYe31yVGwhkQV3++hoRT+TYfUib0xXj5IYHuTOKZKE7z5h78XnOxjHypjI/vJMQHfT4Fvhb9fwwbGZL7fYIYG'
    '/JsAVAUMMApN5DfJeYIT/fokomG+ToB547/DFFMDv06HeNr/IgZoJzUVdFkuahevqnBl+YwdDVM48hzLBaTHFA4EHF4OzyJ1M3bt'
    'xdvUHiHjJgN0dDudDpygCiifdVQ0GXmGL9gS86I7bcHvRfw9mr41BUA2rDSEO20h8WqNL4wkAlV0DITR2MRavljXz9iIA0gMMMiE'
    'H5E5O4+yeqsV4SZuSNazkB++tDLIKt1FmRx+Om/IReg9YgpAFBj5mkcAHx4FgoN4YSrO02TARdlRkbwf15kmZzHM/QVaqWYxxaIT'
    '0QgjBiUUC9KDT+KFA9yxqTn9hniGLY515GCS83nX5ZGvspuVUQsrjy/Ks2m5TPW5DNlU2yJyAYhqgqEiKWw8XSiwS5dmbpT1rokl'
    '2a7J8E2A7jCP74+//68cvExicArCyDo7jGQX9wFXanhtP4jl6VY6vuRpu/V8kWb13FZlm7j2/WEyJu1Rm8RG1CbWz4E+ncSjer1g'
    '5j17J+KU96HrZivODHf9z/9YWy+ekVDJ//Tv8YCs4AFhwafRZslHZkwORWnGzjAvGXPkx9GAn51GozOM0lwIj8Nzvxufx4BEB4H5'
    'Z56jzYzwH3qC5fwuzj25AkaTxIM7808y1rjEmV6dPdPOXJTNpGb7y6bSkgz+0POZvaP5/JlMZ23XEoE4Htp5w2cQKVEHhx9fYKXd'
    'T8UJfmB2kjLeEH61c43glMt9oOVQRXqrVg6mH2OGeraUjjFlNQClD6uyOq2GgBJyIca9HAu+sxVQsH5fYrpP6FtrAtsGhT7AMLmM'
    'YsmBi2g1ZzYLOIArF0fPKjDnVBJZ4xEhdZpzctSRbGECpWIzoaN7w3YYzxLRck5PeCw4o4DOrzMCTNRcBB0cgQudRUeO4Wjd4jhe'
    '2jfbofNusPItak2vipIKjAZwFppFwXtW2lSEKeCUHSUxEEXgYsg/zLi8XYefsMI+2bKhG0u8HCBN6Bw5irwURQWcceMW9LShChBt'
    'Nc15BJYMCI6MB433XKGDWYWsvJ3Km0wZLovQdjOvp86gTznPA8wsrZlNNWeLMkg0eKnviVpRpkHhQ/rlm48c04o3DiWIJAdyPMb6'
    'qbssp3vx5MlZVh/MjGx4kAz+cuMu9GtwlrUch84e0cyAmKJ2/YykVwySoutXX3bImX8DxXHuPHK6xTy5XM6fNSl1yKqfGId2Pg/m'
    'emlxjMiDcG6SFkdu+euJJlLJZmikdCUdJJOZsLCQDcsAYd6R2dHiUL9QshjI2yzWRQW9tRN8f26pu1ocLpu425pUW0Mjf9XIJDbg'
    'QQTMZbiECgOt/URuYt/xkYlCT/CU3SvHOR864e3Y9nINgwzneEU72NP1iIkfKq0rG8yiLp6DB5lyMO9DjOmGSbVs251zNX9b+PEJ'
    'NFqYumtkTeKDtMCiOuZNkgTPzZ7UlHFs8jVYhppkLFr7MNBaOMK7SiUzYZHhBVS834H/1HO8BF4ry1HD1y5v1B5dkyeuaeJjwIGw'
    'XvMhMq8B81Fn1hxciIdmcfmk1vQyCuCQyMF5jSdXejtj8a9H9BntOcg3cs3ZTlMDSdYvB6DDcji+isqiKx9XpKO6g+/b6bvS1Ex9'
    'B6WzHFWnSiYRFJIX19FAEwpN2YmCUz356E0y8Ig5X9wwre+ul/MBBMVZRKloM3dciHFlMOF4UM4yECT16A0wt+tiNiTJPIypLzwV'
    'yThH6zP1+aBzyLi4u/ig3YF/3ZozHJJnNsTbk8lkvLaw8MlVMp6ufXJF1fnIvMHMKFN5fh7JGduQRcwEomL2lyDc3Uq2CWiRbizN'
    'lKlRZrPJ0kWxlBGfbRFBcGbamnDQLsJJjTnoepyd6k6l46ifUECvWqe97Ahme6iWfgUfrVxKBh3QriNblDeYGVSiG0oe9E//Qeyx'
    '/pU2Nam344GoR+dRMkSDEJSdOIRXegrrj6p8WX/Nrd93WCfFQkqAtUIuMDfvj+kBYSVGU5hePc+jY6CXDzpSYeSyq6i8pFp/Kpxq'
    'xfUiDgZIx7v69UQc+2hqxgi+ayF1Xs2hvtq5hQbx2urua6oQpfpwsVOmPrziCyXl3mw6ix5ZmLY7GtGRJy2nvQVx5lEZntBeteMB'
    '8FZD30PJLwN1QTngT00mOjVDUNtMchUKhaRjmfvKU2gUlZXEJQSFLoKSJ0NeMLLUsASworrA8imwo1/JgtqgpVFWwjJjKS2jLVhs'
    'CdiyinnURrwlNVrF15ZqwrWI9MVJZfFYzUuj9sRipT8YM13GNgvDbqwVubppw4kJ59rPBbjADY8Hchm8jWrNjnxJ1kBa3roxYdbc'
    'z7XJsq9cYQEKy3Hu35fYQZOy8w7v58bPR81ZqrFQZBeHoYiub1KDgRv+ROllgHByOnueBRqbG6aiOrCBu8WsKLZRb45qGZsHtya4'
    'v0w4j6Kj1Ci9+FJF1ht7C4vODLy0KIEE3yol7bMjFalkeCnO2XJO/Pi3/yBO8DIlmaxjB2QIP3yMuwQeG+0AoB7ACij1+O2Q1pM4'
    'XU4vVNh9qu4j1dk1izPGvJLYVqZMyWH6KAU9JSHjUCHAQcqubb58Qrf+cqe+hxOZy8mDig2sbZ1VXt96TY4Xs/XJrsB03SlSlIDB'
    'G/YttDWutTEobkkjMDNmGooKet+cjRl08Qs5eiHRA4jWDEIuq2ENhWdLuQmrUDkTQZ6BBdWuOYPX13cRgdJSO4oigW02f7pwP/Ml'
    'ZnExpJIa87zWPUI5kJ9goCZiQQnB8l+hNuoVhivz3hau8qTmRGa+lZpgcrhyOn9Oni9tfv+GHbKgX511r1R1MjupA48zGXC74Vd/'
    'eXY6X/3R2akbqI2aBtxAMGz3fnrg2zr1163328VoRDDch6KDaC8ZoZavRafdu9TVtVUoRKiF3mvcRdK4wZOC2xqVYXovOAo/EIqa'
    'H7lA75kc3eDmQVqyqDst6mlDg3JiJdbVkspd1mifRuM6Kqgx2PVDL5bi+KQVkS30XUETtnEXXWSOKc/dmgmsyNVRJZZmP/xQtKGW'
    '79Ek+Icfat/wbDUa07usMt24WwDlFZ2K//7fRKEQxsSEQjgeKMIxGx3D5xJgKqZjo/19mozqNXcCYYa0ihM3fAM2hq/6hG03kHcE'
    'DWUzjsbrbLku8wurEk1hIOJnTLoMzP1ErYDdeABXQPOESJBrwL8PN9xoFiY8n135IASpJbpW8A4nI+k//J/iZXxBBvx8G0y7edSO'
    'zkBoYe3xJpyES4wqWWs0xXJH2mxWJcvVCE6TBS+2sov8m2KFoeo0qMBWYLoh1FShcAcoPhrlqHJti+cRZV2JYacyT5yLhE47fEQb'
    'N+XainphhDaMj6P+JblOIGlWBCiXUV3osGTn+AoqJBm014NFIjP2vD2bFprHz+GY75FUKSme71yAG4UL4bXloInZXEcTlPw2apjx'
    'M65ZRHDwiAiLz2lWk5ZZZKWEpJSTkxJSMptS3IJK3JxClFKHKspwc6rwQSnC9KNbU4L/nwrcggrciAJcWRr629GBqeyCRgkssdH5'
    'JcGxnEC4URiuSQ/snOU3IgOkffh58/ZwCtJB/PXus630dAzHdzQpmjU11v2lNJjaZf2bQiHroj6tXGnq0YebT8iH0aLO0JEagw0M'
    'OMPpHGB3UMEt/bRCn2qqWlkkE0u7qMcbWmRyaYbdby8rHYyZ6wptEI79NE8A9dmSneX46N++w4dYb6sj2lG0ub7Ohhh+8qRhlLm2'
    '6naz34/HE1TaImHhDrZ4GlBrC+M9BoZkzZqLNj/CWJb9k5iISYsUKjXHLkBf+2PHgAugLaG/oxK4AbxKll7QomzjfRreb5z7V3Rn'
    'I33JV/NMDmSCKAcoEpldeoObHBisdKBXHi+QnvCTupU3s3d2dBRnOoy+jpRX1CoDMsP1R5VOYT5459me6dzNK0HXVdCXFIPKGSGc'
    'kyrhHzcxI5ZryPjQOpEL9fDehhpQm//WJegr6Se7RtEK8LbJpETOvhtxUFMrGQ2NGulflF364QHVc8zmSs1y3LqdozqAQCCNEh7+'
    'KON4ZLKWcp7UDWHQazXTThnd4j2xaMfNg06qdETyhrUGswgUWTpe0UnsOFHo0GmTPEBpuCXRJa0wepTpBtFa/jqZAAqm7b+GY5Qt'
    'cwnq5v2Gl0WTo6PDqQuCwo4SJOrxPQfUyvVAJQMCROMFFrAnA19KYEsKWMPRcAgngCEZk8LeLOIROzte8S3OsgfG2J+SJnFQKxj1'
    'VKn6HfM2a9PDJDXChMsKVEGlmrQ2M6Q3K+siuQmThprwOmEamxkpnO+Gc+FoawAtFud2yKFI0EKipUdwyb7AsCshwczh3BTfZrg2'
    'zbNtHBzaSubbJgOXw3E94G16HyxgBVfxaSfQvfSULwGkrx5nDiBWs8naeH7tpC+e1yTSoSM57I+9k0jaV3O7diIX1Zh6Bgusi8V4'
    'e1jnMLQmFdsdOp1sE6myeKuvBLFoJakaOSAohw2LiOr+GZSr29cRIvFkNIvJ4Oy8CxteG+vcL9vicwO/0CcQNSJOW7tONCeLJlaH'
    'kWmAfd9LANVe0ug9HEGQSWRDmkunr86w4SvARnTmltlwXvspwLxk0maltVi4YSoVZodpxkNSdOjZiAYDSkBs7e5mYPiN9eSIR3gV'
    'Mm7FhadavLyN9cpRTc2AQjaJG+rDuh26jBB+7p5CE69M6TMK0c9wIer6wCsP7qtxlg7OaGgysI4uQZbA7bZ50lg3WP0tyqUurKnH'
    'qKn3xZKw57uParW1GuaXBAb/OB6QVydev2dAFtpvm/dJEpt+pAmhY/QCTCHamWEUs34M3wZtJbccJawuuwqjmA2OQBREmI4+yEKG'
    '5HzjKaeOKIpJnbQLd0Boj/N0CN1oWFqrOQPeSZ0Hgr1GyDvskyXSzPSjJvCWNoqibqFtQL/gRx2SrFG/gw9IfA4VKKiEvCtEjvry'
    'C7q/52XjYTE3wFuCN441RXLkG4Lfr1e72nxs3+C2uIpo98dHbJ5Gx6Hc+0ZdOktjDGC1NTaXoJDayI6Wm49MZXyaN1ub+29ebO9v'
    'yhhD42E6kdFwrgRl5WJbyn8VryjmhsrlmGMM31G/BdxXC+tIax+Vp2jNrf77/02ofEMIwq2u05AzCJ3yZ80F8b8Lnb+HbtptELqO'
    'hCGzz/uj+P3/Kgi9ymG4MDgpKNfHaB+BWfj9/yL2U13dq08RQrh6OjmRMYms6j/+x/9D7OCLYOtUhapP113jPlw2jlLEOQr/xI6P'
    's++uk2/R4Mx8vnyLuJOfPnu+vy0DLY05SIzeXs2a2SbNGi93syYDu/D8H6rcIdoODGijjQutYChHLh59qo8+RcFkYQlROIhKFJ1K'
    'QqymLVhfy4QSiHoJgMqBiDIg1qwAi9Ifng0QjzWqYNVHaLgaH6fZJbFtjFHM9NtUQfGn1UkP5WKajIfcOCZc/ryXPQRON4vFZXqW'
    'AR93nkykvfUkRcFEHMXxALX3bZUYMeCnVZIdkXvKIjPqR4Bzx1BOGruS0tgzJabLABmjsBhaCyo4mmVXPZVIBb6uawJa+RWNStpJ'
    'WpEL7ZIaX4gnKAtzXda5dzCwTtdcZKrM5qcoLmIt4L8m6XO0p4+xsgzWw7c3SNmt9/tcC9+DfHV1AtO/VlsEdHyMwZaAmT6bxOaB'
    '6/oD++NFDAw2tKgpyAH1U+2cQ+yucavV1V4lwyHNrYTwyM+FyAgRszRyCaB9Od+RyO+EUPVdCLEi0lUF0CZlY6GLVExTj5vB0R7y'
    'Y7nr2+q7ZbziFJR7SX4zaQTeSqHD2eLQb1nw7kMtF6FbDVfG26rM10fJ1vrBvZbJ/QJncLPmaI2s+LPeNrPqPArWmTg7K4Nt9cMP'
    'ncZvaUvdcmeozCQUfO1taG4uKWGlNT1lk3hZeXuX9Wk/ZMmUMcIc4FBL7LVbVvQU9hiBt6ZfH1Z5n5dNQk2XQUTemyFScvNQp/1H'
    '/OCtrdfTd35KiSbL2AdAnbJsMF+iVyzppXq1RBV8y5dpfFiYvKAEIDRNUpKAhuZkOS05J3wXYa2HX6Bq9Qk/0wZQ2Naf0QI+4YXE'
    'KuVoWCGUciiIZRGGxLaFCoShEL25C/SRektto6rgDaUDelQ8I6jioL1y1y+tNev3VxrTwktGTA/vrzyq/fg3/wIyd216194d05J1'
    'UBuTCUxhb2rkhcs5/ahqiwNBPb0rkgE8y45aEmIymNprjA0AnY8CWAF9hFT1xK4u6EbjhKIbb9x9jR5BIiKEfAkjvSuy9AIgLd59'
    '+PmCAl++q7gxqOJggs85P7FdEI3zuXA/GvXj4V1018RwYYqToaSpGH/7sl4zva017j7cogqfLzDQudvJgUsutLIXc5DvQiP0sNiG'
    's3juF/98sSGRvTrB3onvz07HhX79O3i4n5Iizd6KyeD9FDr349/+B4ElAv0LtlEAjy7yoWErbEAIYI0j+PXQKWz97kOyBqNKhuIa'
    'ci3q/tNpQ56MYi8/ubrj4DtrCfHIhudJFi6MZZef+wvIaQXole7AW6uhNcUUySEfpXhBm/wuXut2xu/X7Rk4zuJ41FgfR4MB0GuQ'
    'QsdrS1DEaWOgmCWPdJQknkU87qeeZWkU11yMk1EufiHKHd9ybFaYFBL1WjADrfRihDY5WpQYI283Vv47XlCU66bjCMSEjPKWRZtr'
    'dmDN6ygvtRCHlbQM54vSvUta6Q1xNcWHVFbLTKxVr3OZg5E+/Id4x1t8KK21OH+en6vgVoE1/F5jm9vD66SaZs5lp/c9vG7DQmWA'
    'IeTAzJrUD2AcTZYlDwuep5RqVrZ8QDeWz4DJghqNQ9ur2smiSwm2/UAk/gLb8ghsuAqGDs+2Kg8lXYbO27CmlKsRLpr6UxlpIliu'
    'KPasujz9sIJTnkycxe9gEnHadqg42hz1gV97lY7PMKmqNcNyUZrYht5ZnL3cQmf0MoTNELaICLgYI/Q/Hd1aaGr4Nuq9nhQemeNX'
    'RIOsULrRZuF6LSpsO4/hd3sXl0OJxlJj50gDvFVQDh6poDQOB4zVsAwwc95Ti38vZd6RoPn1NH9rM7eS9mF0GseM0rLSownAYT1G'
    'mQPI6hawDqPJrk5MTXNRFbPCLoAe2drgAtrL2r0UKP4pHJ/7TSEN5niiYjKsbYnFxQ6pbMbvC9CG8dHENt9YbYqMH7bEUseq5odn'
    '87fL3A5nFZsi7HUmDY2nVZmH3PN/+46Ueihq/8U7GACFyEJeh0WJMgDfoBfqW5vmCW8fC2Seb2XC82il5GC8gtyvWFA8ofhT5Y0s'
    'Nh+R7Y1NRyw6qSs+mkmYkejqNHtIPq8Qr5fnmPRTTNoZJt0ADhsPAZBMOd9c0uEawi6SQaNYxdXjLlGBBW9pI1xtGSy30ocPc3UD'
    'v3ymL/SKxx8ODhXgSEcDZh5H7YRtYuT8GT5p1LDuMZw8TKFLzDLvj/KIoJ7F868li87e9tbXu8/2vxUvdp5sPv91DBtv8d7kcf8J'
    '247yTYTLQFFsn2Ry6Yc5rowFUkqdcgltZtxUTDXQ342PYJ/LlJsuoQ516xatampsmoFKexcJHAVA0uzYPkvshRocS+BGhgkUswDO'
    'OzY1WzDmplgZirYsusk+NtkvGWFj1uIQULoCg16U825FRwh7tf6Q7iARGdy1hunxzwLvh9F8lYP5nYHnCCjsEzlQaTf6jMD3zk5P'
    'o+yyruiBfvE8Pa4P2jANjvOpfv3sVV6ss/1+nGhYBbzvLq3buG2iAE1SjA7TuBWHI51QJlt4VTAIO4oSUkPgO6mIIT4XOM38jFa1'
    'aESG249ontRGkJV/jn5dQMTeDJPThG+Ar6YNBfMcYZ63ueYbIHPJEERwvNkDkntRbyzwrZ7fUhafp9wUe43hlzcYZlBqakz58uOU'
    't6LJBK/z80KUO5qYWbVphorhvjd46mbVZt+yQG12G5UOnY8emSjhVdB4/grgNuSSzKouZ7AYOlC+UGGs0yHaN/DWyGD64YREo8tZ'
    'SAsdtvRs+bkHdYFzC/Wz/cIGZ1Wl1qQ/KOuLoekG6Wf4K/a5USQP5uTBHrbPRFzpFYsdggoFex19RiQbX2ooggCMlQhjQKG2GtuL'
    'SCMQx6fAB0lrTqdPkg7U7V36qrv0HS4TvVLn0jUC6OvXKmiU8z69mO+WFQq6Ojk1TZmOqaCi4OS8cfq4XvAHFwp6CV9SDtePC+pU'
    'Ubanso5KTGEqstm2OM6i0UTe1z6JR4nMn+zYndiWATxs3+ikxEJAzDIRaMKI09GgzJqEwnpco3XbssVM8aybZzXrg5SsS8iqxL0l'
    's298VelkjBok7lAyJr3TI/+yOFgRnXxNVfxGlcnpd576vLKqo59c0fd5Kqp7apzVKQCY5NpYJqgfhbmz9aNFNMAU9lpIIBlbOMBQ'
    '0xJamg0ZeRdIXYhoBWiWE84KihgSKBZo66iEwijeY3qhs1ECuFTAwNhlGPpk4lqOleEf7se9eIIokNSWRMNj2AWaAj9OYVmjUaNx'
    'aOJbjvMb4Tp0AqBkViVIrgzLYXsKyyVjH8Ul+a6eODltxgoQBuLgs+Gz0VEq4yAPD5LxoVkEj0uRZbC8z37AtNsVNO4OsEM4lSQX'
    '4IzaVw82FyXEjKpShVdgrD4Ypoa9bBA1ipVIcs9ydOi3/EfJ2U7NNpl8usUKRxXA0u134FYbafQ6yHU5PBnER5hLcJ1z0K2hrKMu'
    'e9c6dPP9H/+LeBzBvlC3vLX1j1zXQlqghteht6EOJbCgwR5xpjy8Vf77/yqeE0CDU6oxcKAZ6D5p85PxLHym+gSF1U6aqj1lHt0h'
    'X5OcDF+agPFo50xpA+l+apsWMwtT/Uwv3EflV/1mzQB99CLbbgFefY2Pnr3Ci34Ylbrjp6eBG/61KugEWzjQH3uw1aIb0NMb4nYt'
    'KFnoXSbgaKtw9Ci05V58FD5DjI/VZ7dEPIzGOZXwJBLRUrVt9H4aJSP27sPmH5kLjk6TnrQUwAbMXsfG+JN4FjWKaZDWvao2Y7al'
    'UxZZzzJl0qytoqwov3vSs/UkyuG9YMDtWiHfkEx+qC5qOEGmGeSCWLrv2fCeumWtwr/hwlDpvqoS6JopD+y+DqP9ltY3xkBDsM1P'
    'pifw+3R62n5rAmXbQ6LxxIO2jutC6bBkhgxKNSKjPOpUBYI3oL13XkR4i3PVWauhz+FRrSlW7y934CslMYBBLK/itweYnWBx5TOM'
    'mLxWW+oMaha5BzAcn5XhHcAfokYS5Po8yWxw5T90NhsFk9LZUB+rgqoHdUl8lpOxpUtC37kkO62/hXeCDvkjsX8C479AY2nYZ8N0'
    'dBxnohcLins+0aIRhT+XKpr228bN7hYQ8wHy+ZncLgBF9zRNTtQvQHw4+VAK7RB6RPhqtvpH61Vnhzix8LZaj3ln7Wz0JzVvSIys'
    'aSMCdruJU5mlFL78ORzH6gQHcy8t3RthvGR0nM5/JstrcsMgNSxf6T0dvBZJk+DBzL/QVkRYjF4n8xQBwlExHRA0pb5Et2PxR7iW'
    '/rOz+CzGztUHwBFcbpDRQ6Vafmakgrkjs+uHwaCA8HJPhl/AC4Dt3ac7uy82X25tt4doX8DvbNaGBtDERNnI1NC3INXw4V/3HmKu'
    'SbACXOAwn42eEtVvGDdrfEyzr69mA3mrPrxJ34fJfzX8eWe+Csx8RaiMQuynalz2M0FhPZjrNyrcwZoXB+GHH7rNysRWP/xQSGsl'
    'pqWJqUBk3lAxl2SkKPd6qs6F8IbqqhiSgV6ZrnkF1k11HfbgkdL6lEVmkRVkgBaviaYPjuMiFKLblJ5ENzCCX9baUhwc4SMveqsF'
    'MBAkxwQhCbVvQRQFHL2ixZypHfD/l2RdIR5vb+6LvS+3t/dxPne/Eo93NnefNH5ZA5XxAnCsbza39tnFesTO0134WYzwVw9+LaEb'
    'tVv6DWya7edY50pgnTW6mGsKqLlW2+xPRBe/AAj+trhJX3vq62P8uiS/LQEaUvB7cTSR18lX03USVykjNzl3Pxu8F/VOC7HOAJA2'
    'XagiagHUi0Hi8r4T6RZBfRETNGPuRuRJNUIWaQ3hfKURAUAVXpUBo/WzIGlWekM6dVxNDL56CfQFhlaXwrWTZQla0HOuo7KpglYT'
    'utBBPQFuuNsQv7EqMm7ym0Zf2cfQ/laUDVzvfPLTqtCqYK9b+UkcT1pY1NKq4NciHb9tBk2EWq5Jp94YVTqtPinSBWwzQXmkRJ5i'
    '8mB8QzQPOXtOv1mibFdZOKGCSsJ5g7BTB8hhtCjM0l2ChdKPHqOBbsee6vxxBlxskW2VTB+1Q4R+hpHi3hdcIpAo+MfJCb6lqlMg'
    'ugATpQuo9K46kJZd17lm6FMwiTb+RTWRFetYp03ZwrkjUx+cPWUNBDV04MTaAqCvlut6QddublWoMldVOe12r22lnQ4H+IFcd6lv'
    '5LNrlVAcLr5EhLiBK2a/z6LjY1IqOdaW83jy6vZwLvGeUU7x9C6FP2xBQxggGd0C/YvWIJSiV7B9G2DKjc5O7z7cI8CI6IqOu65m'
    'XS+ZulA1KxrqqYrsvIXKdxR8+yfRCOoBBLrNlZGcPcp2AK8PGwVvwjlGzVihGE9abh4OD1146AL2PWsJOhKi0Pgcj1rE/kSy8PQB'
    'TbCcapfshmGjIMHkjKzTorNteGxHKbC/2d3qpUEXU74JK10LMqifSDyHqmzuL/qa/oNgzBGe+bcmMASyDv1LkPTNBvfNadydAkJk'
    'udsCcuRWLIeQ+5ITEBbJ+L24Len2PrsbqLOpT6TGOQUMqsH1GMdtOHwDP/SaTM8mHAJV+OHf5JuDnsKrh+LRI8XIYJBVjOx7ia/o'
    'G7ZEH6Ksv6YYG/xPwlEdok6Y6LUub6Gfw6O9CIh9usVzYV6xrArj2QGZbxhdqjfThlnFJ7gLyV18xjLidg2uIOejLKyg4Se9qa9a'
    'NWdUfEKAnnnlie+89tIgwA+yONaQqIczF2JqE5jrzS36YsWD9GKkHHsC5+Lm0B2XoTBktU0MwkDcMKNBhYA+0IHHjGe48feQOzaP'
    'CzlETRyYnGyxN4kJJreWGvfbDuBSrG4xFeVeMcJ3ixGuX4wGIf1h1jH8930rTYr1zTmHwDbgBGcxmSWYGS7OIHIYFNg4NIt4mPYx'
    'QwpGho6PjmBhgIdOL0ixUMOrAB3h0yucy/PJIcyBqCWjGrOj+qxpDsncBxC7AxS0Ftrs4b7HI9Q38aR7INVlhYE6GxwqtKyZgGFh'
    'JgQo9oQNPch/paTnLapsebpWtDOMI7LCn9lxCXQWxHQcWr9C38NzH2jPxYgoVDF7es9b5+PAOnuVJ6nH2coYbAomeh5gEdcUnfbx'
    'Lu9fyVmwUjEZ0U33k50XTivRcLjHctYHlgTdWZCO97q1AzmMQ3/MVFA4RWmUh/Yc3NEg8VqAKwWmQdnFASg5Cb14chHHMr82zw5G'
    'b8WJGWH0GnokAWiFAqwV9eQxopp6zo35YYkJD6H2iN4furHf0WuMnrexFSn37CU9zFpkSsqw9ZTSZGRtM+3fWXMuA7iYretn11AO'
    'AdhwInJR70ywAuzPqLIvJqS50vUghHCmNFyMx3L47lypZSrs7N0Y4wyqrfy53OuP5PoHeibW5DsFSTdqjKEpyoQdTzmPs8njGN7H'
    '8LLJzTbs1Ht7F9GYuSOcRrePp2OPZZK9dbgj0n6preyV58NZKM27GeXS0/Gt2crysMqBYtG5qR6IsawJIalMqiKnOFq+vctR/ynM'
    'gHOHFxqQdZtL8hnp2QReCQJZJHtVwx8UGnEngdrA9aPkp4DZoLfEaYo8FcmklotxQhadZ7C8fKe7p3gmVbRtaVmtuPze5Y8qxNvG'
    'mzW/l8/TaIBTQcvPaQBM+jD6alCU9Id5F1/mXFTv43dMQfWGeYebZcCf1osmbzCrFl9GDb6hnQBjfCIVLq/T7F0+JoUOgrXtl2+k'
    'ElXHOB32omxmbVnO06ZK1E2vAgl8o/O9mEdYZQXXa3H/YhXhXLZgqjcsUEX3OJVM90vM50vBUjl5LqbHRY4XN9hlL4VNvAldrs8b'
    '/kZl0Hai6FyVBxWANxW5siVfVNUuXSi2OPOW61h4VepaCAzZdVotzP3lKB3nSS63xaxs34RUqsxYeCf4RVQSYipTxCr2SfAklGoH'
    '08K2ntX/Obd4CIwzBuLOOGmztELBVfuoWlyyh8kOqf5Ab3m/gd8eBVkObbEUkgB1eHvn+S/xMvT5zhfPn73cFp+KvW9f7rzae7Yn'
    'tp8829/Z/UVeh8LZZnKKGppBkk0u1/g+HBUxFu1hb+t0T6KCOciPwhrXIUEepim9k5uJsH82SODXRUJmoX44Qcg5EZs2UJy4vt8S'
    '5GAvA21MsD8TFWgjdMGKNUAwwpT2at88yaKjiZuUMWeobhHHI2g4Y0eiT5qMtcaGN8NhA2qxXhTFvbYswLcLzkXh5SzY1ikh2Pll'
    'A2pZsFWBIvBJNgs4JmCanFIMgnUEPgH2a5JZwHUBAx0FPqjLsUde990ZaNrfWhd9XtVCcT2opvO1vILpaNP9LqtMC6iI5BAXGX0o'
    '/mVe8gxgX4CU8ASRphFUXrH1HV28SVcD3KgpCQG32O13KMyFZR3v72mZ/4Lchkm7LsSc2/qR3BG8CdhCToFeE/PuXwXFAqKXcW3u'
    'fVqAMp0hjdl7SV3qoa3eRf+Z4xM0qSI8pqJFrC76FTUIvLU2bLXaL4o3FykwsLTWPDJ5aS4z/i18l99bKHhjWr6EF33PTYbhPeK/'
    '2qHYCZNPr2oyrPYvkUXb/3J3e7u1ubUv9vZ3v97a/3p3W+x8s737fPPbXxiTRpqPCBNNouoyi2O83gXB9Rizp6eYlZ3yqdcfD6N3'
    'sdgbXQ7Iy0bpXBprNF90d9yFozwei+6Pf/OPiyvwrL648puGeb24uYavF1fg/Qq8ry91ftMga5zTZDBOkxG6woq/XlmxqjymKitY'
    'ZVVVMa+XuMFVfN3tdmSDfCrQ8ODV7g7adj/becl2dTn0sNNeXGmKfDHCj0sd/NjTH5fwU3fF5UxZSLIvXa1Dj96IVULSZETX5SlX'
    'NQynrkHJWYshglAQcmsqpgNAVvpwlN0SO853HpAQkXLDwBRhWuqokrFYuubAaD6s/ZuCZrBxFpESuXRporRFZSwhgL47sEjCxrkR'
    '6XAgxsk4J1NzTLUSYHsBJCnMW1DQYnxZmRwP7cjHkpTjMQMJPjmFyf3IukZR9nTXi9JLqWExtsxrSRLICVSBcyMoX9kl722I+jBg'
    'eDUPDeEAFG7QYgKNg8vtOJzdJn+mNAV1q/kFsdjpmFmRqllGQmSbii41dP0KH4kPHqd5gvtSDhr4IJpKOWK62uLi9gWLnt3NLHNv'
    'qNQUObZpBIGvzbiOti21YTuMPsLgSwK8kVD174muXYqI53auQ5TydNTtygtm0VSghN9a66Ua1aO24GjoPKl8kuW8nsRwJGByoPMZ'
    'ObPCSU2OR5R28BJ5wlycJ5GF3fWCQmFUy2xiET/+klZrt9GeUvmrIRUB2Yk/mDCjepGZpRJ5fIxHMic6ECekNSX9vb5JEWmGbvlM'
    'oSySJNfZ6plaZ7qtw/BG0uhzDDCj/sS1haQSOZEFNLEWHWldzR968sOS/Et9h49iGrTSvM5RDd5yStezgCHpm6ZIAmY4xsKJjaYP'
    'H4UMO4UZKZnfYUAr7wmHj9Fb1PUSURG8ila4UM3Z1OOucIHDpB6yAah6QP06hI2MJBh9tXUYLA1kEVloqwosyGG4YM8r2CspuCTc'
    'gkt+uTd5jJtnT+7D+hiwFPQDf/Xg11LTQmaWdcfmYCDvfCVRUIjoVKG9znXWVFW7t2HjzoXixLuXn+P+xA6b/NlnTVHXsBbsnnOA'
    'IO/udJyM57OkxRDlY9eU1qF1diknBjN2EASG3+gSTDvd2ONjx9LE4VP81fG4unYOq1V4hqtXfNgLPPRXN7i4gC7x0hgRq+CwaRbF'
    '/umt4K9BtwJ7LR8WcUcSomn5sBHaWxaV5hhp7mZDUEFi1WWHzc6fwoYzbEdOYe41ayEZUyCzZi74bIXmQpHj0LlzA3Jw3JoZzCkX'
    'svLU0veGrOyOWnZRDtziLTEyjIkcnsxoEhkuCiZjRQ0HRDVOPA3B23Ebo27xeKcw4L/+5MqMGeOs2KLDtTCsUnK9TLPTaJjkcSGa'
    'JFCae0Qp7hEZuIc4XlEjeLegwitSGftbz/62ZL58ZO14cqT1O2gFz0oGFKbpgHYj+nThX/Lrog89+WGpZtUZ9ijSJdWBzy1ZDT+q'
    'mvS5Zz679UdwAhiC9APTHmDa90u6fenknHJf0J7DYRnaM3Zpj2RJcV55q677iTvKNgxMBbAdVixTE4Hc3pr0hzemeXeRDNCTB9qV'
    'b6Y2F92raBUn0zQr180WNJgLHit+2cbsFOkJI/lCE7IjGG8YakrlFuAFfOVt9k+ueAWg2amow1an9qbjxlvVbx4jDMfLofGLUont'
    'bX6zvfB8Z/OJ+HJn56s98XRn13brNJeZvzwF2Sv0MLYsf1D1LkPEGf9KtP1z1OUqfXSaJcd7pu6GBWj9o9x+4cY0qOfJkLcgXZdq'
    '1LhN3mBuWyLJ0T4J+kVSFWqtoh70jaRJbOOG9wLQXKGdaAhke3CpGmFrK+umwjhcekOXA8LzsW7NKxpMsqBHYiUKpfFpb4jxX0cl'
    'k05hYpP4/2Pv3ZbbOLK1wXs9RUnWbgAiCJCy5bYhUWiIBC128xQkZLk3SZNFokjCAgFsFCCKTSKir+YBZuZmYv7/diLmdm7m/n+U'
    'fpJZp8xcmVUFUrJ77/17T4dbLFTl+bBy5Tp8q99NsZj3kH/IZpinN0ANoFBk2Gy5Z2y6CSfuGXAq1kAMR0VN0Q8JWYaJFZfAQ1y4'
    'ly9xMK7iG0SWipJPFGca7qxwl47iqNs7P09IaAGcxngIlBYbtgGFw1BVo8vhEC7eA9TYEMsDA2xsu9hEnI04YET7w7irW7WaSb+S'
    'LePlo7OcZHYdOeux/CI5QWBQoi0ZSWAJj9bMzdy0teGZEwN4xmdd4HgnibZAq9BIEqDII2OYmLF2c1UFPoy8PD9jCYtRinlbcQlq'
    'x6aS/UE8Si+HxEr14Zq6Ox5ix35EAYftWBWBpRXqlzW9kQ3y6xXN1PFcTXOeLi6bWsS24eYiGBq9E8jGEDbwx2Q87nW9vfIxHvfI'
    '11F24Q0pCGDfJXormi2acqbeoE+erteQDa5OcTQaJ4tUKy78R2W7ErXknInDfkAPo+hzKSLNxcaASAct2j/YGeEth31DS0x4gK+w'
    'o1O2DjB53yelfh8pSA+jukWIlzgcwzD0FS3xLTmh3BSN/AjtDUiKWqHcK5twJcjJCzIoTW3Vj3G/GonD7LgakaGLs77GpQIpcKnA'
    'nxqG6sapfBXt/2VvY5futn9uwx33x/bePlxwTTo2V5cfZJqhDbphBDpIOuE/JKtusQg5RiLX4+EFvmgcG8Jr8mOh+eav/lgE5q+e'
    'ffRnbmgzFsX2GdiocL8U2GjwJfEGuELKBFQAlRfIFG5azwoUbwvOyDHBQPmm695xZ/ubO5dy8Xz5yFbrl8GALLI33IFJmQLwkpx1'
    '5LdAgYpgAKayCcH0u2JL32841Wz0bnet1WlHG9udnaj908Z+Z2P7B2ZXf39MqQjQRaMWXV8mA0Qd03IqVtqlmp8QSwZIgzcjFpOv'
    'ENjT8FzSBx9RdG/oUylq5iZqSPAY3JRF1TDNya0iCg6IqLCt5fkqTnPzCsbGaI/EUV2Px84AJVfr+LVFQp6he/HykfqhW9m3SqWc'
    'Mvjry0f5jfQO59AOCHlBNDxUGpjIMeA0xZKHzmzjvFknmu5dN8KCVzJ1wdUjm8idQ/D7P6vV829lhVVcDpwBhM3+2xX08N7Rucbb'
    'cX+TFWdTBHTtIRYlnXbmY62bGOPYYJeaXeSlybECENF1fxftQ+ea+vWNDanjqCVbxeQvDKukxExjlMPOFXwiQu+ipNO1yauKKaPA'
    '/WI2d53BbH5A3+tfvWBtQQ+f19x9yfvspa8RBQKAnjAUwQU5aUwTAbuCPph28+PL1F8u4p7F2SkA3K5kDldHYUpFoX5fXMLqznan'
    'tAbEdGsH2IXWu87OVgt1QCzZOosHqXLsFO9WXgrINlatxkeIcLcX94cXU+D+x0O4CpEUAq49H3vjyRT4czZcQEFkPL6pkmSIOeg0'
    'urgcIpJ1PP4AzHvtd8aVWJF/IUCkPTiF3cUXTeN32oR7wwWwuFjEOvATmAVDFHEiwtrxX2lBLYYyYmNEpjU442vHNN1stoouF/sI'
    'OXq82/qh3YhefFe1F6DWNwTXaF16l3EJDEd1iUIL0wXtSqWQ47ftjR/ewm3rp0a0/K0rZPk5XFmBSxn30N5gEn3/bXfUw65OBwg6'
    'Ll4P1UeecdlxP7mIz25MIMbBpLuFLqZfHkp0jmGUM2bCtU4iLCQlshhpmRJlExCs+9BEr6Chi5i5SpZeXXmWTcDKJCqvWqPnwfQK'
    'QzFdPcA0ykc2/QJ1qkIQe9z3VJP+eGwlMQlTYRRx444J8D/pRpcUZph2O379GPf6KBWp4hz2o9OYcY+UHhjpd8oSAet0gSaUEoYi'
    '+m5p9AmXVBV1LPAoKwvReb57ji+mKYtdJhSNBV5cwUHIzeDi30wnKGBBeSOZQBGLj/NnJI5RGWcE+tAXCQ4Rp+hvQ4zeAleDflqx'
    'Q4tb4Jh2BMUgNVul5m8SGiVUJ8kSNvrtpZey5OF8nPZjIpOuTZIH+789Rcz+ZSoHpjwq44cel9CLXkV6auDNwoJvqiUIMJTqoHfk'
    'WaYgIeBPuYBhKiU6s0tK7eDubDnaMo3R5fAadsPgJnqCCdjULH3CkuWEGYBoeHY2HfWSNGjm2+w4OjrhA6/KEpMmFYTQrvHUo2aT'
    'is+Ymb3jwBEFxnW2ljpnr/gYashV7PGcYlwENbsS5EXP98KKq1HBm/S6uBx5jcX+kdcMqtJWahy7QTegrlajN3Po3ZDN6rUtyGvZ'
    'RZv1tW2Ak3kZ5TgRJ9rRsNF7MMsDtDX7ZUooR6Q5oZnHzhtzA7umbQULsryNIPLciwFBKxjKsAwD8QJkT8dLGAkAGVlSC4g9qTOz'
    'omR+ZV7DyMWZgkq4MtRrpLj2G8E5YPHGWut1tBSI/NZ7AlUBw3OWkAwYLsdjoINwzqgei1kTfDJ2GCUnNrNb+heEFokWYSjg8TVt'
    '718WF33YCNK+0k7+5chHmqAe2NoDtIlIV27z55iqTobv8GKwCuXCLwM6WD9Mnx2Wa8+ahxV4elqvIjqbRyUsrAWuBv1qpgAs9NBt'
    'EBZEVMa5qhStFBuzBD6iZmyO2QtC82kcI5PFN3+xp20pJ2UQgoWblpcQTTEm0PvT6QQvO+NevHjZ63YTBAYqIbihboiAYxHmhSmh'
    '8jJvLNxZD6SjH47B6HT8Gd2H1H7PswxFyU9tFtOIacUJ7UtW08NmNWF/TOrPGgI7cHT/KkP+zACQZJyqHhB2RkQ8DtzKhqPFMdLw'
    'Kn99Hg0H1+hrXgmGB7LtU5aHj5HJ4g9UwGXlJP+svttcGXsIM7K1YGh5kEy+/KWy+ra1hxjQSOIqcq1FOkQT60n3zb736YHjibuf'
    'ua8il8sfN8e9lvJT+wNg6dFC9MT25El+zs8acD2ItojKywIytJekjjMTgS+KBBFHLBqeU6hInCgHvuMzceGZHsiGpJbt4cQdXqgK'
    'ouOR4XDg2E+np5N+8vvd/5oE/lM3//Mv2P3PP3P7P/+y/f/8SwnAcz1cwerzfi5GZXUheeZYNh8jalbglfRPvjbPvXOavbHoRBeL'
    '6XA6PvMibNA9xpjcGUZIr9tQ6vF4hTQqFV6ATvQR3GOyOQUNmo0uHpSWEuXg0M3pmDFzu2dsVE5b2vk4vrjyY9bnyQD+g0QP93co'
    'WewzwHAYRcUWlx3KnGzWDaYVeay7FZGjNh4WzcdeinIJhlyL3mCXkNpj9FdYzhhR8GzYn16RbApKQ2NuNHSGAe7fwKfxeIqBReF8'
    '7Y1JsLx4erNIpgtxv3cxIGLzMHHLGZpOw5XGeoElNmyM1+cifDm4rRSk8/pPov+SjQ4zX37zeaKMz7qtO9HBzrlsOpzeYK/c2wmM'
    'LxjczR5xTMEccYRuoNrstt4CXHRHDAewLNbhhtzP+LzBHW/yNpHwJsVih2bNEzwsuXiuLAG1RSw5xYwoHyhyz9VoijJf1MwUaKSs'
    'zonTZLI55akAy+lay2RWst4fxpMyq384QWc4qlg/pqJEb0jgJumcZQR3Qo0PXZVFOp0RrpwlvX5Zp17w2lgx4hY40ZZqSy8CqQta'
    'gLDERZBpG9HzKrJQglneiKCe+IxDmMGjvRLTrwnCffb449fR7IAXJw/YkZouaTtayUuF1snBLpWBW0ob6P9RJq7RTJInqWN+EqUc'
    '8yV27lyzkn4y1LaD2dODLu8Wl7NtMzuFABnf4Zr2W2edXKFx3pJPDyidsQ3/wl54QkM1xsrq3C181s/CioOBvEwmvbO4b3W0/E3J'
    'ZDwBA/dgIdMFW4k3TtZRIX+oNmH9/GcfqZXsSOmL3b3jYe5VvYGDCp/lVqKG/AGlqlnxhtz69lAZ1VBGOdPzQAK8NamWlj/S6iqr'
    'UWhixMeFnn3SbNE7UFz3AK9rpRInfA6R8L2CKwbQAFcjvFkmGaGtN3q1or7bfcmWO9oYDzHZ80TLLH/VcsVnusK67mPFnR0mbgs6'
    '0lLPWhNWCmTWnmgFvI6RUNFbd/JhQZBKYDJNWqD+PThxl9HbyqGK2yp7zs1VqJVIR1ek05XC1XDLHW1w09J+7ywpL1Wl6ErtlyEs'
    'lFJUqlTJlttLlk3E5n/+VrZi2FVD9MvkmZdLk+mLjIyIW3ta3PoFOzNf/Kq0tD5V/xXS1lkuDXVybY98hgSjaH6M9YceUsHsxRwC'
    '3MtWysiOq8PVyrWrJILfEud9bWBswmh3VaBF2YOSIxz7zxb7PlTo+0CR75cIfKl/jOuspL1K8PS50pyHS3LukeIYEc5niW9Ud5Tk'
    '5otErp8hbv18Uet8MasVsajuhAJWvRBx+3hLO1yZny85fbjUdJ7E1O21XLHpF4lM1ZiE8lJZslp+V6vVKIM6Qh+7/Rtc7QhWJ+fi'
    'niUz3uHfIn0oLt1iYvMwvuDciIJWfPIbeD6OyWU1y4CY7IWVqUGgUpo1SkgoY/SihicZ/QzWk5BcFdPS3VuLwpWplt8n+lqxXc+V'
    'T3Gkh3uEU1FWbsZ9oj56pOAzKfW9dPpeCv0g2uwt9H8K3X0Azb2P3uY08p9CWB9AIh9Ed3Pa+7nU8AG08Iuo4MPoX04HjDz1YbAK'
    'JnVmvIvltC9dJr87jkgEZZtFxRvSBjHsq4iErkiMXoZtsLHkgAmesAnF8GpEUmwrG4Ua44txPLosqT3OKgezp6qwZKtmLVTtoFZN'
    'hRVPRmLDAhfaOeXZMvEr0yqipjsDDT9FOdCgdjhNNVEW64l/pi1U/jGRvQlUiuyJfCGiM/d5T/FEYrFVsTOBcurTBIVaOG9Jt0oI'
    '3mjhErMAG8rDWEooh3YedzZ7LdpAwxc0qUPDNVmIiEeVRukQDlf4y54bFKuHJNk87bmaFG1A2ob2kLANrxG8b5yvVbF5U56gYeZQ'
    'f/xooSgsuWHbIWoZn6BnskVOkz4NRQ2yOduas2liSlO58f7s3XXIUMhpBS4pzkxsQsOcY3o2uqrZe/aHJBnxTTzTI/+uFwZ1EdLN'
    'qygjGuwFuDCYwFRDefACin5BvogFPx15EDCisx5/hKlGm0TcBDGKB2Jcogg9KSqI4bkE0bmW4U6HuPL60wttYQPFscNTim0Rm23y'
    'kIvOIadXlDNyckMW5Q8YEGYr+Pi66nprnfBIR37/5VlF8jF15Eg23eDqxqhcr1a0gqOpPzVy5H89n/0l2bZe7IhbAzeEzGLwrclU'
    'f6woAHL520a1+LWWjtkREKK5sGAlDnMu5JDQDkUeFSatZjHJpfqKSe4DhiTonFsP+Z0Tf3RjGGxmTs3VYo5dpWU7AuFDnn1fM1cm'
    'VBHQ3bmCT+xP0DTYpF/ja90vP4kyQ4F0c281ZmaXq/7Fxi+wauuqaJlSZllkJlwLHl17F4P2Krlw/sLIG/7CVTKx9418QbOK82Sw'
    'CFPgs5IBuR9J+pi1M2IZGDMfgxFeDR0ydvX2HLxwMcPg+Evo7EMLqdZqp63MpODQILgNCS1W8xdTPFiV9ppO5S8pvZcD61D9KW80'
    'Yfk812ke+5dCa+eR3fNoyJVtoF4Q95CFzO0ZD3MnTQxtlh5KZGb/HsTmHkajUG9xO6cRefzKvYs6PLbu1VvlHWm/dkjEesfeU+bE'
    'L/1Id4zXypxHXXToa41F9nCTGaZwB2nW7jU4sQYF9jKQwSC2Ioz5lxkbykD0uvRN38D8IKonWaA/im7Q62IY59X9/VqSnsUjXqkb'
    '3crsydGJay2X/mvxkm3q5v9vxVRsxdT8XDOm6j/RFInbmdNze7WRi41KbGLU+p6hkH0V9vqkM2wPuhnLDO9rWZabKjO7TU/707GN'
    'm3qr5+q+NvNkCbjScXp2mXSnfWfAhwYoNC3V6BYOvLOkgR1kSDVBr3hroZTwNLRObGwJiHiQCd0Rys7DDjFo8k0EySfXgT2xt/8G'
    'Rr8Wl9y1BF1aMKYgmr4CNU+jb5eWrlKxW+7jzQXBjybj4YcEpRfxx2Gvi+6Pi+41OufjhVEkA8eT3hVtWqN4LRyNPGAEgk0yYY65'
    'KDnSbLkqDnJgH4mRipcsUsLvFBBkt7XX3u68bXc2Vlub0f67H35o76Orb7S2t7O7tvNefH4vh9fizCtonGRxR5dqfQ0nokc3b/QB'
    'uxpNbqLhmEo4TdAnlK/vpXKJVgiCN1AxuEOqUZvIepUQrBMBXqr9LoN80aAfu8FGW7wDWGdPyj/WdmqVJ1V42qnty5MRe+Lz7l57'
    'cbO1yz8QTxCeKOO/TXvJpH/DH8ZJgx8IIeMKRvPc/U7G8pvyjVk2w5+JUIwuh4OEf7MxBdxI6Ffau5r2gZ2HvZJi9qOXpj+jrngN'
    'J33GNsGyxZ/fOvJGMqtJd6P7qREtLuMrDozDWTxP3x5wTbu4ttbGwxGCB8ieHnVr88EXaEEudiWX4mMop2YMSMKCjn9Rb5Jcpabw'
    'TEz3UXcRCRIxd/W6BfTrDaK3na3NR1F2Oh1+aDq9yEMQxQofJoPGlIH8ubuIL0vquzlAGKq4p774QmhojfqWPamuhgjUj8P2GZG5'
    'acBbZ2cJQhZOL4I46PNqomjs/sFIc6DWietOJL6gu919QxzKQV08fRq8GGvPDZ+Lcld/eTkzUL1acpbhS14oSsIsb/xmE6Of2+RH'
    '2s70HsfWl3ZVejCxJ09vMTP9nI0+nYTJJsNRpJKJ+/RC9NxPHOgJhzBwJVOlbF+8F5HcP4z3mbc58/dZWJfhNguqs5rSzJCy/aMb'
    'e2YJdMNyxvvehuXxsLLFHM9JUaz1PvZ6ZMLQQD7TYljXPeId/V7kLsZRdzv+2LtA1Jlub2zpnN/5cvBmAaNDwr9Z4mNsv/+l8Fvh'
    '0vRapfY1khHNCsoEmKlAUzoX5MMzRc8QXDJ9IqW1cYJn6mTVAkBDLhAqgMOVBKbc6ppOBREr3pogK24VNTmrMz9m2e+OmVvbaG3u'
    '/PCuHe13Wh3Ec1vdj7Z21lqbv1fkFCQhKO7FkKnp1rAb9/9pWCBvMAIy3VWcdirFap1gA38hIzR7KQoXPLHRZf2WZVBVNsGsWtEQ'
    'RwqYubA8yEtjf5zu8+EQHgWSh/tgHR4OEvHoYXaQfjfYUPeLzR8NOoEpEIWpNM4H6u1RJcq+I78BGnaKSUMjr0LSKBHf/XgBoV0l'
    'Wo25qnyb/t+meVFOFkYm9YXFc+Wh1mj6s0ymg9ApuS25NnGwoOjA6zBP45enNYsFItF76bw2ChcU7AvcW2Py50VODsuuc2lOcqrZ'
    'LLiuTkhbL/jLUNa4l5D1/0Q8TM0YlA+qUXpEx3wqnUSFF7QxFVxYdHjhLFhsuRxXo1NKf3qwbMZlMYrtD24IIcBRM4wWAbtrUSaQ'
    'G+0M4xRY/+2h0n5bjfY5sobRDWxajBzrTtTZIz/gg4lkJnXB1W0KG60MJAc69lE6BkzDx5pQoqUwDJmR7N9fgpA0XcJV/IlbENkS'
    'DpaO3MBw4Anv6jUeXqeKrUgn8+52ZynhA0r4NuS8SEqK1zDX5Kt4BPM4IOVHepR3+8rEamkCETDzXdeRwyQeCRCw9d4n4BuWSaG4'
    'VFvygPpO4/H7IDyZK82MiR9TSOKEYZDXFTTDfxZ980fk2L7+dikoeXXYp+AnzE0a1VMzKn2Mx+XFxRj9qCtGWdWITi7TfvnpLZQ8'
    'q7548S/4/8qJZ8Zz8gqulxExrytPYERhBp68lvyv0HpLf4sHH568fnpLvgCzV3X8XJQWR/xJRCZKKKhP0rO3k6t+GV9XZliI/yYo'
    'zG8T9JvcAp+8zn54wu5wK08oLEbj6S0O/+xfXiLM1AUNP7+jgZu9hCLqUIb8W9B2mixso8xbJo7rLLqe33vaDYuEK8Dl0ItZ1B/M'
    'zwdrEdPDn9m/6JTc3BO+LogzhAsH18ElmuLm8Xcv0ki1ex0ln7elKGcKR6/eTCePcqaFUqI8fpKZGP70Me5jb1xbZjL4eYn7p5DY'
    'KuvTzDT9msrf58/ifa2xGmHK/5u2iAjrwxtAyYMGnND0F08lDCW1Jl28QlYYZrTggq+veaQRzOWhP6Oi5pzr/e/xorXZ/qG1+ldl'
    'e/DnnXd72+2/Rlut3ai93dn7a7S7s7Hd+T3fu/48hNMkudmKR3rR4Jfd8RC4Bkz4dnoKC2E6cd4AitWxWz/6hYtKo8EQTdE+YiSu'
    'aIezRX+IMGIlRt9UnFE8PktruUs5v1mFa1mqXgSu4b/qYiZM+NbmZrQOizhab7cwfvf+fw1YeEYWV6pMxgln1aLg4NYJFpUCFqG1'
    'Ll0GI6NgyKKjczErkacfHXqf5kOjUyonzkIjqrwGjZNTEkkIKNTNiA02pymhLRarSeHyWvixbGvM9lTMarke1P0NRMOXVQE+yjF4'
    'uM+tWbiY+1Aq6WLJ5fDdkZ/L6r5YINv37v0mbYGsUG6ROm1ByiCAjIbAx5VUNIwkLiU40txRLMDc/9WA+24kfkfzQ4EXrQah8gXz'
    '9ZfkhqYG1aOwz9F0fwy8dT1BY/w63FvwPLpv35tCVvxCzSy5z3aeEjbYdCqKbC8oUiBGjOJhbGGz1kivGWH0wKxSTisTluGnERYo'
    '+I6wvHcjLO0B5S0uO+FDfnmswufioLy8OZhfQCc+pWXjFYqzQAZ3gQoETemVsezDVJQZnchBTqloTuy/bURLzhncCWCMoV6UsxLs'
    '/FqU+L3pwCPhaLNjAsMxWL1eVi0JRSABvNg4KdYvw2Aj+mMmyIgqjsfMK8qtyl7XCyuisuEnCZ07x2jmuTKaecRx3dgHRhNB6PTa'
    'zpYQEAxnlnSjMoaLM9r1SwysdN4bO2MiiZsFm3RYoV5Zno5y4PVFCBhGhQPaWgpYv6wWOmwCKu1ChS/OnqNJufrg3yNTuLGFcZ+j'
    'OnCA9ECzgBzidqe1sR39j/83Wt/Ybm1Ga3ut9U5UXl/7qYIvd9fWf39M4j/+97/Df8ATxbgccdZxhUWXSR+xx/jrf8h/ChjftOpN'
    'f3haPoV/0JW5nwysTzsTlukYjWfe7W2KyQmLxOE35VGi3JhkuEUGKjFf5uLa5Tg5J5K4gkXzOztAK7YJ/IHslZkqKwLC5h/YJKDe'
    'ww+qSVBipRp9vUQEZaam4nfzH201u6l4q7HB3Sg5a0SXk8kobdTrKP5HLWCtN6ynN/D46fc4FnYxJ59Gw/FkXTr9G2p0b31Ny8QE'
    'huIKSwFzYmr8aGpbxUeKcOdXlMEERMwTEdT2DOAr+6KZ6ORYErvzViLxZSVghhPK0MB44S7JzNm389t4OrnE4OY6Y4veuZycJpO1'
    'yxH/vKwc8g+PcZed0mVy01ieTZb9qlf5rctskmXyE8hruhzUvzoc3dAXV4IkVAX4uIY6P8rFcaxP+/Hgg5igJuMr8o1NWSEhg+9U'
    'ghZt4ddFzDC+yx1WrzPHheTNlR+Yreco5ZO+fwlDfwnRjuao54uCxST9iq+pZ4aS1bBKmQr1GIVsQ6PztvrX6F8LrcXgpdpvN6Wz'
    'H7p53vvEZjo1nBEM7Gu4NYJBw81Enze2O/X2Tx0PFljNlQdbXf+5DMnvIPkd/D2sHWJO/HlYx/cb8LtS78F1MxUrJB/fWhWdtTTQ'
    'YNCh4xPD+mNnF7mz3L9GJAAmcPRN8usp1UrRQjS/tkcBTL43+DK3DW8c7Cp6rJTjlcKhC/qtvuTV6Mw0GvdOihkWJWz92IujP2Er'
    'e5NS6s173O8vwo0vzSu1/vNBa/Fflxa/jw4XS7XHzT99dbTwtK5mEi4stKYbUelPZkjv6Yg1cvCWrlWasG/z1VUC6SZJ/0ZkY7Yn'
    'dU+0UYWuKKLxhWPrS0u8dm1xbAxBqe1aIULqh2XFlUQbKH0Pu6dMshLjc5gMuvK2Upq/9Ocvdk1uy09vMcOscvLgJavsMj5jBblc'
    'TBdeY3+7wyQdlCZRQmG+os5OQIX6KltK8XteG9oDyQ1TkNuI19G9OzOvcxQ67gH90mNYfxbJKEbP6if5ibzMudty2O8ukmbh8ypf'
    'kbrppFjd2VyLdnbb26XZyT31wR4QPJtfUV9rtRO92Wu3/jKvvi5LYBqZhV64hEs+tP+cxa3g7NTRa4zZPMufM2s0yuWxGv1QrI7l'
    'WCX+AC8wiuOinvIhrjwXz8mgD5NSImfIdvBzvPg3oHSHi8fRUf2iV41Kx9aUDZZkqWY4eCrNv6whcAM9HEhzj9CdC/sDhBE7X4da'
    'eoOXSMWAR1iZTs4XvytBR6vcoFCt9o//8/+J2sTQMjII7gmT8Pd7iXq/t9Fp7629a3eicu26+7eoHr0f94Dmr02BR8PQzxWRafwe'
    'R4DXpxuD485fd9vHqIy2Vm/n4yT5W1LG7WfYP/NQte8My1f4DVkI/1N/epHzinhk/7Vhe+wTve0mvM1yPl2gkA7PVP81hokN3ykG'
    'R//wvyEuQM73dASUKzcncxtkxpvzlaCX5ifhr/jBMi7qPbfG/9KHi9BZWpTDELTsd92YByWiirJJAm4mfOHSFHyT0ucl0a2Yl07z'
    'HN4v/gqEMVwFeJDjOz7Q7as0eGfsEfy3aWLXp34rQZKD11CrVC7VYMxZfgePi/Y9MjnyHh7de3iI5CTWxzKvV+AKIuYKNIvAvY5p'
    'NeEfbt4EJQvd3tg1nl4tuldV9gXOUIhVjAJ/vL7R3lzbz6cSdMhRdfTAcz8eUhCXvG8scaAe8ZN6m4avr4E4wyqNTm/CL2djXCHh'
    'W3FDh7enwMt0d2RA6EfEPfc+kPyC1jc9uHck56AP+JffZ96IAINngGUZ5oOIKvCTCCnMEDth7LU9ebaH46u430sTZFPKH+P+1I/o'
    'KpZp9IGDsop1seUtygfMWxxVynifOqrUL4C9eLocPX1u0jKfIc/DzeG1YXyDog6OF48WKHuUqQZNweWLb1SjOrOLfAgJG6i9VWDz'
    'RgxV7VSY/Op19B2yUNwt1MmgZMR/Y8N0V3xUYuWI7xLDqsZxstbi/kcOJmQ1zDlDa4CZXH9fnY7R/aDefM38GjKF2UQHP78+evaa'
    'Bibn8x8Gp+noJeeP8r7HV+bzH/I+9yfy9VXe1wvz9XXe13+bDs33J3nfv/r6+5d3f4hHw5RTPSk9yaY6HB8OmtQ73X2nzp/JfLCA'
    'rJfSXxnRYLTpJdles2/r6/yFgx/NulmIlivatNXVl53iIZGnkofvzSQN1cSQ9oBPBOjKyFRmfxybT1QgPjDsDT6Zw/LI9+IQcgjk'
    'bjLE1tQu43TnGi3b4FY5uanBKdU3uwBaQBd2+nkAv45IiKM2u4czzmK84m1FJegxeplzizKQjAqHSV+M8sYH8Riwx2hjTA8mSA0+'
    'wyEXDkHOpFPTKv8hfZo98tDLCygUTxvJ0DWxJT0Ar6aQgDxWqws/5i91j0LlDa5RlHX4OIzsi+OJeqO/ug/2gbhI+Gu0Zm5Gwk3B'
    'q0xTxgycvUCFuuTG98ft/lq52YCr0t0v6XBQeVrvEZXzvIuoEJRF0X3XBE9YiZa/c2Ff6NvLz5yovfiaTsRxfO2myB97+oRQc/F1'
    'zYUeeG7rhfcHS0dWzQM/1eTir8ce4bh3CgkQFHLjDODz8UR+SCzjjv/TfrbwnJ3whU1i/pLjAs0wsgUTf36xP5Z42NNRRsB9YYgg'
    'NQb4xRBP26XUsXT4iwbTDBW+0G5Iy7Y4/CJj+rApxA0ORVexIR2rZ/j8ucylHNi55aPK585wUVm2IGzEWXx2mRgMLy5N3unjxjSZ'
    'vtQm/sz4hnGUpNuZQwhVQcpWzuWzHXCvbOiULzvuzNmmTz66+cDfh58Gn702A0I0f0j4SPGITv5hMPOW+MDw1V2R/xXy3GZlai+1'
    'yRlqfv+CBmaZXVKDrnXLZHz2urhUOvOJsfUaUlFbR1fTLO6/SnZk4CoLdtzqcPARuA9U+fGu48gmlv8WVAnusD8mmt6+/E1GUZSX'
    'OTKnA7/Yo5e+Ln29l/S7fk59F83LTdufKkT/X1dKJipP0ZLLpVWuZL3iTFFWae3XdKs6UeWaZi8Vose/TSnQIMHiIYnCBufTQkXH'
    'NM2ROHhyeyGCaWH0zK/jnv3ZE3y9ir4FGtBT02Z6ifVV+QkjHfD9r1Yr6zY3xSl5o9vw+jKDIm9nFc7Uu0Lh8lYyiRvOppeu5w2+'
    '1yfjLox5qWqVARMyo+yQSNs1gwbtvNdNELkMfSPN60GSdNO95GMvuVboQXzZwJdJN/M6ThFK9KT9adTvnfUmWvb7j7//t6e3bjhp'
    '6mf/+Pt/F0sBZO5Pql43CMm5wbuLv8yq1qDxno3Jc0yAQor39FeAfMVgEfQYRGsMVrM2KgmNUm5nxgphnJwNLwY9hiV3uOrD1MCq'
    '0DuuzoKa8G1MIid5WIV0iTPQx8NzASwKeOXMN8OLVlzFCzZ2lVXJ4FBRMwtIm26Virthc1Y8+1vVcVcXb15JX9PbmJ4P8r4dkQrI'
    'vHcHD+lSlT7KtcNBIjJ/4lqCm9P9qnsYvWZoKtGraKn2/EVm2i2lEQ9ramJVF1i8ErdjNExavUzOPozgYg0XbnQmqeJ26aODbIdN'
    'jpRBlU1KkbIgcbPm3vmrcCseUWAG87VJdise3AsmcSvDvJl/yZJUlYL1f/+K4WLkICdOJ3WFajswKYeitNiZzguY6ix5cBedjuPB'
    '2SWRdA1k6gZiD6aGHe/dOxqb/clwrGZjg9ESOFx7mNkdCTkFz5eBjCkZ8oX+IGQKqmTiG9kUuzGJ8gyhpPR6KdB3Wdf+l+ORfCqV'
    'AvB74m28UdnljQCv4f5ZPz2slw9+rh8tVA7rLk0K19LD+t3TSt3jCymXlj2oaaFvcFnI6KOzYgSZUzZb77ZsfNb85VMAqqJz271t'
    'X1ajbZJIUqYmM/3NGsk/+Y3LHr46jtW7M44rW/GxV9XlXibL29w0ERtXov9V5yDbizm19D3pcg4bZBcCylmVtswy7IZoCsSekVLx'
    'WWokI2kjOjCTqT5HQu8eKUOARhRsV/PVkYM3shgadllk07wzw95wEyjn+1HeAQ9HAGrz3NismabnklUkD3kDussjUVL8AGXXRyj9'
    '9q+zk8vx8JrCOrTHYwQiVEUibYmuxLwoJvV2xBkRPTMm8qqNHAbBsRCw+g86NAzlCstyNDP4oFZQPOj2umSO6fMx6O3ElB37+R62'
    '7H4ifju4SeXztoQSXFKmHfQJsTNECDti8lV6CvdXmH9gXIdjrs1TU3hMzgNFgkalsUwxQ702vY5eLKF5useRYNGSCsXGgRCR05jv'
    '6JbP3733XDrzM4/mCGQrOfHqHnRY6joDdilHvCur+wD2vx3bIzTXRyzRcoXE/vlSWLlOG2whhwVu7JLMwmDeyicxQlxkcmcZMHrW'
    'ORRyszSW8paCX00uZwdPbynB7OhErRNPI5Hv5PXID+nS0ktMD0uVW+VFHILzkggotxcJ2A69MfowvtMNs+82GDNHJeoZvKWQK3Np'
    'VBZj/2RfiOxSJbHCyvRlwUKjdlVMNAyszXEqtv5AaPa4iMPzVysVTWuVnlh91DUh3CHHQa97VBDT93NXvNRVtOYzK9GuUW9FugjM'
    'fK7N1T1UVRSPyWXDLsKatIXsw+3dc5YXPlSwqrLgVXoDC5hQzKNNyKcUV5BS1tLhVULAViThYwQnf3roQ0XftfyyYEJNYUp4m/Ma'
    'NQNMD7+MKpniGMLJa7HXxv/Y2WMWMWfe6LYoXbBUCQWcXk+YLNELR5dqT28h3eyk6lOXDGEiPksIGx7S9lTOP5YyPETnMtGsiTHn'
    '6KG3+lCCyH1ClxgW8kRpfJ70mZewR69k4hEzt8aaKcoRB/+9RyKawccG/34Z1mH4qoKJ8lpCh0tBQh4rwinVPI0KSkG+faueWEUt'
    'KqFA9g3O42P7y79C2qn3Usv2jeHufzEoq+qqrh5mqSuKb2PbuFXNPt3TqoJGaTi8JBkIw2WZLf5iOXPLpYX1u2Vt68nKj6Qa6GcM'
    'J2ii2yyNwv1tLlSwAxhQABbN7HCK69a8QfPqE2MhQJ+WS5pKuSoQoA+6ReyWfRuwXJQA+S2XwHOvkaXm2motgcuZYdDaM1jMajpd'
    'Lm8JA/nge1UkDAgBqp0E0TXVPctbIUjE/EVicCK1zbK9Dxph5rxWW+LWDNef60Fut3L7Z0trFJdWnPFzrqTq/mhYRiHmqjorMzO3'
    'R3/9CclWojtXppEDZSjn9lCHsHJbhTwblGxONdsKmCEVnPeM4ij3Mivk8+/J3qLBu4ep52DpyPTN1U0XVgPmUnxbRQJa/BVIQ5ze'
    'DM5cjOZjdO5xKdd7QEHRJkHLDU9vmBzhCL2Dy953fILH1zFcyzBxjW6hb6bn50CinBiO8tXw300TTuvFEkEjPv9G/nzWsdXHuEZj'
    'jDnBAb+gsK035vTq9656E+8iHF7YqaVoa3GfWUTh2jS3e1dHL/3XHrLk3FXHMX2DZyO9hMlkNMdPL5bcy2Xz8ptTdRDGN+gpoLxK'
    'STyPVWgF7eNjDiMNs/qpPbhAMTorGGCxfGrW/rxP6XPH9XSKiCden+IxsCcYeJIsvqElU+AC0e+L3JRqfkzdv1FneeKxNq6shq1u'
    '4briKfeyZLhakbpBUXio8RXmdmY5f0xP+tjH9FRDlHR3DoS8KSJQPID3MZ0Ul0/mgK7iwU3ETchlglwfcHW0bT+kDcaELmw3LCpM'
    '/9R4MnI32DkfZwm+GzPP2+Xqd7O8hNY+LwCeDW/ro3FvCL1E3Tb5q2D1sKJlz9wZ6nHHx8Od3BErQQu5bc1oCUj6soo9yGTL1FGO'
    'pROL7tWp6xd/haWAIIyrwFzCeWK+vwzYZ1rFalCLKXHBPKJjGS1SmVBavRj/kMVjhmag6MxOpZKh81wB26rbkPZ7QBKWGNQkvNV0'
    'k7M+HpD7vb8hKRGZL5XTrB1jPc0akFTo9jhJU0lHAl19i/FKwbUbEsMwuqKn4+Ztx6uEqHjZKuFCmwq9P+6rA4fi1tIec9DivDUi'
    'tySrNJgNGl8UJKSJGG/AnEYzOHXJ//gYxm2Wj6nldQVnGJX0a3CWdhGdhR2d0BnqHKrpi84X4VC7lMQjLNRiC/eT125L6gua7U6A'
    'nw+n6+31dQYkr7gLnu6RGajs4oRDqSdesm4JqvVK3klm0cL6o9XJCAR2Xc58bGeWrKLGnQS/K66HJF2TX7DTH6nu13gF8jY/7g3O'
    'hwSh5H08Vdc1/aV2GtokVFjZh+vXV89x2+QUlBg1fnu9NjTNne/Y4ILoYpjRM4fz3GLkx8S/x+liGBHhgeWwr0HhBVRz1kYnntNz'
    'baoOI5tJgVQxpwyv27llqBS2DI+XeeSz0XOvuXZgchphvulWNHNSmLoanko0e4MUbpF0MpohxS2zBddAfdnNuZi6hS4XT7fWFfej'
    'ly5bZXkz7t8DNaUQ0s+8MYun5ih9dDV52hGS/5iyau5OYdpu3uSd2kqZKWvNYu9klVyBsjUYZeh1r0+BsU3yZmYLnDZrB+bzEWxt'
    'ydOwm9udHV6pTUFE5biIFFvWG9ywMcH+Ccoi/sQzX8qrWtks2BDGZmzMzVelfJmXzrtb+2+r5gKpWzzL84zPmZEdEe3n98+K9DOw'
    'F95GRIG536amhXi5/ezexAIE41WR2x83xBtdvyZDAzlErR1fuxUQRtdl1SPOkZZMRui6sEU5Y/dOa8GBYX9t0prsxWn91kaZ5qWq'
    'ee7C7DV0pp7DFTwL1rKWZdmO/FaiLLsk7hNgzRVi5UhGMt3OZWRmVhISDmIx2fp3GJUHjUjhaMwbCe6sS5F7nVL6qZbb3nFm5+Pe'
    'Ppyew//82yHlfKMIwwNyyt2KKw0uTVxe1dleI1s8gB6Me2eNyIZ9/RKh1nQkQo188ZYVXCH8xgS5W8XLemxrrkgrI64KhU0MuOrK'
    'ZBlLmYA8tcAJ2fcwmjVd1OEkY5cF75P4jimnwscswnLrh15mxT18/7W3hUpOkJbVy+EwRcOLkK0P2fkqKWK8+TU2/Y4NUQXvCfhQ'
    'Vtb1j7//X1Dad0tBBJGekUiZq2Ch7M6XNPcl6BsxHKaQWrhi0OgBmYfkWnhYRExXFr6O/YvyCpnH95gr9ITbgZwX/9hdW2c+c518'
    'ZMo+ZQmUv+xHg/THFFSTV7i9oN9X1tiA29eJT9fHwysCcXNHCNox9NCAeP8vexu7nePdvZ0/t1c7xz+29/Y3dradJnCembPVKvrM'
    'ifvMLauqswXqbQSnuvtM7uYNNGDxQVkaAbF1n7mLMFU44Q3viLQ9XK6qt/O7Y75vxqcY17WUXZReYmPmzfPWyJ8Sv3jB1zU5wgHy'
    'DcQNI2GLdR+ZKdAZzWpEWy+kd2uIX4xxfDb2d0w0EJd+ZnW5VY8xd7ukmvNWRPZ24XtkLzhyw/0qmL7xqVzhEQEYdgf8QYt+5K1D'
    'LENrma1KwDhkqpGaK1LJasF21z9f3pPB8O+5nQzMKw2JwSgM73t/i8ddw887CndiRehPbwvJzkzTP76fz0lttXClEpKjtDSLEMqP'
    '7f5z243W/7UTCu8tUMWGIUrwWMwh+Ko9IhM+Bw4f/RAQXYdy1a6SNI0v4MD73hb7XwG09PcLqhOwKAZ6zDAoecyJx5ho79SQ90jy'
    '+RRjzh3zrRIpF57ge/SiLFwWPteGBmI3+YiEg1elaSIDQn40dYyTdNqfVPOVXQc/1xCXj2WdqgL800qpJMwH31keG8BD5FRM7kV8'
    'GL7tGSbOwSjvosRVtMEOGBVuosk5hqc4741ReuCwPAl3EK2bor8kN43oRxqwUQzJKlKkb6m8xiJSqxe2DaED6N2AfndLkXWdOR12'
    'b2xcWd/G+g02bUus2ElILLbrP5eBazw4vI6OFhoHPx8OjhYOB5WFyuGgbvnvoADfXZT7vBLWYk3YVRu2EHCM0tvK+eQ5TJ+VawvI'
    'sl553B0LALYyuVgUAO1OK83CzISRklMlYcQeHEdHTcKJLcouaClbYXYDEVucb3SzFWWrddCw2Zx2kLcqhpvCua8ZRDczvFsYgDCM'
    'USGDVNEZ+R1llM95OXmE/CoZWYYhs+lzXkYzNhWV0aDLsO8Rfc7PCsNTibw6BX2Gkevgc5hPLWvRY4WLbenImQeJvsFt087wQ4IW'
    'DVwObJ9h5GxFw42nvqxQBhthdHD7vDqrVyQirtrWKy4TMIL4PBmOnSz4fDPH7S25Yptv8iFkN0bhUTkuJWfSJoAqJYc0QIrTkEzN'
    'Gv6SDzfu7Y28+uReiR/g8TlMEmrq3BfzhoJbPq86CEKMokMxCa5idPBNCEXXRvQkteuniZCg3sBimNoA6Mbvm7z7YoyYEkekpjFD'
    '7VMUfM8+p5gys4Ie43et6HskiJvIDY8sriZM3iC5AdYNbQH51h7Vn6GYMXpWf+RAew/rh88ODtPD/aNnh88O6wbXlSpRkV68CTGY'
    'hoKjRbPSoHbL+nxejRafWy2GY53zRscy1UpvOfP7dHBwdMS3KN3wg8MD0/Cjw6P/LA23Lc8CL29sd2oUh4H+1NZ39lbba48+Bz/5'
    'AF6nR0aywQtBdEiki+KeKATaGiPQPs5+gC8ZPbi0VnZ0pqCmHikKoIq/zUDY2WKMQYZyitLpOQK+Apt0UYue0Ajs7exsRYvRWuuv'
    '0VfLXz2ZO1GCOigTJe1zTM9XBz9/dfTsq0zQ6V81cx2FWovTRkQuGdDIMM4tSodeM8B2V83f64PocHIkh9tnrEaNiJddksu/eh/J'
    '6lpvrbWjnXewtO7ocWO7wQ/Qo7vVdx36u7/V2n8bmV9brc6q/eVEar+qV7/BDK2i5QLcPMneIHrdgU3yClb/YDhYdLVWsjODIGAL'
    '/Pjqs2bIYBPqfjgjAyldVqADaTMVsdnZryImIluz5CT6qhp9Rf//SnXzq9vl6tezw/RXkkLXs68WYGv9Fu0n8EXgAoSNUW1e+dXN'
    '/S22iWnoWw4adgW3rB6FB9AMEZpKo5uewyFdCELmLTi2oIehkeRKVNG6lumpYYi49cReCZSxXeAa6ZSIEIaY67P3ehXB2qMpomIT'
    'GnSZsdGHBL2KcfuEiv+p8iiALz8f9vvDa9g4pzdeQ9FTQTFxO3v4Uo2BCXjhLslws9tk3s/0h8xaFatiLChdV1bMQfHzn+pGNC/l'
    'kKVDwf+g/Uxp2UD3T1JK2YGNG3j6IwVTf8g49c+eZquC8xALzSDe2yROZo42ncXfX0Xfegke6yMcjmuirkhZmaoyNb1b29jf39n8'
    'sV3Ja5kq67CW03ZsOBokueMIVkFv2I3K12TaiU6kRCrqISGMooryQDSz5kveYGTUhN23FRVErmxHN0KOhPxpPvlAhdd9m3IrWIm0'
    'Ic5Mf20zFuyShuN5hNpM+8ItYCjuhylwxQ0chnTSg52k2nOKYUNRMybbze0JeBeTFMcDIUYshzRx5EwVBWP5P88g39/214Qudut4'
    'PdQHYSqeFxieBHYnjIpPEGEmzCQ8sroTY6gJufEeZKrKuqumEyYwuSYlj9NJ1tzRXg7KtWeHlgtLw2Aj+WMdQBfLeEMjZvNDMuSX'
    '5uCYCwoKfGALJyYzFXMWEUZsILGb3Mzt8qGVSvo1aZYfQeOfsgaLp9qe2f/F5/yzSWGL+UAkgOizfcOBr7B1j+YxPC4nsjCIFMfH'
    '+0hYCr7ofEiSEbpeXGGwAaGAjnJ+CWf82FsTM+P08NiUZcwZgnBeoiqyUR+s1YKNvkAScD/MlxK6M7SUYbOOz/vxxbvBWTJ2Qv+k'
    'KxHw0rK0hbAcJbSDdjMhTeba/dptr1Yq4JjC466tM/6V6NG8ZFUr9xFRoKB6GTl3I5SFVh859bNtE7+0GmDbC/3eaH6tdMjo3iQV'
    'N0v0oCVusRMl8ZiVqtYqRakBMUgFajWiJxLxy7V29oQjfnJpT2/9WcdNJT7sojBgDQSsu5Pfd5RAHW6zdt79VNHxAtfXfiJmYxD9'
    'tLUpU12L3icRq4Dge/R9fXkpKoshwMqT5SeV3+NQYZ8QkWD/A9EC9r77x//yv9IIOcaM3gsoPnzR8TJuye81GcCSdv8rsWDurYTH'
    'qEr4XLSocGlaLhaBPfzM99KqFxrCkHybvbSm4zB45wumKe1mAiQ4Vl0KKXX8GAliQKIa+INE1LBxBiT6UM5XFSso52t3GvcXdRQL'
    'r/UUCzAqrDiMUNDwRs4GUGjkZjZhFHK+zjwMftgh7fQMDvSxB7iPL8QiN0DA/wMBoRNme+bbK/7Wn2Q/MTo8orVnPj3hTwTVnvlY'
    'kuoQoV2Uqm457rfW28e7rf39ztu9nXc/vFVm8Qc4CnIMwW8kfGmpWnpLWtvWoLs+HNIigxVzAQT8ZjgFElx6T06ipI+AX6imlWcs'
    'bSs+Gw+xkBbGOsSHVSDS8IcWPdvd7JCcAL8hmU/leR/FEKqk9zFGXozHH2iTlDAgdAptWhW+pIt5NoE1SLrYOioBUgu0cqkTX+Ax'
    'UHp0VAmnco1Wy6pg1JYHwy7colxwW5lcFcgRUyBIGWfAGT9wSCJnDJEhqBJsamkdOFyoJK8FOGZ700FatkTEqzqnkTYhzDMB9DJQ'
    'DrYM6zYaKuKA8CXZw646yJYS8EeEGC2fgY63JsDfwnUzKZf2CUu6oq2qxjIziIKVk8NM3MaazYa2QGgrnpN6Fb/45aO3w8UYuarc'
    'HG/sZ1c+asdyE6/DB7/0lNRqeT2FDzrprJIzPcgjGPcGMj3m2WFHNpkj5fDFAGsSdrOJxymVfzsrha5r1qx19pINerxq9zkGrVdz'
    'Nbqyjie3KnopXr/MF+V3ZV/5IH9kIW3igmL7Vrj97JTTO78p21qyo4GjJxgxqbdM81BkUiFNsjkQeIUxjBiuxGJiebjP7jWF9vDe'
    'WNrKOC7sc6eKPAGuDl/OVoD7M4TaC9dRmT050aEhwv7tmq0F3I6nDXaDCRPG0BSEdlais0Kb7Hiw7QghKDlr/gdYFZo/OMDKjjgQ'
    'ngvRKjbf0wmiuK1EBycM8jCYzF7ZlnJPeWJ45xMerlebAQ5s2MawPqwatfq9iwGSfPcpNq94++yT2m07uUbK6lKl+nU1cjTAJXFk'
    'gzbX7PXJkQ7EIr5gpFLTS7hGr3wlNCvxVoI0fJvk4ZGQgnaAougVnTISWQMWpTdQDBLQoGLkBlCNqIf8ihT4HGVZ3vAdAnuhPQno'
    'Uzq9gtPmplLYFGwMp3ntJo7maeWJ8BlPXr9CWv7aLVy/7NmrOn1/VbcFwLMp1bSpcCzqwWBIDgd8Phz3LnqDuI9HkQ1dbICc3JTC'
    'V9S8ei+ihmdMMeYSdIFGVgSz7L3GfQzJce/Cn5qNBVlye5T9wYySpum3E5EeydmDQwtgkcY2XIotHBAczOzWocOvgW2hA9Jb1/jW'
    'LelqRAcZvaXDrhq5c4reulONNxKeTPQBz65qRNYeVBM8yEZsuH2h9JVogrpHsaHILF42k1sowdCZlXLCZndu8ohvtxyLjBO+DAeK'
    'mhtsJbz1bEPaz1jAWLRtGP4oWsSu8BN0N6Vm50+czniinUM4eZagE8jMvvHiKTt8a+/0OjCxUmxoMBf0ywT6kiheKm6XeXzuHr92'
    'j9/Aow3kJU/PS0fuAJNQAHI+MX40RTyQHZAJoWXtCbRn0/J5eI6dToFPhLPFOFz9hnHuvVgnDw5jb60OA9t0E9AJ/xZZp4veDnjX'
    'MVx9BxcJl8CcleN10L6deBkfDMy8bhDyli3u01XftwIzLyRk7KsmvIicRKO29CRKBmdDvKKvPHnXWV/87glClgy6cDkdwBYYDJ9E'
    'zdcsqPPLOnm1jtSKrBwjMyO8b9xGUd2zVuiGSSgZeN3Zk6iTXMGSmBTmnch3yrc9pDw/ml7kZ5FOUo4XmEG2VTAiJWt6JlZ85joh'
    '0Q2d3V6QEWiHJH0tZai7lF1Z9j5VyY1qT2As/dpZP07TzV46qRlolbIvMFjEgNg6nHWmMdAcR0Cco2ROOki5BmUb+YNKrDoAjfq3'
    'aTK+2SeHk+G41e+XSzW/TXA4IHAev4Uf0D6H5DbsT68Gvtu2Nz74OWdwfNBopZAg5j5vnFiETdqxUo77ZwCZMcJVgSEaePHh2JAF'
    'Nt1/MqoQHV7FH8larZbhqr37x8Ss8kBVUS24e1WjkpX96PDbs4wvatGk1gtmNW+p1PPWig/fake+YH3OGff7hwrKzAyU1XAUzVHS'
    'NzOUM4jw0aF+5+7Wut6u99OBjjO3D0x3UX2zI8wapULumlAdFcEy73+6Yp0fUPSiU5s5wZyvukDDHVISFZgqpymGSmSGAD1vihpp'
    'DuCXPuJMdhhtNfnjSMvLH2kbF4YrzG/eiU/ChAOjyrL8ly4tj/M68WIjcmofHuAhlbP1v6n9vQ2/WljhlxQbdkqa+dBeEQv3OZ2i'
    '8xp9+4oawCXOr9/zXLAMB+c3XKQgCprfz4PfXwe/vznyRCoauVh5AgTazAf3WpwpXJ+98giMmwfBMKB/+Gr565ele4Yhl7LOpTKY'
    'INxAs0Ji5BGAEZBg9EafXlyGNx3DqnhshbwUyBAgP3lScsYKEO9QFg471tO8R5YxP3BiLoVR2TRREYimkMzuj5J+nxDwNy4Gw3GC'
    'p0waUYil3pgt6NbXEFnuNEGBWK9bmceR5ZY2h1C5VPXiCfuMQnNfvqo7TtnwinLfsCnl2jPI6DXYWTDUtoWx5639tqjY3GHq1Gqe'
    'eYnVpvnRzH0tWtZowynQfLNjjDAPjZiemhZVI4lF39DxxjlWu67TC+yt43qrCOEuQDiHB4elye+NZiurx0JFud2xWq0gyLvFQk37'
    'OxCpk8Klki/GRF1HkBt/+5GlM2KkAhWJhjJGXRLpPu5TlgQysFJFPCmNURDJ0qQoV6zwJEG59juWyzmD8ljc8oBGGemH1eNMMnoc'
    'TwE1IUWGsRh5c9OJL1DJVBZlkK8NylcAOfka6z3MgWLqtqIbTZsk9o6ShAssnJY00yuWLjeKVsm2iauttDRW6lyYy4qqA/WOJ58u'
    'yuxJsQu1W0W5czRcnBUWpfQYJ7tqgNStaBgXSCWQWtuB6ysZ9HZWPcUiaqfyGlnpdE7ibLcmTnadk54jBvsDyau4ofdBU19H1Yff'
    'cAFamWZuYMFGDnU/EEpy5F2I3GYZF4iWXZ2cWAISjsbD7pQKedfrlk+g8EUTzONEUsI7q9bIxCq8FVunEqQqVb2ghA9uvMKjwHiF'
    'OlAhByS0AQrNTwpMWLJxCensjFjM5Fuj1Eq5QQaF/OvbcBlFFPOIfwE142wle5IIHRNlOkkvNgyUu3g7hmcPJz0x4w4T4LLBLDwi'
    'c3GFMjO9osPhAKPwHBwdGY9rI0+JltSRvop2YyYal+tLgTDFKFVrThTvOAI8CxYWgpJfoymyrdkGJaQ2HvDfI+ZxSIThwJTMYqd1'
    'Hpi+iAUj7vviZUpZ1Fo1tQZzTZppLRAGfooDA99qgEWxBVnb2SJP+nG5wjptxLURIbVkRH5khAsvJtt+eOuusFCQLxMrl6iUMYFZ'
    'MMXBNEbOKVSkqYwlSNXrmMFS5T40VOJ4vS1gkWy08eR4OJwwpFhYuxcUcMKaXUX4MKOWwqHw2iNvvqFHSShdyZehE+5ULugwmpAR'
    '0kMGajg2tqeBvNXrlx/IM2eDSu3BHrUhF7KMXwBXhuvsfkZGkxLLCuk24thjSc0HUJ/GQxjUl0U71t9LJvCdZmjcO8xEK05ocUXH'
    '5Ax2bF6QVIWoIBKuX7Fy7K23FEblW7UL01UF1EjVZd//qqWqK6tkipcPOSJpd+gEi0fiOZcfcGVABVd4GQhjL+dfB+Yf9xmndaVm'
    'JT7IhX82wjc//kUQtNUvQlSGJBLARmJZ9Z+vrSDM+qlSo0zRscXKnVc2iZlI8WjyMSLEPdlEbgOZfq24yQI9COzCuGmgSGa5SyY7'
    'kre5+Pw5tEQXk8NOeAvMYqzRKflrFoUB1PqC+4egU2WjCTCSOVXnYZGMk25vsiGx1W1AJ9ii9E6h+v+M0IG8gO4ceuLdBI5UeiBL'
    '1wgfK4fpglpiquZKXiCXsm4DOhQ2TTuAXjdZWd/wmhb2yo6T0I8EhW+lCuf14vCRQFJXR4ESg9VvatcJF6Jl0xZVnPGmuIJzkVEB'
    'Eg9M34ZL9YuCJb5c8aaBVfEIaWHKCjpKw39mAGLu/sf/XSkeXuwkF2i6ZuBTVqQiFfFZIeHMq/7wlJIcns6vVoTaPlmgv5kqZTvP'
    'q5S6TKnu/nR3uNA87B4cdqNyZfHo9tvq7J4RkJy/CbmR51oR2XHymhiDikGOLDSsPe0rnsjws71oHDQk3i4sKGSQH4MxsDcPWuoQ'
    'OGTUyCTi34ZmwiTvr/90eHp3eLr1bn9jtUGPre3tnXfbq+09N/fcSzg2bO1w4HR7w5LGNx8Dq9P7m4X2+mlrc9++0zI1LR2fw6d4'
    'OgbDPRQKxn22oqJMNJ1FMkVK8BNWUazbcG2v2cfOUK4bmKEyq1QykgGDOlkAqxl5N3KRhARRo1zMHegYGRQTRqQX4Elf9Q365a2p'
    'e7nq1aIdm0p5VxEnGhBYyvwFUg3AK+WtEhCE+dynqkKnLAKnnDmJhjlDTY9oEfhnnliPyIm3bFE2tZVKXj5t6SKZxY6lag9utlXJ'
    'y23sXCTn9pCkX3bpVnVwZ1HMNhxX3IzmLqqJUwA3FG6opzlunKFdj2DTEjBcWdbF7azitDRZkQpcnrdg0fbLymjq1sPfE5wCQ6kU'
    'nFQj3zLCd2l8iGWGm+F8I4rgOuPMi+nGlmefk+PwYM0Hu4HwhHb5A0whtIGfGRje8ZWAry0sMd/4Rxds2cS5Ihbr5UrSk0bg7fFl'
    'Jj5I/6x5z8OMe5jeemfY/eOorHCY35WhzC+PzkQDwKDQVWcPsqWMB8MB6rhoqpwvxL0X8EqOXDczGWb0uSgj45Pl5o2mJLUKaa9d'
    'NCKzXHUFFSweGfruPn6AybO2Tx87i2YxSs6YQ5NVckMojh15Y6B7lC/qdmOY3fcFRWWNRKPgZjPINfx3bkD3G/cX6EpyzPxD1UhG'
    'El++NQJ61QnjjGStrs1rVZlve80JgDFQupdGgZ2z1qhZtiK0SzZaLlGEkJNmoLRpWnW+qG3878bCXetqghQjN5bCkgQJHG9iSZLR'
    'yQQp5bW+hkqIleyxRMJROEyBzdlDY/QOUA8nyE0+jYjbIP36Cpag/Jvy8eALxcleJD4pF69pugqKpasPyvlGyD7+6NmEBZEWfLnv'
    'Gab4dKAaXccDvwUFKXUdV72UIEJJSMEFwMLrTmGLAQGaomSCPImUqNSeHqgMWIjKgTcVOx6RiDH4wv05oIKO0KtiGSZxCRq+xNFL'
    'oTC61ManaVmaIqtsUcZCw2yqOAnDDw3djxXSh7g3VTebM4VSbUGqbUFQDqubVGbgexmXuuGhU2ec2ATbeO2nf7+4C58DckyNR4EI'
    'A3yqEAw2JiWmpdCfRjxvw1H4QMllJS/PxoCygdWCTSO0yIIiI5KyEPVKcWgBccvzYqCjyQ3UkLvPs74ANrfrM5VQG36AFahh1Ine'
    '9D2IBM/XPa2dYPhhQggwuQgTC5V3WKJbNDPTOlwZ1/EYBRDltOJhpeesQ4Xr4GqR1Qe1+AsQyvojlWV48yLE6cBdgkNqQPmenwRZ'
    'c+W4UtjFBwkyQCEMfzIZSpk+IMiD5gtLdUojMy8sU4Vb3viqfEKJFwnaUg0qY5LkjXy3h5Fy8XqIIx61qWlRPLi5jm+aJ5XsBvoc'
    'jw4rVgwu16k4LSj4wZ85Dunh4nF0VL/A4LfHnmT+uDu8pi31pj88LePmpYcDGJIjDErDXGOgd3yJuli4Lq0whjjwsXK2Au0sIa9X'
    'CgBCStx/WKpAn6JxZiwN9H6mkN8vAMju2rqA7Udsxb/Yj29gBUjEOdIg96dpRJKbaGd1j5CU0rN4gC67yNWkiPhBZQFVgzG8uGmY'
    '3KwSQQ8fiWj9qRrdMH+0eN3rwulG+VbxngNnIhoyDlC+0aeY158Wh+fnML0IVnw++ZcKTZpR0Y7iCdxvgMHkmnV7oniMQYbhYBXj'
    'SOhj7ZeU59yF1KYe9W+oYVRIB+OpYrMhcS1yyD/EukGnVV7qVz+JP2JE30vEXb6CSxNsgt8l+AlvdxjF4z/vH2/urLY28SiuwwHd'
    'HY7ro+75Lyn+C4QHrmW/pHBGuxzvd/b+0t6bl+t6OP4AI5eXGapbXdvGbJeTySht1Otn3QFMzll/OO2eY4BbuCpe1eNf4k/1fu+U'
    'y4Niv6k9r337x/va9GuLzjT8EcqJj6ln0YrEPHSvduEYR+Tz8Mt7KmYX6XL+J6SE78b9zFc+rYGbPUv6fWJ1BWWLEjDNhg3Lhfi5'
    'h2fj1ekYDVfxjmeUUks5QduRJsOY/Xm/7K773B97r+efL72P0tkgjbwlgh+MSZkr1uyUotubQ4YRRWqVUCByjlz1bRi5CqnC1Ygj'
    'hQqrc6AXbjWzKG0gpAO34qrBMpE0YtOAIwgUa9IWLtIFt1QgcwdXw+60n8C8wVWEZgAej8guV5pYUXfKiaSR0qoIdebNuQqgHGDU'
    'YUWmir0kHcHL5MgG7pIBrgGlKx9kIhmVbSO9MEfnCTJittV4/p7FwE8QoNf4LFmkX3je2kxHITie3yDgY7LWLyc4m9JvXiawiN92'
    'OrvAyQTZ00k8maazk0xwUk63yla73OUgK5Jq7a/mRvbd3mbtDNjDScL4FfBbcR6uZMeARCUsrf5L/DEWHieaaUc0N4lQDO+7stSn'
    'yuBBL1UlgnQpJVCpRdgQi1xAycPpg+S1H6CQuM8lCmaOkB+hG/zjoZn2x2ccEwNb5jJlqFFYah5Nyi2FCCC0IRPiXb2zDL+GRtT7'
    'SoEqMuAKNweVw2MguqTesLAqKiC4DULKLavQRI+Tj8MPaqLNxyDa1KPc8NvuWki3PuEnmBAxx1i2DW+aOwmxwtPBhwFwtpHYv4m4'
    'ldej280yOBJrLySV+XGk8g8V13xKbONFOYIOpH8DGTK8Ve7RxbPMkYeRzdkWYBA0N0UCUUVOr+8FJWJuzo+gEXeNZkPC9JyeDj9V'
    'VZy1iLT/7qLM5jxGJ/MwiaaKOsHWBtqdUu5tS1CqRHTDJjRr8KbZjPgZuUj85Z8YN5k8NyrPZDjKZvm0nKlmGVOVobYF/wNxuRJd'
    '1q82U8YNl3GTKeMyQVMCvxCahUDLwYFLJuMGP31qQHPqPIHAdjdu3C/JQY1rWNOJ5Sr0YDlahGGsmKT2XLAhSmzy7yD5DSa/KUiO'
    'gZVKsNyA0p0O+8Z4GcE8Wwjn2VgSSalaeJIb37ynxpmFyAPJGd7SeLhPPD4mL/E2Tl/KBdd66XpvAINWlpF1S7OCsrfsWxTGVbWO'
    'RIUdRxjSrM5AQmDTRyyTI95zWoORwj+t/kziNb2O+KmmbK0DTZu2f3pkw2uwoVLfiFZ1BqP4ka3pdAes3a7xDhVtixuLCrte0S7j'
    'NebAW8Tljfs5ST/mOrzZY7mbicce8ZBAzsCyw6HmW/wWIGCZsJ7O8hs+W6z6SckLZCiJHCz68nMcGmORvXTE5p4vyC70sXm9bKMc'
    'hd7xxp35hkMcUtnS3Gr0wliYNEqBXE5Ma3ggKK41FEEK7VtW6aDt+qelxgYMPaxLuBTf6B+flnF33NC/Svl/cORCbotlLdC0Fbt6'
    'uTPfHqEcZDgK3/8R39M+Cr98h194G4WfvnecnbP+YcKjBg/OYf76aWmFCQSMinlTxUbaFDeZFDdLVWhtUM2n5RVLacwbKmiBeuCK'
    'y6S7WcbiFrg7QaluLLkLQWeXl45gA8ikpTxpVc5qpJTyl5Pcu9lkecAhxnvNEKlg31klQzq9EhUDS6anV3AYiMqBqKwm1mEhog6o'
    'BPjG4TaWU1e2sTp7zQa4DSy3U3dU8wYm06pgC6NyhY/115F2HctzVtaFMzGHGlzPnjv+w5x9quMvXoh9junSQvSNORX5vTVtZ3Ln'
    'rNrN9PB766C7FJwy0TM+zOBvbflb2pnlnjEorMBb1e5n/okK+7a4rO++oS1ty/p6Xlmzqg1NKxHdVFTab17YWbbMI01zXihsPBCB'
    'YyVozDIwjZrTS92l/vE1gXnWrBSsKZcjZvgLnBdOp6joQX/Tc9oEKCBkvliCIiDTTArlmrMyR+HJYHpFLYpeR1/DHT5buhHp4SUR'
    'S+2lMFZXPRTeToaYR4R9I7hw8W1WakDGeHN4UT7ZcW1ChYHqtVVpaDlmXoqcKLDGjuvEq6zEnYGe3kRDiWhuhYKREV+0ge/ppZdG'
    'kkjTc4WKUJRmKMm6vUfyjcAJJvWMlEsJORG7rzvtrWZtc7+zhYzkslnhck+E/dOw0jdYEnUlvvoFo9j048FFNhW+JfuMcZL9iG9F'
    'W33troV7m8Lq8Z4cXlwgYLG5FaljHdeCvG7KFZ95Chmfv5FCBb0KkW6FnJzkxBi8F2N4zsHvRxgvUr9l5rXpCAocsXnyMKS2ORkb'
    '7Enmrrr7CVoHUgvYCpnUCkDF8FZIDViIwqbmFo3U4MW3lfBG6oDOc0R67oJu1J94odvwrmjumqnlI3i8oZH9FSxnBMCLRhg9ZPwx'
    'OSZABTzfjtMRXMXSBlr+RVP4eCxIncfdUQ/efrfkBBUk+SoUK+YLHF/lDEJ+0oWFirdocqSfmoKs7Wy1P50lJPKAnQkERJSHZyZ1'
    'Df3kW6fwrs0Xc5+rcu3yV89BXuOOsnntzkVKd5FQ2rIrJ6gNF8mPcmpIfZjJvIK5oXOhsazEQn2KYR2T/s26uwV+bfn2Y+eL/eH1'
    '4gj9bCiM3nLtxQtY1c+DXvQ+JX0Ku6kaZ4807+Wld3qZv5onl8JeRy+Ol5aW8P8Vk1jO/fTfoJ/2K24PyhIMFOt0HjBUmQDpMPEf'
    '41SPFVNSGalyiROodUC/pcPSyLOk1y/7bagZZlTSX3rcTF6GgC1VfockEpFySPtK78ql590SCg/j/ugyNnfo616/j5YN64gBAh3o'
    '3zQwYoffb2LDgP3qE64lqjq+Oj8/L730vu3BYYYkEC8aqs9Vv0e2WFnWOO7csfKtpJT2NqRwx8M1/BGoasDn0vUlkHIkI0gbjcDL'
    'kFY+xeHspz2lz+cZCtLhhWIkZnCGnmQWjDtnffFwzRwxSZmbXyVkX7mc4VhW5bIuP+DWGg6xIrYOxStHvKZaUcuK2vReMuK2omW4'
    'nF1oy55ugGfmDDnt6ShfOkr2EdE5Wjv3b7Thij8+98hYC9VLDnzpsR4fc8Rl2DycXscpolsKGW7EpwgsNu6RDRdrkQekafU0z3M4'
    'PmsTkW3FTNS3HGvmv/1vHpSoSv4yx6QJDhM/UvvHeFwcpz3HUqkoRrsJ0CLH2uUQRQzWYMUx84XJYALFV2FtXWKrE7EgkxhRfqJK'
    'a+34p63N4+19o/ps1Ovp2WVyBYsKwzZ8uuqziwH8HF8gk9iFnQlsAMbguerXny8tfVtHLyKrUeVC11b9MkfTcZ9K6J7VTWyV+nJt'
    'uV7ycGiw/J+u+jYADkMBOH+SuTj8eTAU2/vNWln30yuNhWSBcbO0AV0Q5tZvK7XOCnMro31CNqZhNsh0ct14emvTMshBcepsobho'
    'Mp1YG54xPF5rIB4CTkqY0nLoI+3tONdMFUJR3Jc1RALf3D2gVuZu8FKkXdAxPgNfgB5WwGsv++kNbsVdNuiAErQDJHxUPpD0azIc'
    '08PpDQaBdcVcxrAKxNPc9qiWDq8S2wKvJvawokY5jzYT9wsOzG5H7JtcYR5wrYhEqABluRx4Mdd6g7P+tAtXb/E2rlRC70ZleLVm'
    'QOaN1xmrGXc1BocbYHOfduOvxDyu1UYUCpP2HX4pu5GCNqi+KtmPH/V+xRsRyGQLd46j+FYvMC3o4XE39wF/PNn79eEzJLo9VSK6'
    'lno9PtBf0Z+0onpknU+LkysPypzxd6MdSGBuVeysbMbQX+hMjJ7g/HQoB8qBOdU7tJ8Tth4bGWw4FMLlLc8cKV8BHAqlL0KCEB6V'
    'KhbD5Qco5Sg4rPEknwzf4c+sh38qPOrDdpXOiQFjO5mW0URmPYi7wIuhkVrWCSvCcPRaRkskdTM5nzQyogdqHUm14QJlf4gRvpef'
    'gd05jXOe9qz8Kd0bRHR7Q6HHGtFjktnWTt07m5YUaTYB/Kh6YmkDmC1kkIacbEEx5vbB4eh2c3bEf+Cf7VlU++oPpX/8/f84OVys'
    'H2G85hezSuMwXeCo4VO136RIRjcA8ry902nfdTY6m+27/Xe77b271dbeGoWXpTizNq6s9U3nAg6cnkWZvzjEDTM98+I9hiVVNRwT'
    'GuWKYyYOK6L4aUgmrzilWPn+22qUhV2KAtylKAO8tN3aajdcaNcUbghnCEtbgyuNNg2Z28VMoEbp4fMv6qHnVPXv1sEsLjKeXoL+'
    'YbyZVOQM3NnqaBQQRXb5LLPzN3khve9NLsulcqliADZqcJmUt5USriJTh4/DGDgRhvW5ZVCxZ6D6nI5g5+FHV7zLcU/RPFY6q52R'
    'e3IqtEhqFXrlw3+4qd7C7orw4c/vtnYjG8WZniiSMz2tb5p3nY2tNj2839h1u1GS2s0ZdXYauGejN63Vv9AP+4C7OILKN7bvdt51'
    'KgeN2lGTX3Z28P2bTUh59/7tRqddaTTvNvY29lXyRtOGPiXqrwZDdfKe4WCYCxfQLX+mgqhvqqbwU1Bd/efWagdpXbNxsPHjT0cL'
    'dzvbQNLe79x13u6123frO+/27tY3YNQOuwuVw9OC/iDQyn0dIdzR/Ob3pxclY0WHU/4zDWLnsNbEyN34h38d1uUn/zms8+uKDVjP'
    '7dIl7a+2t9vQQWh+Yeu5aSGSDB2mGJqJTm6z8YzCL12oVxRP+a1N4N59syQNgU/2eNbPFOFJfvg8gTtiOm/bUXt77Q7+H+2s363u'
    'bHc2tt+11yoFfSncoQce1Q8IxZGbDSbS8aS8uIw8OhRbvIkV09L+aG2ccMdK8Xe2zjuhJndcxJ3bAXfBEr8LluwdTc8dLpKKjSR8'
    '0088bad/qPgtcm6LKpqV5170kCOF8+rD5LvPOUxOkMNVsITM1f3j7//t6a3j8mb/+Pt/r50YnQeG7FBNNgeN56d8TyTdvsTRpQ5V'
    'cvWiPAJ4ad5kVwC4VSCOJ8lzXBRAYm6Pk0EKxx4mbpN6k0HEHnfhRbP25/1/7Y3u0ZDSKIh7Wr5qlNfU33ojK6vE0rnwGhoetrAD'
    '3EiVwcEqSRg2Dr9WhoJYEsUez1b7aoBzbATvF0u5ClhsPDXayMwNLl0aTYbD6Coe3ERc/mRoFCxpfJ70b7z+WKWEWMSYZpVpaupW'
    'IO/hCD72chVBAJLcLcABpBav7az+lI8CeGCxK8RaDtZeys+ozMSnecbTXrNqtKDK1gKKd1bQP66Be9cMc+iLgMsHlSBMcUrq1Xtz'
    'HmnwRds1Zxzhuujema7qNRA9i5aXnn8jfwx3/oBV0eP10EepZtFSmGk40dSaSCu0yeyC+Ymc8Dh9BovSn8a5gJSmsLnAlA9a/xgE'
    'GXrbja+ATHe9dUWjjBK6jNWb+s5xUzMpLM+QOlxOL186dyj0Gs4fiCgrZ7XlVpFRopifDiqf+uJBe3jN2UBXE09qanOY0ja6oUoV'
    '6anB6c5tjGTHdAo/Uo3ORreihpnMs+R9NZDhSlVQGtAExXiJ92LQnd3d8X2NGu2OvTbpwTCxIPMLgMIhfw+Dl+bnRwHDXnydO6Jc'
    'No1pPBbguTmpUAZRyuthy6G2+fnntfmXM2qyGcQ8+Uve5Mga96dH2feTPKX+82IT2NKnmqmRgVDWuP5rX7iiIfuCTlaDWEAzS4Hw'
    'SmoJhwg2nUe5IYr+BsS3c7efyVa8+cIqpcgC9UVZ6VOqBqKyYuWsApHYVEim3IXZo3zI5gOLjyyWCcv2N1yle2jzI6lJBuW8yDx3'
    'Jse+Dc+zS11RWdwtpcCIcJS/wzR8rL/D5hKbbDm0XkcSulitWU/wR0x18W4d5WxUnbNgn+pi52zUIJneqZnzwUjbzU66cDup4sBr'
    'tAEw6Uy8HeW1WW2p4H1Ddi9XZR0kCAjE86pTBKT8kMkIiIelwFJRIAnNJS5k51Mw1bCQlcC0VFFqDyXTNjpnWvcLCpybDVySMyVS'
    '5x1xGae7pmy9EfgriltX0ePcwImLkGs4ifvBezHji/usGg+sTjrjJHlP3/QewLNmnTRmtf23O++P25vtrfZ2p+JqYrgtKbZ2xnZI'
    'mE1ski+RH2YUreDcpvg2KwEGsCbiA4sJPCll7eiMqjofzd/Zw/Gg8pWUrZiVC5cbpoUVLtHYfAW1EVwQ18WX6RyUcDYTxCiP2XSR'
    'xPs+6w9T2AzNWrmkLLwEtRPqwNAe4QKD97DATu2SqqhZL2j2TGGVuVGMoQxvPDxPhZwcp2Nv4PXyV5rp0oQx9SjLiMM+BKsWrVRc'
    'Z6kmvx0D147ctqMr2564z9uC59fjr0yU7OCyLFe0QNjX8yhOLiRwhu5nlDcmPiH3xkL5Op+x6dJSvJTrNiYrK742kbiorGYevLF1'
    '1uFNF3e7ifFuUwRBnY1SKp6MpoJw/5FFDrloSwoFjREdTo7yfd2EL+G8enEoIue5gFlMZFOh3HDFASt6/ListiGsf7e4X6/oHfos'
    'qn1bYTsl7RiMB0TVnQbV6FSrrfL5CZTn2TGs5sRsjO5nRITjUzOhF98sjMZoE1YKi3b5MYde2cF5Ya2Zcg6WzJVxe+iMl2iBXcep'
    'GCL1xCjcu1F6V0hPe076aZZCqfVdO/i5dgSHPIUD9nFMqVxB2XRl3qOSNtzMPYYjPgMbKvpzYhEUKbfDFjh5T98LWpc3sBaMwzYf'
    'GIbkAaPrQe0NPzQiNugTAaEaH1s0RfZoZFkJFVrnbQ9ThHYSHN1izliRGBXyYKyxqPRmCsf9IrSd5FUsGyy5cC358krsYoehUNeS'
    '9MNkONpPxh/RDExJL7NuHcf768eI8lIg6NgnH/SoyyUihioWaYRr0OgBY6iVLB7yaW8Qk0CPaTTRQ3wvmC1k9i3PryJqmjXxltew'
    'xZY+fUfCR54cKXLBWAGQrRcSJPTCR+tKLiadnsbkccnlVG15prhA5DQWKAAr10vPW6PeOoEclOrxqFfnkV0U4Tc35iqZXA4RD2h3'
    'Z79TqlIcuWScomTaxE1YJIDbhn/x+yXFoO0CtHs67N40QuS3W7u1G4wsNiBAZEG2aUSnk2Fc5rGoCKbRVQJs8xZU/j30b6kaysJN'
    'D2tYeTlX2s3mi7h4/v0g2eglUC0SkltLANtle0vUAGyXQ2Daojja6p2Nh+kQLiS0p7EMxOChsgSPrcqSaw1/Zybe+Tyosvc47p5P'
    'JBhH5LsQR4RWmgjq3sFe/459fHn9UPW0BN9MEV6r7Fsm4RrFfzeNcPV5Rrj6MLEqiVTHkDhm21coZ+uNka+SM1StpK4HbLrqWiIj'
    'P2fgQ0QRAaIz+2S+hoSLCtAcIrZVbGukAocJkk+KXI6X97TkYbQv4AtcoN7fpmDFaHBhueAm8omRBvGkzlOnGC3QaeJQLUsZF0mO'
    'mDFX2+V7okvdjF8PTK7+Tdyt0ou5qr4AF1/D7NrAdsp8sGGqdsaNJMCo6kNUktg3bF8o66uI+XE4A16jLfh7ZDSZGpk9KnkTUDIq'
    'Szqa4SurM3mWeIgVOrQ9tm2X5I1W4ohoxlhpc4Hve3+Lx12jkcSxksFTCIdIm6yxes3nREy0Ime/7mtU01okLT8lTlzWEh6gJ4pG'
    '5sOIKPpIpQp1OY9hBgQNz0NarNIRVLHAIsExE5qgT9NkawiEo7XBFc7FrXIDZz3q1PmoiqKkcFXfKK4tl4Oan4UaSILR7rnyZwjB'
    'cAl3ZbN36miIwsh6+Ug7r5QEKQYTQEcPp8//uPy1v+vUMWILzJ4vfrEnCGyKLq12dGZR+eltWWVRB1CdjpzaZLje+5R0y0uVWfSX'
    'NxXjKsN9td5q1DO8kVvQy1tCbWh4DQ3ddUTIZFx6VyLtmBO0nd5h463jzonqnvam/I6xKLRjndhHe/fzft/3d1S86Ihj8uHfVyu2'
    'ffhbexTe57c3CHQqH0fzvPSi5az3mY3epdynIG/HSdIgu9ihbMXjD0l31TCDtDUyJWIJYa8jU0+NPf6NOs8YBAeHsdheEPmyPwpA'
    'MOwRkfb+lhjvNgQmZutiNGhBQnzw9RHdSos+L/Hn5edhuUYoZDrA2kngO6kAxJJBSdGRln7rc4ugZnAkvOQi+6Df6/FVr3+j37wn'
    'B6qjEJ5ApEp3pQzSGIpKxMQHH+9O4Vj6cAe3go83d93kqneXwj8Hi9FREz/bkDnSOi3tMHMnshtj9ClTwBA+6ucn+eHG8ZsjxPOB'
    'dWjcwBbDFC+OBOlD8joYoqpD8uHprJoBZCGRwucJC10+EsAe2D9VhdGDDcnC86jmaVmP2a7ceTsWB25ULMr1soMecSUYKhDkr2i/'
    'QY+IGBxtdsuG3RzVLSVAl2vEUsg4He6Kw+FgZpADfAcy2mEnOeJNnMs3N+JLE6Df2K6HO9NlIrWp9ZMxzEdZJbjQCSoMCgVdnG/t'
    'b6FBPJUTe9IZkq28q24F5N5S6GpUPtZOAdbC3hgcmm2kHadfZ9qtPKCl4a/gTqNuMMw97BPLRja93XNtNKwabEVFgX0CJ9knAQQO'
    '/z7KllW+gI4ab013lmfAMnJzq0PHzarv7fTYtYUCJblJqyDvCLxY2dQeQH67/iN4Vnjp+Gf5vrPk1HTm14g4kekphSxLB4XLvG9w'
    'SwUVFfIAL174TIAxTHx/5e4n79Eh5wqOzbIptep2uFtcJBJvZSdOxVSzhbt1ZTtga7FtaERPnt66PLMnyOAtLX+DBLw3GsF+DP2R'
    'r6/eiTOMy5bnEhMVNtauMjrRDdFBtWwPT4u7ux5t/7s7tfn9CozMiI1wTYv+8Ad1atfMEXB3h3t0JVqqLb94qYiwHZTWOV6Aru3Q'
    'UM9xfr32F5HNgLl7L17OXl4yfHBfgWx8a/iHej1qDeL+DfBHKB1hESyxcbHfrPoYFh/dAMQzuha9H0Nb1qbJxJRkE6fREEobXyOq'
    'Ym9wjt5e0O6U3YU4zAMCSV/2ukn0xHkpPqk9CtQ968qr0h+OBzhWehjre0ZmIQvexokt+xWpQ9krBMhPR0WoVWXWeu5LuGHtcOJ8'
    '6iIKN+u3z/3NyiJ7s4S9VjQLhoTGwzmJRg0/nafBHyeo9u2a8o/hxSomRvdofFdW9RcNDcz4RY8w5WRst/jFBjCi/bJXRbYIO1aS'
    'yex/MnJ6eitlk1kFp/AuYWggrlJZe/GfvFTd/oVKZKzQvTRF0/HHJX86kDAY9ecxAjCM7Eh5HfW5hPPNUKkDuehd2RZYNeOYHSNL'
    'eW0xRCOgDBFe2ehkhrbMl3Q57B1eMm9JLL8+HOLykcZWw7Vmb6aLFGXFHg5OHalPXi9CVjjVpiGWyG1qyUzhVdbuDA5Ur119lTBM'
    'tH5zJV9Kc7x4fGT0xp4us+OC3GVEcjgDgs5vk1GMh/tIiTGS8zReFa/twceXefJX5XFu6CKPIPlW9ylWmQolJp5jJAJTr8WlRreM'
    'iqwEYwmvJJTo9JQVMIh18u2Sr2effYkU1DU9I53h2I0on8kN8ugfyCS6KY7qOPsX5XlhpTbzxa5qRVUVp1HNSEtNMBiWmeo94H9i'
    '8anPna4If4rgaBqrrayg4CqEmgZvXaDFs3FxObcGUrmkQzFEf6wt1ZYEoGyK51FJcNRKArewM7D4N56Z6Cx/M35v6SKum1AA6Mnv'
    '9tl8AM3aKVHU2kAa//zbUuGF8/uvK/Pg2o2TjLtxXFHtzMhY0upW1xzaaroQSv+5Bg8PLfKJsEnzUiWwneaextQigbEDqpUE4ku3'
    'cRyUN3UFLgq65qDY1oYJ4YOiZZPBYmYvwGs5RaeIOIIOMoNubAXTpQxgt2UFNxbxeEpNdBdRZS9aVTblT1Hgy0AyaO9Ewg02HjPl'
    'uN1W51FihL4o5kgfp0ZnL6dhD4N+ZMb3nkNMz67eDWZdhmtq2Won0wTINmmDyxIqAc/lIa0cJzQX3JdcNYS3skgXgViTz194SgLU'
    'EVRUWE/42aw5CzF1eyRT17wraWYvbWTuoTnRqApvrF+/UJGivBPFVtDe29vZsyoLs6TuqSRQdDg1h1IJ50EmwUrZS2Ao0bouGS9a'
    'pR4K0+o9dBDhmAmpmGV+SJIRURJcepfIawnSkikt7vc+JiS6xiQDgjziJpp7tbIygHWQYjTEWga+CQajOQ8AipQ2ouTgdbE/YTwE'
    '1ncohIp52j9lN2BwKLKBuIvCVs6Bhs1CRqQ50LL6/NRONgQUs9+fXmB7qBBTh8n/5Q62jECibD+l99abc36d5Du9sd0QL+qdd1QZ'
    'Ol+ju7VxyaYf1rUbf1lH6qL6P8LwfUCn+LnVd9qt/fae+NJG8mt1ZxN+7ra36b371Wn9QG/MX8iBFsn3N6V1NpnfjNZqB93Eizyt'
    '9zd+uttv/whNQJ9rUzdkgjzsqv2wnJXmfW0dD6/gVjm3uewezr7hVP+zg0Zt8agJD8a12vmOQ62+/zi04Z4mkLPvj8C/nE77bElV'
    'PG7t7Q7O3k8bHfin/W67U6GI8fDl3e4+TFP7bm3n/TY/0b/RZnu9I497Gz+87TgP9nnNWR8D+doi9J257Vnba221Ohv70W57b39n'
    'u9W+W33b2oMRg593q639Ds6berXf7nQ2tn9gXIIWTOvuZmu1fd8knU3p+CSN2Hj+wlp9t9dpbWzfyV/YW0/vCKNgsQlb7W4Th4AQ'
    'Ct7t0lBV7qv7Ai4Y497ZPl405lT9gJXgVum9c3A27A8HawZsw9C/TKUHrcV/PcJ/lha/j2oI4LIo6C24Sw7375loC6dlatqNe2NH'
    'waU6Itta6B8EeXY+9Y/E0/9AY4/c42avQHqMq32moXBgpsB60eVj/uwDMdto70eMR9Pe3djfQaAK/YtxEO6QjPGHSv4gaWu4q330'
    '1EJbdXWuPIu+xQCBiuo/i54bHRNi2n9TLRphHTrxoylb0e9nESqrhIpyPf4QwDsa64WoXFb54FSVTPDk5UDjH7/xX1OQWSnFtvnr'
    '+W0mdgG+mDY74slNDinZs+iFeasJyrPoe6k42NjcV3/HBaP6XTXYHPCd2gacE6uUgKFKOSuG/4NLyxWaowyQ7RtO6CZBXExai1bR'
    'cmeAkxf3IwRX4IXPhaUTaPEFsHnAYl+j+hLZsatoOugjbjO0cYrMDQM1ECRdYsAWkEPrp0MGUh5MasazV43/6xXoFRrEuxHEX+H4'
    '2Xd69CgMqDduFW9SyPOIvT3UW41y7d4vBqviuZ1mlhCg7gk3QAm1yAOM18qSKd4RxrTTLOLXNhEigZiXK64+xKZ0BU8+ll6qYiXD'
    'S2tp75ppC/YLwAReETaHjrRK3gxeXIGqbdyCGosF1zG1QWF/f6BL+oH9arOrkTyqpWj7UY6rp0QjTxfjihdaHpb0uxG5fWB5BwxJ'
    'tqSd3RFlldFDTIeaUdk8LtoyEI7cvG3oErwgS5JCAtPb3fP991WtBP/G21pff+dmGQhE7QXqk127nkXL31eYYnj1Ts3tVrX8FWx8'
    '6F+29fDlaw7DYhv7Kvrj84x5Pk+yBhupuopMfHYYdzLDxplpRN78NPw5aqh5Fotss10J9MRtgqom6VVFlatCW6uO6lVDglfN0Lpq'
    'QOJC6jWzRv48mByB1bj8He+1f9xovz9G9gFOLGDLV2iw1N1sTEjsgWABzdEt8knqadH1hY3zUvBqX3JkDUadpWjFu9CJo5EHlKdx'
    'ZIhFcC9IpCeJ9WuU0sE65GawMbvaNZ291vb+RmdjZxvGwcCB/lNxsIA5eDgSVq3x2UhYCqSU+EXVr9yraPrssA7/+BdSeSkZNg7r'
    'zTbfTxd0+avv2seQoQ0jaMePLy+HZfj7I2TZwfz4z755WKWr6M5254DAAI+aa3c76+vAxUa7b5GVhTp35HF9YxMY+vba3e5ee7G5'
    '2drFnu/DLQC4+8phpbIANXkdhgsAtmSz9aa9qfq929pWo3S3+w4mTP2GNbD6FygS752du9XNnf02fF28iypNYOBb2z9swhV6+253'
    '50doHHB/MPvQfLr9MCvIV9bOPt0hzbc23IfebG7sv7Ulv9+AeaSnFuRrbcrz3upbYNehxmh9ZwezVppwl9qBFSG/7za24F++leKF'
    's0krDYrf2jUva8/g7WEX+PLnwJZ3b5/P4As/VNxT0+FaweLZ2tmDiwPjXuHkeiO5DcOIcHxqFPGKenrHd5DTO77Vw4O9yePL1g/w'
    'L9+k4WGt9dend9t4G3qKtW3DSDy9w3szPWy2YHKfmibtvNt/KjenJpYqVyssrUP14H2U/uCN9PC04i30zt671c67vdbmceevu+19'
    'ZY9zIOqbqgaDqxKSGv27SF6F8Aw0s7uIoNSYNL6Af1OCuz/DvMDXTUpHim6MhqlBejf0KsTtxPfNmgX2NKTOvZFjrlyQ8ZPL8Uk0'
    'DTkN6FzCAXXJ5oKf0ZLl50tQ5rI6YoEu9/ur8SiNVowLdi4gq8jZOIknY/ORAvBkSgNYUAIDrV9MBRtbO9OYHA4laMlgvdEVMB/Q'
    'dabv78kbjsBiW1/cVKvXDElYNeiPGRuLURmOcjk4b5o6wh0ypt+/MFdWAWzTyGR3iZR7t44C32htHJ/DMxp+wHlu7Tq1bFNXxaBn'
    '0jWvvS06uulipkckIJBe6TnD5BW5Ok32L+MRneW5C0QC4MhEeD755KsEL12kPAqUp1+9jr75Dt+ZQ4vbhikU0KB3XKsU+C23b/ar'
    'Imjqiw0Zrbx/2ZHsZ1qrRfC1cOxMgwrqB43qy8fNIyPqmVs+dTwP4/B19Me8PCbsltmjrtpsScnHZHxTxojK3Sy2spsrurFhIqfj'
    '//mAe320cCdPZAlwMaVd4aOvRo+pCERQZemKbFg6KrrJXTfp33V7d934rju968d3sNY/xoO7j8PB3WlvcBf3HVovFlThMaRapzM3'
    'uOPEB9bRC3J/lCRnl6vxoNvrslZBxEhxvz+8FlLG6qn5tIzpY1ZpEOBNZ1cno1Dnr0v7zduMIgIqWBbQ/4Pas8MjT1xI1QYHHBl5'
    'SrMZOrJwzbjBINt7u4Js2RMPm+2PS8E4Jw5xUoY3hGg04ItqlJX4jpI7DEnNmjtrAuDbQ+omQILmbmF0+h5YZLYpBiJCAUb698B7'
    'Lj9Vu8gFXjLy8CWVqn9G8rt6PWp/AjbCghUDER9djmFTpk6o0yMoHtKl1SICEyTZDZpBoSwUJ2BxOOjfcHmoT6YYdKJDvr5E13Pa'
    '1QoZKR6Pex9R/jRxCmaC1GEFfo0uu3TnyQSOnL8RHrYP3IlImQInDkxatCWcstasLFlWHoMWoRShtMfBbFISt9m4DC6dDLVV7iqE'
    'kbyNCuTJLczHyrSnsEnCO2ZaA5eUGurwaiwGXLwUb18FWZ1tUg4hYEm2Qox1Uu1AiG32eVFLxXYJmvpHv6lnsDLGCDgwHnanfKEf'
    'jsn5pTeYsn7XYsC6VovTt+auJPzT2U3obDB/nbH/j+Me3CKr5AH4S/Bb4SFc2lwwf9UoF0G17L3W0XDJeWHZorvydmthMShPZWFs'
    'gpbTlwmGuMSX50MknzCMpzdRHHlqBhzGlI4g3LJcGOS4IqdI2vEYTYjdqWGXclL0nhwhLFOXYJJS2u3YAOhjMkhJxg+VcGnTNDmf'
    '9i2oQ0oKezQShqSCwlFHSmHsAdKaxkbouYh4PQmBZ2bKYCP0/Hh3zguYrHYobSb0Qrjz6Vg5sOtPqWXUus5dzHIg5a+M/4+9d1tu'
    'I8kWxd71FSVOzwbQAsCLKIkCRdIQCbU4TZE8BCR1b5JDFYAiWSMQhUEBvIzIExMOxw4f23HixL7Y4Yjj2C8+O/zgB/vpPNhxHvan'
    '9A94f4LXJS8rswog1KPZ0z1z5iKiqjJXZq5cuXLlynVRBBr5yRf8ntGtjuPjiObYu/kll459cM3xgLgsyxIBB4qmvCV9OnCYGygz'
    'LCuMeiXcOyhbzIekrQyhkYwMQ2W95O0O3Nz+btzXC2jKooVYTna6xBSZsmqecntqCpUpxoncJHIQixcKUwaSP9+UnSUhF0912mWS'
    'K9OovS+EOac2hX97bc5sWP4hW57o8ODeK11q3Xx8lD1ncxecQE96Ra/l8J77OJlmTOtuxDjDDgCof0bNngnFlu0a9N8MEhIXbhgN'
    'VvrLdouX40NWOJD/oX3GRzG/RYtaKGOGjxeCptsoWDqtK7/y3EvdCevduW2wbW4Ez5+i3sRpzPQCvqLZ9cpThQl/o8xPymFyZYtW'
    'CujYWUn5zKs2Cbkf4CVdxXB6vZCqBWONWMsFkTLlMwyGh6KDSXuBO4KUdgwWq9Ly2l/393IVtUwzTmxcdCKmlxGXy6u+1MEQ5R28'
    'Dwi+UvR9Fi56eqiwvRkZPjBzgbjJE5mmczeHr82MDJ9x5chUoogcYg5i9CjvGxzNqtN7V9ZSwsimWgXBxbg3iitCW0SDwEMFnBOU'
    'lZ84VmjwXFpdLg/CDsmkTG90TDBERukmq8ErI0wYGYJutC/ILxxlCYY11CEfOqFj0jpQedQ6YZ/PNG0cacD4tx2qqgtfzuPY5BQF'
    'IuoBfsNAgMIaRX8Soe96Ou4d7+rSZHQyZzGT67eNVVZzW/V40d2kVnKIUbbh87QcCIa23IzDHhivj9Rx4YQ/Q0/FenDRkLtA1Cl/'
    'ArfAet7W6/aXriMpaXHO1u26KOLI/FJisJnSdkMXTYgN3DrsFEVPRQHxdl3CyNvn3VGVDGgU6XTHBWjj0ai/VUQD5Ng4QZTQkL3R'
    'xhcXEdDHKOrdkOPjJk++Qwt2mQifEr2kN+URby14aC8fRDhbEnskTDUiM1r4LqfTjnfC7Pud4pSBQlzIGxcG4cnrdjY47GSRAI2N'
    'innAN4KVJfj2bEH4EvhCQW4eKycYpZQLTExBYEUXlKNC5Ys1vN/wWan6KQh4JBxYOHodOxsI8/xy0B4rHQ9fsp+HKcfjgiLcLTOc'
    'qvSXmMI2fMaRDWs5UeFoj24TeEz2SyZt0kSezOx3wk6gd0oRiI72AS/V4UyZWibbK0xTdCiTxYlqDk+5JHehrKJDRUmernmbSevB'
    'EYuyR4++zkLr6T3slZsxos/YX3qDyr/f0syiZJNSamsNL+NPrl3G3eqPU0R+TqbHAUouyThtsS5amoNWjDloNvgvpYvKVnmUW4W9'
    'LAVfWlmScfLoig7IQQVcJ/EeOCoaR6F4pvMVCzkN/aCUw09HsY6JIoSvweRrhD8ssVfJHc7z55lI0vNH6WHlh9//3Q+///vjo/Rr'
    'NNKuf89X/bdb9fe7t1tvm9+Kq32+7M/kaXOxtuI088n9+nR5VeCSlOha6dpNIo4cOqZgjh3H4tIepND4EhDpRuqbUXjkzF4zWRxr'
    '0slgcTmDxeySZcRYlYCPouWpKFqQKNpN7C6ELjpDcQQjEoMNPI0xsoZ3CrsfQxPE1qmpz+QmK7Al12cGY0vTRvtkJUMQZry4RfYT'
    'M2y5o+JOM8sY3d47crDtw/yvj4rVr49c834URlZge3+65Poyz34JVXIGpkKf8IyRyIUbf/wxyiikUVBQQXShIXTUozgpbZiTj9Eo'
    '1Vxk8qCdpJD5I2bbOGOsNoszkSJqjZaVL4MWGOgQAz5VKEI4qtoRSxeYtzvSB9BhiNE1WAkfinuj+zEhTkxqo1E2KDkJCJ8u5LBf'
    'tDnb3s2abilzL8/Cyxh0uUZcym5rKnOezhIW5SJpnuP+EvZ6lU44iNFi2cGZZqhlyxHKiMky3XS42QPFEjI7k292JA1kMNSR1Q2V'
    'MgdL57NnSm6MhxcXFhzT4qkNyOOUDxdgyetrt3HY5BeEsQMh79Fa8CHYs77mjDiRpTD46pMD5e6X1Q/yUO4YHmeyPzvCkpHR3Ytv'
    '/+rbEGxZCvWZo8sffBOevQsXH+yduDlCaCnTEcrRmxRDebBbp/WJMAI522IzVWSk07yLa3UXZERLV5pMgDWgQZWS4cwNTJ4AqURO'
    'LjOTBE4RIJSHwBo7GeRwAN/vMSP9iHuhQJgfZoUtgmbdJKcDQtvFfBDKw9F2jZ0Oj66U96P1yTTJaqd5QJLv49SuWPPKDLuV6CMX'
    'Cx+B0iHyvkbyxivrww+Rn9aH5qsYyFbReICZhOYSIBpCFwVIQIM4eGe7F1jiAkaCEXYA6OHi8V2gfy8d333IyZPiJNadhgWZWzdw'
    '9ef5u1pxoqunu2ujtsvugHYcemO0lkOPS5lO5SZFvnPuMOx5Wa5Zf3vQZpKWc6Bpl7sEpYLOGCzrGbsVeLy9d9Qm0wx2MNdgiU2W'
    '/O/KZGkCxzbDzePYtbwxgsj0DNVaXjvOGRyDlD0pTWD4uTA5yqtKTTErl8+DJfRZG8EHYXMSoh5LB5oxE4SqsxEcdy/jlKiwpimE'
    'GMCdNKGi+4dh9cMDR1+mTKes+CI842gPQEkGx49atBiDB2OQBHXAJluxqokNc5ezOyOac7ev+yJsC/0Rij5wDHmlHcjwe9ULhbNR'
    'tf5MgBPERDG/nMIg7kjkIif9vVj7ZYKA3O+kQ00ozRdCJNWXBRimGOdBQJyuSZPt3wtbh/zSsF0sbUwTEJxuld2aGLLN+S7MwbUI'
    'S1GLYbFqhwCnK9rBV0sYk1UBjiBi1FOTokuUjqULtPLqdlvOVbsVPwXiFboq5cbvy9cB5bjL6dn68q1LbiRYDnUiE+1DRX8fRYNa'
    'sKiy4ahMJZThsuglLXH6WioxeU2rQKtQMcFTFRHLoRRxpkH1L01JOYsnhgDEOEwuI0pWxVVqRhFswRAOWYu7HhyyEvaTqasz/1CB'
    'u2PdOf2ZHY8tWO4RgdS45gDTNBV5gEUgZ6sttQ1pdm5DyOmmMoOe1ioSWc2lOdV0Tsuu4bBWz4mMhDYJ6cub7W6xoFLhcF+1EaXN'
    'p6xelDQoJxugYq0iqQIxHpWcAIPuqKwKCG1iD4BUdfNXxNcx/TUpX3fidFQNu1CGpHKlN8dEdf5O4O0WEwqJPSJVy8JdJyaJDX2W'
    'VwY6Jnj3ZhoyxVCwqJswOhpQGjwAXMUH8WncpvhtxCYLW0ZTxgmw1P6DOmsb8RR1eXTSHV4I3SGZM8pPRNJ66uiLmhu7+Wndd+F4'
    '1knS3cXzmUMMZhyHNNiKsgqcBeZAhbLKwPzQRFBffUKId2h5sPxhVphorwnwOAQ8CjztuBePbmgScC4w9iru/edxF8Q4koWoVC+a'
    'mV5RWsmiQUNfRugqCpbK1Eb2SFjJ5gHXXfHTEF/SyZjphZaZl1PFOUcL3+yHD0WdyVJPNhMMjmCYoK+SFI0+vOjGl+wptTZ3Noy7'
    'FTgmjy/6tcX5yuLqAFYnkFZtcXlwvdpOhrDqaouD6yBNenE3uAyHxUolpADg6mtlCLQ4TmsrWB4m6IzUSDX0lh5WLuLrIkZwGJ61'
    'y7JusPLLsojcVlqdW1ci5Au2GNb968YpuYGTac0qm+HDShyNkosa9pCaqTFoMvlfRFjv0TaYtnKgL7XqYtbQb7yY5xZsg4OwP0tz'
    'i0t57T0urWLAsAoG4q8tAqageZWKzWYHwlPFCLZUunH+6lOUdl6PLnpFMa0iSiNxXIy4iBFm1ZFk1LupBiazlmIgaULwdN4hm5Zo'
    'jI4S+KmTDPGYqG+0keNo7lAFPMDADRYETWgkIG2sEoHArjTAMMqKUtIaGwYWH5cXT4EQzsIBTb+ZRIDXo6EoiIaoliYTFb/2qeoZ'
    '4nw8TAHpgySGBTmEVl7E/cGYJ3htDgsmc8QpoSFcyRXGT6VznsSdaI796tbmUNafI8aDWOcysE75DLABYmnU+Rh1C7VC4W5dk+H6'
    'K/hoKOZFegEHpWm0gjQZLMB/l5aYEsxNGQDByusv5gkzP2lMjS7z8ASHzUlYar37A3DUMqdXtVR/TqjC0eUhi07fk9C1z/Two4mK'
    'bg3ogF58+XIzePttaQLKXszDsuYH/vkBtqsPjMb1fLHkRQrT0UGW5Q4cEJRQSoIZlxOD0UPHZSSujV/MMywf5hTCc+FZmpkE6p6J'
    'ccHlYlTDneeyBrdKpYjiIIj0/Wj4uvVmBwUb4qEk5q7NdVLCWwXZp2GLWnmj9mUde9WZD4pxbxRRiijVmPRo8gUBV321cPfLuQCo'
    'CdM8dH26+OoT5gJsnkfRaBsbUCJQhaXAcqHFf0k+sYlRReNOqrcCOvejCFQm88a7exoJx6PzBL2y3pvQ+7op/qTuCu6Dg066XQCD'
    'JvfdAP0uGAi93+vPCKWLzuEAhZzEAzbKJU2agkbfZ4SF9l8cA2FT/2Ig6sOiA0etSI7ZapTLRnxcMjlVfULjeRBnZqUtRtFuoBmJ'
    'J5TkyS2ueMMb+FuQUzofzQGDvazQeBnFmEGUDIAU6MIfT47B98nYWilrYSP0zi/ZnHYv5gfrcrEI+bsHB8S5dU3onl6AjbImeV/z'
    'YVthJ6ttsNZbns/1hwldGSZX3q5A3LydXM9RQrUKlsUeVug9Lk/q2h2yHTrI6054+4ADEyfDh8fbjgVnlr8WHAk6jeUOuigF2Lx5'
    'nls3WFBCnyA9VMyaROx3dpcoSKyk4zP04UPVYQVEwdHN3Ppu4pq4qGTOWjlvaeMsCfBYwD5552H/jC3dlQxrvSajKjdemLQgHt+z'
    'IJS258svBlLF0EJQdiChewzHeHSK9Ps3RkNDFTC1DibbwdRwXAYE+ZnJX+ivaMonkr7yJPCJn/VhNuEUV/+S5M+Oujn0z0B+zApg'
    'kPcuAdUAGQfNtggIG4ECiQYJd190NbiaGX81KC2NPa/B2hiiIyrGaadcNzEshkHUT3OWgVQjhOwqRXcQpF3SkXiM82Gu43PZtxzL'
    'i9zjXy3eF8sH1kKk1EwTV2VWMfoFF2jrPAL0GGNPB+fBVQytILKGQqCi2JGkSQNUxENWEvz4DWq62nfqIvV1yf4yJZ3QZ6iKXYcF'
    'lVgi72rBzcE4AxdwdEUZVcBF3KfYjEsLg+ty9emT02Ep0O+e47vFKr5bJYuyCqcPAwwMR5PVBa4CIhyQpkeQyMIEEplbb4hrSX2S'
    'Ic6ilOKKVCrMedQ2rXjMOuU0M4uLg5bTddA6oMc9XXz1Cb9ITkcQ19bwj3+6sEwLrf45lk7zEEseK4/OCHmNOm98cBiQd/b44gjT'
    'N5BEU5PYso88+OIjbwYGTQfUrz4p+zKlAHWOLCUnVUrwz/9Z6MrUvYQJzbTPkfs7ZjXD3qw6WGXMTT4Q/6GsPqtrZ9ZDSfQwGIlQ'
    'ypngFSg8oChw4zB455IDpqjH8fr1DUY0+NF3HDZqDUtR+pYiTzet6dVcsM+kcH6grRSMYv2342h40yRgmGmQyOlwshLluKalgtJG'
    'lQjogTZLmK6rV3BMNeFG7Q7FmryI3BFKj4o6iXLQekeWmKiS0fuAEkhxIyiI7NuCW4qAQHfqFtZqGRB9TidWRRGTDX7y3bwoWHYA'
    'lySgvNtoUfOPexcdTNjDhG/PLPvjH3ItKrvhqSTuu86r6Msuoh1lbUBMxXBDdbmTacTJ+yXCLE2+1CmpVE613L5qwxlWfNxL9kp1'
    '4va8HCiNx73VWWPi1dYhoFDPcS8E1pb47Wv1xr3VtYLEBSBMXOWxz2FYRhuSUQxoz7GiNnUTp6SJugD08DLlreecsQaYwNE+HE4/'
    '+B9/wItu5mlkfudYfSEjnBm0dwAiyD696hGo3aw0HYWPXRSqw6VBn3fAzD1Jpo6I+uMQl39knI45NsuYFfYsqHM5Sg4CP03jtZn8'
    'zxNE+kn4Ik53z3hmkFjtyLwhCXPIWVA3g3w3AxLLDhatyTkqhV1jDiO+4MW5EnBo884XgKTVBoWXd6QfJvAXwTKGmM/79AjEndWJ'
    'ViYatog7P1nKsiETJm+3vo5mumV9jj1xnqvcVDWPr+PU5sQy3qhui0EgqqRRsaetQSsH2wuUiZVywbW5VrVwuWX9ViZFeqLoCDK2'
    'pcCi8CH9gviY1MBUDHGOBxctWRv56fbXua6kMyvsHF3dZ00dN3nftOGTO23KKpy5wMEs2grRR8oxJ6vaIcvuOkWE90jgdNErpSyI'
    'v4TxuDXIdg21HQPvjK0212GD8+wIsiXrI7YM3MLIH+jtst3cUx4xpVltpV1THo6Edb/LT+a88GON9IbRBdCTtNObkG6O8viCEBJT'
    'BkOWoIum02Uh9mZ6l7snvAw7H82hN287yN8GNpjZk3tv/j5Qmb4PeEdxylxoijmn8J4KAO134ILOSnmWPFPR9+VmyJ5xP3z1iXp5'
    'l83E+MG3w8/OnjBtL/v5ZCQiPt2bsBakKTYpFSGG1RmLrUvXAucq2cDbsNfOuacyhtIK26+GyQVlP2Y+ANXx9rYWNL892N5vnewf'
    '7P2qsdk6edc4wEBvKgEJZ8vNta8vmwwm6tjm9Lf8wKTpVREYfAx4FTAzJ6nJMRWHMtKWWTf2hwnmi7YeimYAi15u3/ze5iT5DfIM'
    'yoqyNm1MGLOGvEcw4qUhQpPut+THBtY5ke/1qbCdcrQgNY3YB1kvHakTvM+uoeT6d87CbO8MS8XssEMMaScohxzbMUVuONIGpVfD'
    'EF2WODaoiPFq4nkpWFEfCnT4QtOkBdbmvXSrQ7eAIMHEfWqGL3yY28Na1GmYYBNBQ8WreNQ5fyX8e/QihVUnPxYNieoYkQjFrjpX'
    'uXd1gcHUGr1pepGrC5L6C06Yj6uLRp/MR+6tG3E5v3oz/l10b13UUPsV9wZh596KCYZiG93I+H16qCUzaHU8WhM8SRY3AyzJ0ZqD'
    '6Jo6vNgKPKSSGZyBX1hZKMiCPISSGYwtuKQLjgcYGew9/H+IrlnaEVZw8aPx1srjLfh3s/4sMAUDOJvZ4dzN2SsvvGOnHLNR94PQ'
    'XCL9T0pIbHKebyV9nSAaLVz4WMN3dXdGz/3B32dsDxtPAsOoJ1UPTmHNoXvmJJPXO9WAnyN5UobkcvCYxgEbWpje9DuB3dZyk3L3'
    'JubjBm4uXaRRHshm0iWWvg91ilhxcRsvs1wg+iRrvyskiHA+cWrgKFlTenjw6RKFPbSkHuCujGBEizILIWXudVP3ki/VVEcqz41q'
    'EzNjZHJVqtSM27utw6PqUXqM4W3ULwpwQ2FvTDINN00lZ80zoNcx8MqMwwcu+fIGJyswPUqTi8j058oYjd3C/0QkGnwaJUP8gZ6n'
    'tl8O7PdnIW0eObDff1O/7SSDGwqAcTuMzjAT+TDq3h6NFxbC55MgsuFYLsSjNulLKdGrtiujB7ulTOgpTifjzsDNJgHl/IBFi7EN'
    'lRwS00uqsW4ES/IVd3YjWLRJJO1/HnHADm73RbD4RNWWL5eemNoy9Zs7qanOH7ikUqTZdQRDwbO5KUyi25TFNPOa+HzaZ9OA3LWT'
    '7OC3THZqduHAM6cg2PRjPDjguDUecV6dhYKgmIpu0daXXqSSxIhObjWN3LaVSeOtUphTXiYnDLkKQQ4zYoJvSJZbDp7CkSa2Ucj5'
    'boy6yuSm9CHHJoA/Pli/88W81y+ClQWpybDWoSai1/FqQPYiXhRW5WwFWzcGTyfMw8T0u9uoQWC0u+jLX9iAVRMcoVcykg/DBXoj'
    'hRI/PYIhvAgkTqxUJExNdcdNpeMJdjdtXmI2xW6/e3+/obtB9ZFe4b2STNxD8Ep+b/i1yB4zHfh87OdWkuhGKpqKcU1nOSjVdRGr'
    'Lua0fa1BnSp67Gbi6ebPAqdGzRCirHFsone6DT4C4Qn++yjIqeINndbTpAnLZ8veLJFEraHoaWJj4DULXiZz4KWqnbG9TMzlIEZB'
    'hjEUrLsoqQQrWbTgwuSAd3QfIlcbLk3xUhEPvrULeOmBCn56WNDXc2TDRT+X7M/H9udy4dheB30sx17MQjlAYhzU+uHHY4wc634T'
    'ySDUDkFlvb1gMIw2kScbdh7nbgFwzjogVUcwTFB10p3vxuEZBaKjCiBta8kYKrdjjgBIdid2crAdZQ+V+nfeJsgs3Wekcb/eP+up'
    'wyaGolqoLppMxXwuDbrjsFfROu1aMLoS1rB0/xRcVzq9cUqu8ujYwnGdzyhHsc5AcBZ9t6nLmD0FO5q5XnKSy+Cezz0dDc0tzLT8'
    'MiMvQdhIZgfL5ph56KUnL1SLpaMKZucygkqmDvUBk2GYuQu+BrwtPTEdRH2/+3HliQvHQQibBuArJK+Jn0TGu0llqoNxeq46WPKV'
    'qziPKIakIrkhfd5r/wbmuQqHlmEcsaBhgJfsKjkcnJWD6/TYWyrXqUX5cl6c0ou4q4bF+JgPltxEf6cjI/5dG4K9xlYQy1gdUfhc'
    'Ct3mbgGlCy3TZyqvq8qL1UW3MsVrM+3qPNcC2DrdwhuMkRv3o8GZwCnxTPMdD/Ys+ivyzSdtrxaGxDWTB5RGv0/w+yZ5stKBXCcu'
    'E/wFgSN/sezFFRVp5Tu2VHxU5TgW9NWmgg7ahlmH1BHitm3+uaHfVfSbGpU0bCSs3tA32J9fkMtwWL2mF5hx0nzU/Nm9U2RqpuCn'
    '42F+xHbCHKqLaAClDHMwvAH7bJL0QjfMh5rlGZJwkEmhM43KVYMdwMs6PRmkkoKX/CCDc1ORG47NrUYt4Z6F5CcvoW9oplDBELvD'
    '6jWnlK9eMdtXaaqteRoGvR/BIQRNTn1Y0BNsYT2wdMOLCvXJqrvmxVNg5bR0Fpek0ZiEh55OToNC5KU5+aQu1Uew9BUqr8vBjfp5'
    'wxtYzSKu7J2zTIdEGXrmmq8xvdlIfOMXPhQ070QdlCqoH7H7i0uYD9w2cKVHv5AH5NvoRsCAJ6XFDTBBSS14+JC+UfISYzXM4gtx'
    'VsCJm2JCIIu3JZDbijxDeHhEEa6G+xRMubnWM3NvNjekiKLXe2AHTGPXsl6b87SanyhJ2T47cTGhiB4jLo5idtQYCVKUWjPxiL0w'
    '2awkQnkGhIIf/v73fwn/w6EG27tbb5utg+8rzVZ9dwuTeTc3DxqN3f2d+vfBm/rBN9u7wUHjVeOgsbvZCIoY4+z9N3X0GeuUAADB'
    'qMMZ+CIK0/FQqQXDNB1foGc7LM/BKCiuVJ/MlZCEWWjCfHzPlrqDuErVm52wBwxtMEzIXh8lQQrDOwwSikxKVYhq0qpuEpX9nMov'
    '6p5RWABapPQt4AxysAmzi8hr5cED0p52hcC0vtUnC3O4Hy8urASDEdc0EdUn/6cWLJmaKwum5r4TZHZCzce65tKTJVPTmDcEm5Ma'
    'rgXL1QVVc8X2tmVz/E3u7VOs+QhqLj/GNoOg6ESELTGoA3ynI52iMjUP1DPd/SfLauA8f+pCi+hiFPa74dDcmjzCEFwYYqyDNtQk'
    'mRXVXzRwAIrgHvylLDkpz0Sj5qj7hlXXxewhiZYFXUUhYi0anZU24pgRQD9jTKppVopQK4akz5Gy6VPeLJ1wq+mI0l7rqRYBZHF9'
    'fM1wSmXqGSydueCH3/+dv9DEAtMw7YJyYcLKcWEuaZi6hoZACyvbK1xBLoTHGoKzFDUYXGU5g8Pl5IKBlcZgnHWpwdgl54DBteWC'
    'earBiEVKbjIaEq24BjIvBxIuLRfSMz2uzBrlUFLOGTxOQULeTfqm89B3lWRayMr3Zil3A7pSl60O61DFtJ+Hs1KhUvA/Y4Jl/BLY'
    'GFUPOea3Y0DIRI7XQp2ki5c4HQyRgDi6GMATuZcmFxd4S4v2FfyeXJejbjxKhjFGQIxGIVo86otXOOkeHRaPN1R86OJGTQWHhsfH'
    '+HhYrR3Tx8d3pY3Do+PS8QbFncbg/PU3t/tvSqUNk3LZzUKsbw5z2jk8mq/CiTrztFRevtNhrUXA6kyLuisztYyRabffNDb3thrN'
    'DYqJDcDEE0XItl/041a9JR5LR+3q11ObU6m2KC9qAAyK3F448yZGnTFTkJ4nyoImJffgpNMZD25s8isgR3VPz8I+Rb10PI1N7hYM'
    'S4kKeRNdJzSx6OXoN+tvGgf12/36Ljzsbu9+U9q4ff96ez+AN7f7b5uvMWRrs7SBkcX33+7swCM+wZ+X9c1vb/fetkq3f72394bf'
    'A552WvrnARTA37cMdWtvZ+f7282D+m7j9jVIR68bO1u3zVajvrUNnbjF0sGrvc23zdvNnb0mRjCvbLzdLyFJBXu72K3tLXwbNF/v'
    'tW75VX33m50G/Lzd33sHzTQbB63bzbet+vv697c4dy93tpuvoXmuU28cbNd3+Pfeu8bBa2ibn16BkPbXjeDVAWDjtrmz9z54s4d5'
    'hGneD4PK8cZOfb/ZKCGxtW9h5g9r1cpx6f4p5928QimC9MSOVZB8fX0fDm8wveSVWqdAA8mIsqiRQU/qTBfSuQrnzn/rOxzX/fbV'
    '9k7jdrfxvnm7s/3yoH7w/W2zsfn2YLsFP94evGts7+zUQei83dxsvbt9ubf1PSJ9q958jX9f78G4919j7OU3ey8BUolXGvyr48W/'
    'A+zvcXB5/reJTb6Bydrep3+asPZup5QG8K09/vebg/r+a+g39In/bd7Sq+1N/bd5+6a+L2GbgPakfdsoKU5D81D9ujTzat/bpelk'
    'sfx2s75P07z5+vsD+AMT3zgIWq+3D4Ay375sbbcApy8rGwdAuqXPafCB7wyV3VZ0WszP306EXiQaKf0oXeqpwNGY0P5u/mxcsgpA'
    'fS7j8lbDufBAJdziRtfyctvoIsimETL8s3sXFI4qR9WHG+XV2n/zi/m/KpaOgOn+8Pv/9QOGzh4LxOTuqMDKVP7dHzd60tvKjAhK'
    'deuklV9ewXf5e7g7Z44v4MP5X9Mw5WCrv/grGC8Ob75YQl3vOG/qHTDzh7Xy6sONYzdPh+5kOujFI97cS7bHz/JBufQymde8ia+j'
    'bqVDjp8YcgI3jyEyGrx0x1jKrNNTyd4rfM0OLwB4WgXpsxPBgcYmhUdFfYWSfvC9CgHGxPCrAckm5EqMwPISig5RxogpqRvlcvzt'
    'GGRZSj9KkddUqiHYnpRXIWcggh2vDQIMHXbtrqYdV4XTRAaHlKu+WESzvWxOKX3hRxYBWETcIB7ybB8/ulW/qkjBZ2O6ORRKMKyd'
    '4SpKvS8N9onJdKPbbtS77ca33fC2O77thbe96PYy7N9e4v113L8NeyXDQAh0Dmz1gulxfKeJjornxoxmMxx1Btruj6LehEsj7clB'
    'VtOTTk6arPisBceUgI406kD7szkj8tJI6A6SBOBrnToPFR4X+GFp6Zeo88B3pJEM0j5aOHbxPIhIgkkmC6vqA3kF8TpOR+ZmSl2d'
    '5d5MTbsCWvJ9H9o6YwgfYFS9efRP+zp4bDSMqv3DNl4AFeWjSb626ll32p43+N4GanoXORpOyej6SdUftA8Xjysh/FMyqVOhJJMM'
    '3uZamDZ+xSPx9nDhGP4XoJdnt6rOxurKsAmoRjzDIhqDWHxjdR6ANgxSAS0sLQxGihfalJe2AxUJFvXrS4AAp4NOsw5VL1XFyfS7'
    'nxlVb/dPyYiW+L0+EpARIRrswjRFShUd1Jmbq6zQpMgXaaUVv4/CYRskUcRcNsc0pZGmmHzIkVXyR05zpELjx7/jxHFOPHRnkagL'
    'D7x5EjHf826isLQs5zliTuDw9vJ32oXvpKW4Mu02djl7q/uZF8cTBJGc6+KH3oZPRkgPi/aiAR4zgtSoJCBlXeskMkVmQXmPBDso'
    '6Xi+oQspToNtbrbsPdcGexnhhZa62aohIWLo8xs3yC7T18sbTvarYD4wOV4JTLYBW0B2iE02cj68EImbHi+Uxa2Fve9B1rlUfVLy'
    '2ibzHY8IFjJlXtjLONPQStmrt7AooT/Mn2vjwyWL6sSJh9WjdJ7NSPmXNSPl1ImUOdGcOCe4MU7fQ5YREfryUS1OtYPIR72DFDNT'
    'uBFgCvLFjKEA1p64qWjQ928qWPI7vKyy4MR+It76+wmiedXfIRhaRZahzQGwoBtyqjv7wuOqvb347uekT8+Td9rR6CqK+mJPfLS0'
    'oEPODb+rPF4AbiZTtTP3D36X9KOS5efd3tmPkXnW5V78CDZnc2+Oi0vP0uOFWSUhScWB7pQiY/F0jxwEJSdSrIJyP8FCQSQjC0uQ'
    'q33pU6smrAzFEriKX0xLNKqxDBCHbper3t3ZT5t4tRzjyX614DzsnV5R0BkmXXuyVFSrcgX+W7qnONX3l1WlBwdYIFPyeQhjx1EB'
    'todj7yVSwOmgb2mUVoXlGbycmc5/rNVZJo1nSayKdZ7r7DJ5RITwY5aJGZVaKM7zPUuFyk5cLAbS/cuFin5H12cWolgy8rW/aIiq'
    'MytGQaw4pTSXN825IJz18qQqr5R+Jpx+4qp5KpYCX+XjXRppdZTxANmNWWK3YQ4FnixCROonc78W2ILm0k0qPD890AdUZvlsVKPX'
    '73cqgBXQd/mBIUzNrb6rqUkrGxmF1vl3VInWAH8R/Va5Z3RX+BHQ07geYBwrPL8rhyZMCSA0T6ht6ibjdk/FW6GKJ1CeaK6ccx2o'
    'Kt/M5DBl/YB9hIhxlS1iyh4qsgMVg6R+UhfRg5ibF9bWSrODf1AFOqOGp5X0oiF6Qqc/SwMCZYJskrCh9JJybjabmW1kx9iOOiGm'
    '7ybJJ0Is35AWCLn2ZUisya6TpMf3+WvOISBzClgprVIv/u3iIiw2vGYesblaT6jOMKNcO4XT+iiSDWz1zgKngcXlzDEDpCTdwIpq'
    '4CLpRmiNV/PFNwmbr/0l7KUM7KUnBvaTDOyBZwVgILMlgIScPRwtm14vLSvIaL005CVNygtGuNnuUSUtWyGW5LTyNIsb0/8lg3zL'
    '2mntBCk06xL9X6Nj52AYdTHv/c+F8nkEKI6gJQv6kafKy9q1DioE0TUwGq0a0sm8gbAfKNMTR6dLVlgoT/3z/20pPgh++Ju/ncEI'
    'zCb1G1nTF7LQVnbZa+45QDWgedCSOHDhykXjLNsVXhvUE1OKmK9oVVqbmVbhhG+3nooGBZIVdch+eqQ+6e489uXoNbaI4e4oKxrs'
    'jluq2I5CjJOvkoGbYMEl0U8fru2puwFwd7kp3WGvxCNbAlNI684vS6UmInON7XC488p2Bzu/6Yai74wj0U9r4+PiU+zKFQNPd1B8'
    'fKQ/Pphi/0f11vMmQm3jF2OUcSO1foE/66JqrK4AR11FY6FHGLbyFDpm6pnNUwxR1pRDlGJRxfIf2EvpsxWG7EdvL30d9ShEws/b'
    'vs5EJUmVMhJlP/I4dzSUqZEk6sHcrr42nNN5U0lxjLlo0LRhOAqKP/y7/315hUglLZXZjitVAanpglqd4t7A+S/qq1DVxXfVvSqU'
    'Lu5Vm/R3c2+3VdgqBb8dhz0S6MR2/W/e1ne2X203Dk4OGkQS83x5f1SEv++Oqht78P9b/Kepf2ziD4R5WDgaLy0sPv9wvLGlTCJe'
    'be+0GgeNrdut7WZr76AFv/YPGpWd+n7pqFR6BIC/Ui6o3Dwl/uWmmSKFp/jRvPUVP5qk5rvdhjeHUKCqijQOtvcOjlIson6S06u0'
    'KjK8RnlL2AR6HTgbpEEx7HY5/gafDPg6F0r1MN+h6TvbA51sbTPuqO9kjxPs7R7W0L+dnipv9/lJW+Dw0/7eO/6BtjrmLRvm8G+0'
    'Ggpae4yjW3i/3WhiinA0w2neqnzh/JoHvvm2Fbzfbr3m6s039ebrAN+19uiNwgN3ngw2TjbrB1u28/QuwHcKwtv9xgH/3NtV5tn8'
    '2ALsBu47F/pBfbe5jfYiFvqr+hameC7uvW0hAW3vok3cxm1rD16+3IGx4tvWXm2jhHZJ8BJ+8yDgN7y5fVNvberfQF7NvZ13DVXs'
    '/fa+/qkxUYRnREZpgxCpvtIQEQYMUj3VeJy1W3pX0iSqh7K71xIEykOBFXJ4dFj9+uj46Pj2aB7+m35dfXSLRdn4hgYFPw8aMOgD'
    'mLudV7AO9rbebiJOSiVaYlXMTK5JE+0RK8lppQsrOe2Nz3A5U/x/Y5Q27pNRVI8SLckUAWJO3zROgC5Ud6GrR+lhBaS7YzT726p/'
    'f7u7/c3rFq3d7d23e2+btzt1TLb9Zu8A7dluG+8a9HfrbfPb2636+93b+iv4vru3twtl3jR2W80NGBhX2sWF2IQ1IFCGt5TjtuqY'
    'ZmL1nZ3KZn2/yTFsukmU9gsj5mUBzBYuaLLEgxEr3jYSyIBFCKcAtFlgcJZ1fLu9709M6zVOLqAAaUkRnKI3oqRb+lTyJnj3ZBeG'
    'YbFGxn6Mo8ZWbQPR07i16POxpXFI+An4CfFC8yGRDb0LVN9EFwPuYMlljCBgoCMRdEfFe1kPZNRMY5Yh+bfvwm2O47AFJZiCEuSB'
    'Sfa50tebnGCoeVUic+EmbtOwQo5hDxfX7F2bY0BRFA0czul9cxiT+DapCYfVeLAUiXhvxYTPAN+3TppY2DNKuXMnYAe2+d7NZOyr'
    '2vfMFOo5tYBRdOfIOu2TwktdXHPArLnN1/WD+iYQZoADF+dfDs4PPcRzBNYxBLi9u7MttmZaFmzodezbe6G111Fl/vjTQvnxk7sS'
    'WUNWPz0u3wFNjz1CfAciSJe7h0TEiZQUDjhdM/3JaIHppXuLLF+tB8sLk2bwoW8WRG3mlVZhoxIUAlQ/pOmUCMuERUTbecCEp+UV'
    'StVUx1dJW7PEK2Hnrgyt0LbKmFZpx1rfLFFdjbojVMVyB3knNOtF3LKIRW1p7sSsSbFLNuuk/ZG2R2uJNRGHmWXgCPubSqnYCTlY'
    'IzwFP32hPj3dcdxqVYDTi5huM2x8+bKKn8eBr7kSOzfyrNsgnzbO8cl1TdXaqF6rV+z3qd9a18+TG/v2Rr2y7pv6i+fBaYuRg6Ys'
    'ZX00uZB21NRl8Fl0STuUyo7xO+ETepJ0hpsiJJ8u7L4vy0h6m2FHWe1XyMihlyQfQxQiSDLnFLEg9aDyi/JYY2YMkAk+RhEcmHrh'
    '8ExY+3Mwv5R4GZxpEcBZfBmhKbm1xbk6j/pBSGnIKZheD0OM9ummC6UtzzgHDQj2+vtkfkHO/fXhMLxxwuRQdKBesbIozcfCdNSM'
    'ov7LG1EVMxqUVv0IPF4Qj0UMyLPOgXkqFcMdTTcOY7yYcuGTv7uJs0N3F8GGXwZj7XplakFlUfjt64/SXsKHkvpQMCaJ3vKM9PIK'
    'LVkB2zf+yHuOlRL7iMu78IeT9kATILyUFwnhI3nZ6j3RlnUttFUN0T0aDlQuo1uveH3Gr0v2yi9rywHlYRXNONJMEg0xZOquWJEP'
    'WafEw+AUTg9zZYjpODHmxhSsR5kVaRrCV8e5paGgV5NCIm2oeDnuN7x41MEF1GgsIOg36ziL5p0ajisZ2q+S8Lwhedg2dKgRp2bQ'
    'KXPmlZk2nd3kIu6H/dEmA1ERHTIg9W1uyQ/zQNe4sHzpIvdw4XijiteyxF/1tW7cf0nOZiotASvhcavEcAt9VLlLc+4f/uZvjaBG'
    'eXwnhe6S/MOJ1mVjQighricC6zh+BPaznAIxqWyVr3MsyvrX9gjG9LrqGdVhbCWP+I79MirGki7uEJx6aSlNXFz24k48EhmBOUiu'
    '766HcX1izNBBWRdZFgU8auxWzTDVad/xWdASG+73RZWrjvd7YRyPCoFb1Ad8RT6I5hzGoXqtDOcTgIvQOzM0JS8dvN1pBIs17y7h'
    'pyMfsfaRFc81dK+Xt3f13S1HZQmH/SqiHQ78VVirwJArQPR0nwhbdEmD2zuoWX1oRh/AehG/qaLUjvTGZ4R0M6uKB13TAcrlPLlz'
    'rFIhenP8i8Nf/+L461+QtuOLT3G7FnCc50006EY1CkY8+CPMF52Zs2fs+/HwBQfbqWlVrAyNYFJefjnK1OrYGjSk1a/4e3/vHf5h'
    'bSv+8rSrtSAadar59JOjvMhFns6j+SWwty9CR2t8pfq0oZwly0qPrfyaiQUqVqfdlY3FxzA6AzLrRXD6wpMpuiopeVjF1aT5QOuv'
    'Prn66+tQvDq9qN5nqP3HxoakpaWavNT6CZ4gef4S7bv/dO6RMDzaOwicoBh4IBYWRFVdv0VxgshpEWZW3tVHZyCeFVnLXysHWqFY'
    'DrSGnN8jOZf82F51blTgb8256QOCt+bXVu/k2WXjhZFUyZMynjSbpHhXmgRS3hvlfKmKbuiokDe3AbWNW30LUHIdRqfq+oyzYP6I'
    'fDKUyWpzHDi/BEU+rnk33T8xWjTGcANDlJ5lKJGbtP4sBiVDils6RngUU5CctgUEUnUb2MDHaJRSLsQ2GqXiZm1E266MsQHASKol'
    'vnUeXmJJVV/lEa0KigVWg1htsZNGxijUJRRZGEi06JkSFPkMUtTziyo0w+NLGd7lZTxWqh6HUmYhjOWaq5flC2CrjJ0L/mjTrlBI'
    'rb8B9BnlbjW6jjoZ7KlyiJYcaYneT1qKvoIzNqpeOuIQ4EPMmiTOF25ZMmCxZZf8sjy/vh7ZtiO6oCdQZLIWHZq69HVVm/jadi9T'
    '1PIJjiroUkNgkiPlUcWTmheI6afPLpYzzKKGl3wBXvKV8ywXDPNAX/UB7l8xXqVby4R5ZbSAP8hqQdgqGL9nzJ/bP5M8AbWBmyoi'
    'q9b8CFrmQmOcYzxsaCLM06NkavXNDRdVyddIqVp6dDtab1ljXzJa63FqFrh1FSziORTRV1JHUnXc8Q7FitmZ8/GG+SkP6RQFL3Pm'
    'Tn3jKZ9l6gacYVOykV11CM8cx8UJXpzJtQLRg4DChITmHOnlF1eDJAzpdedfh6mxWFvLHR1wJANReIxZmcV8dRRMoqjL5+4tnsP+'
    '8utk58Ubyg5fuuX3w8zR9KZzihVz0GT41cZE/D6wQdeKAn2mAQKt90pDjLyd2scAjcOM3WKpJNbIKyD1NuzxNSs14AIA8QCmEa0A'
    'zMn/kbuIMDDrsHfjihDqznqYhF1Yj3/NxpBEao4B5TRb3hWBNGU46LizOvF09V3EJk1fVmFsGJK7t2it43qw6Cpc+9BHkuk3x3S9'
    '9PChr4RU0fNtIMm1NV9RKUGSEavlUTrOqfECQd9Ma3hIUam1XSKO9qmjF7wZJGcgBJ7fNIGH4q2K4qAPWV9NDrYwMH8Y8CqvG05c'
    'YuCUxIYVRJdHo2gm+C/GXMntirO4cM8FeoFtY5td8gTfVC6qecTp94r492u62HM7qWBs+0sFF4RDgHgWEWRCycjcronlUBfhvpXp'
    '8TnqMzEgCOcSNAQ/j1BHvGT0TRbfhGlgg2F0ScH54jTp0ZWZUamgiK21ALx5U/QQip3Eoa5SubGiJSwjQV1EsOojg5Gix9LcsYtx'
    'HkRppNJrqfaCq/O4B2eCHuWyx1OGPR4obbdcd1CdOyRk9nsmSLWO8qIeD/TPmWTqL4P2hX4pM37GQTFPAMwX/J7WrIH2T/Pye5L8'
    't5RxJJRq4FkuMuh4GI6CHFfaqjiG5J3OvGkS8rk8lmVmwN4uWqjWEF7R90NPyTHpBGQ7AcN+26+EI9jtYfOSQSB++P3fB0PUweGm'
    'plVpOsIQa9qIkf2o0eTR07OadT2wStWfIPksetoGCsaEBEG7AFnbKiLw1C+GaWoRwbsEmHRXsDbRdjJfw5tDBW4IrcUFMrsR9pZ/'
    'nMuEu3tGjIcHOWD0EooAYTCieFTAgIepscYkUCal++eN9+mCQ/FNOuGFok9az2znIRlb405cCj06czk9gim3MIVNNiVyK0bVs2ow'
    '51hVzpWDOWujXMNHZSNdm1NnTOXTjK4lYerONWOFM4ygi2MIWwGbIXHoLg6IRRji4VQd5QT0+6BBNrXtomPxaQxi0eYTbX99q0/H'
    '5FjYIqMBLfzcqn9PecZWJdVQa1LnkpeOOUcTdWeneYr+PVPlTnilnlxEwzPMdNc0l6o6WXPxBOg3jDHrrXqFqYzTojJ1KvlRtqaX'
    'Fo6fXJDO2tpsCtNoaQfyImVIpae7kmuAgdu/NJLNsWVlu1kRJvbro+Lhr0vHj45KmeXn2LDl27rmRCQhi97v6I/SxLP+26jEJ1sT'
    'y9hmqQpW5qXV84f4eXFQ2EGCCpiQKNaq1/dtzm1LjimgtmEYSnHf2gtIbV+6lRcOjvNBjZX/+smOWHdjglWDJorJhg1MH6ZgjlmB'
    '81XE8TFBN2yCdbVCKJW8RrsNkaQziOik7bwYZwHmIncyRHE1ISTXyXAV8QuAWgT2dbD4bjPsv4yc8EICqhE79DFefHOV30Y/QGc0'
    't6Tom5/6x0SFtNl/MmF5PGUwDG873dYKszWV2rcap68wfpIa9glvYP43gn1ybfMS6vgQJ3j6U1+RGlakUtlHE+PYdkLqlZ2Zs0cF'
    'oRI+nYSfkpPH3uLeVxY7aSI0EXsMdgqrzuGyVLprrFjzUsHISkYXh7nNknFKGbgRwiH/EQaLzrprqwQoHB3L1DZzYAJZ6U/86oHW'
    'TXEpjJplC9w80GqpvABacfqeL6tajNQJi8ZEG8knfO8bG/rkNqOMleTQTFcNAAuORCzRQ7uDSFQ5cbvkBxm3a/G5jtt1kg3ctVh9'
    '9qQkeYfsr6Ve21VmkB+++uS8ugu++mSYyt2H3ADr3p2MmCiN/pMbubb8FaoSdXNJxzK45NzfaAqMKanhBCi2dQ8SENM9RTBG18KC'
    'XbYTyhl/+rhfpM6Ug2kj8JayK4+pxcNm4UKuyU0Pw4W9VY8+ogMrVb1Reh13ySsAUpxSVugnbLN7cgP/vy5bC/KysRIvsyl4WZp9'
    'lz3L7jJ2XcWbJUNKFBfUsy8HcuYwtF6Lhq+SBLOIqX7BCWZ8QQm7TPqJeu8qvGFH2AEpYyuUCFSfgdlxIByO4lNY19b5rX7Q2n5V'
    '32ydsJT+6+JRESWtoxILXFYCsz9vf11BYbCLbqmVr7RXGHFu1SnUJD92uSF6hKLS18Q8khfUZxH5OrMhpBVHlerBJ1/Sop7c5LpR'
    'yOx+ysZemVeeuGb3z54vuTUi7oFhGU+WZToopfR+YmhU5CHC1QvMhgCgpky9UqH/VP0KfVfE6ihgces8UNq/VwAzBsACFxoTBk00'
    'fr5RYLvTPIbtfWGmrJmcJm5jTC5RrszCsQNZk1aekY/yiEv7fe4YMJWnvFNWFMAZK4vy0QsPZTiAo6kenQ+j9JyTTdmAjHYl0BQ9'
    'fuKeRcxQOQnf545UrA4Wvz5OoDoVcYtTVYCAr8W1SeXVu4cTMUeSYhZHePGg8bAqkHT3YOqQH2YG0vOFyDub1kdn2TR5PdnWOYJl'
    'SB7eMYVP+dfWkWXCUL/X3SuGvZ5KX+2yRYcnvcD0iQpHxh7ajrk5wjg0ZzdoNqwSner8pibfqU10Wgr+kLgqm0kPQ6qgLkjHjEMd'
    'XD/pV2BCLtH2mrqAgy3e6oyot+i3Vl18Evzw7/774Pk//1/WpR4KG3cZ5q4aI1ODyqWxc8mVk37VHtSwLDfvH5MGgYitKtfDQ9Ot'
    'w8FxKZBPRpimtSA+2GyhJTdUnJO3NX0P6DpIRjZW3MfoJi0aQDKzJvbEqbMu2MeSxz6WDceiyxdqEROpeEuhFozCjyo32mJQxEAg'
    '8VD1jadST1/J2I6i04NHWO2b4Bp1+Ziet4/BgfqYOQdexMOMHRc1oKbYImzC6N0weY9C2H0etdG3QuHcAPNdMUymTHEH9Q0G9lWx'
    'm03GXw6b/XhhMArOk2H8O9QO9no3cDbvjxL22VRByQB3F8ogQ5tbUHjvMB19R84PlefPn2dcP/XJyvTUp7rO+WdFRFQU2TkvZayM'
    'VPce2cyHFdW7dRggbm+qhJs7sXNuQqVT4bVgUt7EzrneL78OnjkKR4MZ/pHxHlHfTReM/yqlgv3k7iUaRtZv6y7rUGq43VJNXT3q'
    'pM1B2BkmacrrLPjjOYdiWzixzWj0eVzr80NhPhw50bPFRuB4wuE1ZB76jB+P6i7sxqXAffbTFwfed0rWa9PqrvpM7f2bk/d7B1tN'
    'FsG3DuqvKNzEq+2tBgjd9R142P8eNeX7Ow2MiLHfOGh9H+y9ut3aw0gbAX3GH6/2DtCEuXWw/fIt5Z1pvt7ba1F+os2D7f3W7UHj'
    '3XaTwsvosBpc+T3q4t/UD751ozzkCl1Zril0y2G/G3cp0BnzeFdjcsh6dCKuY1zgXqxPgTbDig0HVymNhQiUMZtM31+8B+YDbWuU'
    'ZgxdzSGfSpZEj/XhUvSxFoiW7/z1xDzF1ldera6UEcgWfNe3Ki+zisppzHHpdU5lUw04t8oWDM0KOQ2lsMEwORuiR8JF0gW54dwJ'
    'C/UAWe3JoHu6r0phzo7hJRm2KRlInI/PkyuAqIsWQYCM0J6kjPmk3oDIclPfZoQjVG5uzeSYQkMedbJ+ebPdLRag1YruXIVKiwRz'
    '9KxnLwOqgzdRkYKG17uX2p2filYpe3deA7IQxdJUhjIFelVJLqNhL7xxisX9PpyxW292UKWjCOQFtMiBPNfmuGY7uZ6Ds/VNL1qb'
    '49S+y8sLg+vVASxsjNmytAIPc+vmsEMQVPlunKKKsXbai65XyWOhQttorYP60eHqWTioLSIwvgeEtkaj5KL2lCC+OF/ScPhzbWEV'
    '1Q0VpMjaIhf6l3/8u/8UbJMLN7JxmMQX8+dL6y/SQdgP4u7anEYVoAmmsdIO4WAx5/cPxM9oFY3MzijQb+0XTzvLz05PVztJLxnW'
    'fnEKP0XLzugH1wEioA0LKhpWhmE3HqdchGpcsQf804UF6OwP//GfAqKmoL79Yh67uP5iHtDlIc/ptiZF02fRkUVohbt4GQ6LlQou'
    'lMrjkodNwhTVOg0v4t5NrbCZjIcYpXUfdouoUL5I+gl0phOtXp3D9FToN+AE7flXkXBOe8lV7TyGE1B/ldowL6NeLx6kcYrTlTMS'
    'RUhJZ2jJFaFC6Umf2+FwzsUAvXEIcOGXurm8RrN4WpiAJ/pLZFkjZ5A8MnT7MuiM5tYXfnnPWHvJmVcP30zrrGp4lMB6QHLK9Ews'
    'MKjZHkMH+7pJqFVpj/oYlaXTizsf1+ZOOhiGtYeJP2hpFEuTyEfT8TLQ8eIyLalNqqsW1Yt5bkt0W46CHz4wVzFMrJ10b6pkwNLd'
    'PI973SLzPH1av5dvGqJHiQbvWNAcjgz09IfVmcAA5QAEGrjJ8V1Y+GVhttow15n2Z68NMw61JYvlMwBQYHBCXGiWHURyLbuHcP2S'
    'gqMGqHgZ2q6YPQsFd3ZCqJAVFcnwyOyoK7wL+LULyKwLtN+G6U2/E4gYzT5V0S6Gmyy/YMrp0Y2RDudiIuSgBd9acIKaustob/Pg'
    'Pb3CIv47s0NjiOab4FMQXoWxhrFRxeNojOdFEDiDO5AVMDHfCfQFaeuEkkk5ezkqn0qZaNNeKR6aNhyyOhR+X5ppkH+QXKDEgglz'
    'oubMGQNAA1nRjADIVV7dAe3PRGC0RkQMkvZMI+DFofvexuwf8I+31KAMHAkLvGIoWEgbRgj/eItKlPMHuJOcFS/SMzkwWFgz9ZAW'
    'oJG64EmefFT8BmDAM8he8MPrMXSJAjQkZw6bg4Il/T6Fs2Sv10oGZBesn1klTuP880slzinWX8NZbAfOYfQE1HkKxBmTDpET8Mbp'
    'qEbBw4bJVYDme/i6rJMooWaILCWqVJ8NweEs0sS6vygHLQqdpHzB34AcUg52IvRs3oo4pSs0VQ52Uen/54hhqalGw2wMIt4LfjbU'
    'gVO9AwRAfV8Dzk5TTVGmPmmrO/IHG8GUH36Ku2WOgAXjxJnu0Ux3YabLHLXj7hg2AFLfa0AAdW4R7fyW4J8ffv9PQXGxglfj2oyT'
    '03OFOmxuiY6JfrfuVvn0mPbY4QhDd8N5UUWR3DlBGj9pfb/fQK3FISz4wvsm2Sy+RzNmJNVCOSg01MvG9WgILIU+4vtX/PoVbHGq'
    'LEJ4w2/fRHCAuDAw3my+la833+JL9W4T97DK2wHXb6i3ujUuutdisHuYrRqAjntdsk8v7O+9ow/7SdynEM7v4uiKIXGMA26Isj3j'
    'z9b7vQoOG39zqmf89XZ3q3FA+hOuuvUWzbYobgJ+frl9sNWsNL6nh/d7B2/Uw4PjVYtMFR3hzd47i85mq97a3qR+1neDncarlv59'
    'gCZw1KHtnVbwdt/83Np7v6s6gbmwg+1d/MS/995ylYO3m98aaPyk4GG9/cYWprXeUVDNI0MOCjqvNv42qbW5KiXeVvX4t66E6btV'
    'X+gndQWr1A82TVfwtxnYK+jy3nvuYX3z2+3dbzyE7TRgggyqFpcvLrDw4gr/XVpUf9X7JfX+8RP8izWWF/jNE/X36RP+u6L+Li6o'
    'D4u2zqIuvKQ/4mio77v1N3sHmFaau2n3b1w9V0jIRTwuDuMuKcY+3TnWBkrP1a1xghC14B49Kpvwd/DF1Od7XVJ2Zlec0mxcujXw'
    'BdfQRKUU8biriHL4gsuZUQfEapxS+CKQEfCIDdVECY4mZErcuXt9sAfSQjDPKU9/BnzbzmYCHW8qPlk0phffRtEgoPzAAeox0Wif'
    '+AkngcUAfXB86PUqpyBZjdFcl/ZxhEHiPGkadA52nFtgRM2d4CFe3I+BU5/CyaVb0MqyiTJf2q4gC0fRopJGymhuQ0mjKcnIIGiM'
    'blCmI5G6IDIQp1cxHCAO4nY76bfCNkBToArOfbo+vPJhBeTELdWb93ocxUIvOgs7NxUXgHJyBdmSI15NHgVUq9AYsLCsPEqS3j3y'
    'vK2sCgvZl9rGgHDqkxSEYQ5f4xLCpKYRqdAGYT/q4RXWObxvjpLhTTsJh906AGENv+nDb8cw780I73OTYb3XKxaqLINVCAYcf/Vl'
    'xoBuMoKBe7BZU8caeE+aDCSLKmxesJjY/PwSz7xK9zyt1Q4uv8ol7mC2zQ632ZnQZudz2sxg+6afoNpLzdTGNFjT4GBGCyCXKBp9'
    'EUhm6vPAXMZp3O4pONiaKIN3NE47CpJfxIGBfh2oH4DFznfAyCKQ4qKLwehGE5+8p5VyVslcGei3COzVMLloEg0V8WxN7ZwM4YAV'
    'DS3zcY+JRKYuY5p5if1odOcst3txzoymTuBR2kJHHxxpoeTtEYRVcnfiAsFPfW+YMIMpKutGrk7Fut6GwNuRpQFqyWpnU78r8gwA'
    'L97uWiZmqmSP8STZo2xBYVariLmiKT6FS6Fe7BDtICu49azNEZy540LJtsqgDal+Um9pYES5V60kBLor7Ca6G+ixx9N2E+Hc6u6a'
    'e2jeM69jCk7Bh2JysuWgWnxMwdikKnhTOYClx36w1AAcgGA7C5jEuiLm7JU4vgSqsI0lGvUw6Kp/o4zt8LbUpPNQMTaBLnUR7Qy1'
    'FkTqyij3wl6u7UMAe+w4gO2j0+wQJDFn3DCW34wp4Abe9TkudoEeEMGis6J/Psy0WKUP2sbQM6KFTuxqHJLkiFhFNQRIGeG4Nwqi'
    'dBS2YUmf697N2o9DK+h+UhJr3nmQZclCQzRTgH3m2PTXBBf1jqOqA6SxDYcf3/bTECa+KIhUkeOnHFYpaPTDv/zjv/9PLIAh5wpQ'
    'uQsSGfbzq08Ood8p6vmAO6HLm+qAtXYv7H9UmCS1TfBTZkrQY4qFWZQMiGP/Kpq/b4sySyJDcZIeanhyblWDnb3NOhkXIGK36PSc'
    'JRQ97ZkJzd/sXPwTyxgl6BrJ1PzT3BXgNIe4x+Fq7YzVqz90cKm/H0vmnl+CFznbKwh8ln4UNrdgWwDGQwj9eSjRJHa59w6Cmda2'
    'u18M0ehfOW0elKktJa5K0ToBz26qDz9qSjajXg/jAPTPVAalLx7U9EtOwVvauTLoL4NEHKE7hMjYIWSViUh15Y4cSeecLD9ZQa4n'
    'oN8V6F9z0W8owJ/vQ+rgsfbczJkq14FEjVTFExYDFiPMiAGC2j5NIiMrXnBHvG74+88BUc/PVa/veDq7y0DQCJ3XP1NRYA76dqKF'
    'tI3aXxa1N/E3TkFGylaqBgopjNHRsOBGlZ9RnfW2T7+7hRzBe+IOKnUYo7DX1CyFpY1h1B13omKxXw4+kmiKoZc8SVIxmg29F5Nx'
    'dpkMtJU51vnoomcsmKQpRtqrUJfJgsRYLJBlkC2hzgJUcG79q09A6o20U6Tn0h1t4kZnpWx2JkDCaDkIIU+U8t4Sl1wkF302q70L'
    '/vk/gxRmkXRH60W+ydaR3TGGGJNOLlSKUPUIcOWhiU7sc+v2EANHFxo62ZPASEfDpH+2/sPf/D/icMqnPOgEf0SJ5Awqo3VtVdiF'
    'OHK4dyohMcx3S8llkR8VdxTFJC2pzQqIQxleThst1aiQ5DpHRy9+szb31Sdo5m4u37DHVDwnrzTXICdDVFiwP76YW6dgMAFDdumH'
    'Ksb9wXiUrYmKU3hCQ4M5ZozYO0WbPGLFOEt3c04O0KRPINfmMjy7wJ3AiA7ncVplxu1WVjZCwhKOfMzZo1vZuNUWB9dBmvRgs5Ef'
    'pV1R9UmO+dtsFmjT7JwMeuDo5hs8WVlTD7M0t/7//b//IwnM+P4eQ6Ys5wgxeTkbq8ku0Xu/nFMEC+HkrHu5WV+MhuuZdK1QVAI7'
    'Z6L5xYv50fkMhZHqgcRe77VmrIDH07l1vLqcsQIqGebW+Y4uwDu6GevhdcrcOl5VzVgBj8dz61sNNtbG89N8UCcr7RkB0MUL8LC9'
    'VqMJdRv/5u32PoZbmbn9HlroZcvCO2/esFRmfl+M0OpNcWBaSyyeaf0LWznEXZnJRYQrS67QjaJ7HfwyWCIhjjg98gD4VMEobQUR'
    'tdPlgjsU/4bcspHyq199QkBwaL37YItbZjga6pF/9QmA32keCJDwFf4FSfLOI/uuRFeXydQ2BCjpTi3PlMrQqb95VdZfpKSnE1WR'
    'A1b47Zw3MbD46ZggWJ3gcXYg5aCAZO/xPX+av/rkXOyT+/MIp+rDi4SsSmAvhnkhoAhuAyaHugUSUQ02YyE6lGBsXGf9Q6n6myTu'
    'FwuF0p1HQ1x7/V8TDbiYZ0GDvJInRFy4iLjQiECAkxFx8ZNFBHKnWRDBV+2Egp6Lgp5GAYKajILeH44CX0KYIBNgX5CH+vJAEFAs'
    'BnQZiYZrcyTLdq2t1A+//6csHn0JYhIaEY6Pxj90DMTG7xkEmXeVg+i343iAx6I/aBAmPc+9o8hII7BnZOUQoZUxLdoGS3N8xFqb'
    'E7on9Az4ByOguG3T9mP4+F0pR7qd560H/qIs4ljGf3A9pfXNnzRLRjiZ0z5Nh2OoUUxvb9HDzMT2+Kv5s3Lhr8KLwap8+4Le9kbO'
    'y3V6eea+nKOXvx0n+NpTAjUo0iGaaUHhuM/eecWByWlS4RCgHBW/FHxZhTE3jpccRffO6k96is6/jnJuoEZ0dQHHMA4Umbl7srm9'
    'bGLKns04SR1zvQDRLJePwNqqs1DyahW+UWe+LognFIL5Ck0ToTKA2kk6YS/CR6VqL2WqrxWq7IVZXFnIflWBG9hxHGPdkm1xSn51'
    '7LKJPhIqooiep957ti0EFNZW2IKwtrTERoS1xadsR1hbXFB3MksrypqwtrSAWnnhb42Wf0XgNFcktBXVIHgllKrwvdHvFq9K1RRW'
    'f1RcwIK6vxy7xB0OrUWoVSywKR12tcraOUQ04Y8+owiiPmPv7WcLATdnVQTH5UPAnUt9xtHmQRCytipJ+4cHiORp9Z15M0DIzFNl'
    'llmcdvif6egvYH6Q5+pAX2DpQ7FLxXcfSpn6osdPF3T8naLQJdzeHh6XMuJ7Kauu6GWl70dC8jY5DMJ2G0MFqTS2w+g0viYy1lb+'
    '9HV048CGyefQmYwSIgaRQg6DpR3NH2M0Glik8O+8sGvKUp6eeerxROLTbU4kPw3GSIATqdAISBMJ0YFFhr2TCNEKBx4t4n9Kq07U'
    'FJ/2PJdj0qnlaSFnVULe3moVpEuTLQRcm3SbWtYKPtbt4e2q7VO7l7SVK/VL+Fk8ZLgsMB71C6XjcmBul5HzzdPOuErpMqLR2nh0'
    'WlkpONkpT1V2bGbswLO0uYnMGx1WfrdQeX5UOQmO58/icuHEOJEj+tExdnSCqubq6Hok9qzxEBH49mBHOU3w1gXPRRyItHub4mCB'
    'qusgrJ7DWlgDgPi7m1z1e0nYXaPO4xsSrPjqCMbZii+iZDwqFktr69g6rJnko2gdwMDMPF5YWNAXtnp79C6/eYuMuihjIIlRexlD'
    'nPAyCuYD7FBwjqHDf5JhtxnRJ8kwPsMOs1q2iaJdah5XH9jfGKPdceyaYqgDEiW6OYVtddFEJ+KRvmjKM9SBsiWsUD0xVkH9cKAu'
    'rn7V3NuFbRMotkg/2Qg/Pr1x5R3pCp4Zl+otzpWxyadCm0Rd0Bsae0c/oUES209kXuGINQ5QB6L82Txg/EmPDx+qurdar57jQICv'
    'lUCHCczP+s4QUeIA2RVI0diukTjpQq+yQambb0Xj/DPmRUWs1m9LtkDuLHV6ST/aHybY+Xd4IPK6/knzWYoUUyFasr4SaJhwmUBP'
    'trdQFoMhYupBE/3kIrwmh4oFB0V07vKtL/Tmq6QCfSaavEunbPJJ95CIi3VurWQaxbdo3PlAbBrSy4PLqWhcd0RgmF5UGXcHLs3q'
    'sPViZcHYYzgKjruRIQlNoWlvH+256oNBLwa2QxJqF/Bc40WHgmfREKO9T/XqVbGKvMvN+55xTDzhRTQa6iVoxoBlvFGJNZG0f1MO'
    '1GYxLAekoZehKeA7RmiBP1VAUUr5AIH8lvVLPmqoBzoK+VErRp9JxwGB0rjlqhs5RAxHLUlLMvKM5isaJ1U4ovSKePovB7kDVhGW'
    '70q4C/3Zuu3RUSB4edCof4u+K/RSh+KvpKOw38U0s4uPKxit6SwZksAafsQNGybh7Iys5m5SDPRCdevjUVLhaGUpRugf8aXh5uv6'
    'QX2z1ThgwWkVZKMQQ6vzERzlYRCiKYgSg2ldJWxNHrzdrqnzAW3gRUqGRQkEdTfIkDooksN8qfpn7v5n0iSo+YgxZBF6iiWXcRS8'
    'Cc/iTkAxDwBp5+gQ9gVkjJdbJ5v1VuObPUp9yw5In9B5p4ATXCgHOioUnC9qhU35zlxaYBSGwi+ile7yche+ts9qheFZOywuPV4q'
    'Ly0ulZ89K1OoNRD978oGfjoa90epgqbgN+W7DPxn3ceRD39x6Un56VIefEpi68Fv0Du8hhpdJOkArXPpHEwNrISdZ0/bhbKBv/h4'
    'pbz4/Hl5ccEMQMAfDJOB6aqCvy/fef1/0n7e7j6R/X++WF588gRQ9DgXP6fXFpLGzyDqYDy9xukpLkL6bvGz3M3iH3Av0C/hX0bn'
    'cacXMRAF/516hxjqxyDMpBY9p8vhyuPQgb+8XF58ulJ+spLX/04CM3zhwt+U7zz8dJ4/O+2cOvAXAEFLz8pLufi/CD9G44E7v2/o'
    'HfT+dRgP1SfT/6Vwqb3i9h/oB4hncWU5B34PeQ5a9Ir+76h3eBmJ6v1h3JEYOo2ePAsFAS3h7C4BAS1pCpX4IYdnt/8mITY6QEfu'
    '/D4L2yuR038Ei33Hec72P8XLfo8+m/guoCw9ccfDz1PAfrjgwF9cJNwvPl3IgR8ORxn6rA9HwVYEUtM8Rg9z+x8uPFt54tAPwl1c'
    'Wig/X8ijH63E99aXToG9qz+b5buywqXF+n1a1v+HBpa4/8e844vNDMGpLYo2ojTgFDS8KVpG+W3jex3XDEUeZmDo5XjIzKxQLpwi'
    'gcDfAchb5/D3I5x0U3wPAgn+7QD7Ocd+A3sa9JKU0nFALeRDGEI+xb+nGIAH/o7CzkdaoIXfjC/oTQ/2bPyLcQfSwjEii9kc96Iz'
    'TK66BJtZX8FafWCfomTQi+hHN0LhMMQbs0LSx2xYIOvBbxgGhrmnniYXF+MRvw7H3RjDPWPdEE2D8OUZSPdUkoN4qO4QVyTPz0Mo'
    'gYP72I9PqeY5emlBn6A1+jMaUW/asM+ddnjk7fCMPl3jWKMRJd7CiqME24nCAaErxZlCyNENtQ+4jRDpekUBmgajZEAYbPOnfnQF'
    'kt+A4J0m7DFdiPqXUS8ZEOqRkxTO8BpI9m1I6x9aAHGcxwdcucYkeehMIf3u0mSp2TzthcTpCukFoBeBhTGWbAO6sfdoZUO0QYym'
    'zy1Z+kjPw5FCvwZwmmCRC3RDLBdQVEDkUKJ2zMpA3dNMvYbUEOIgMeIn4XuMoC5D7MIFIHTYuekw/mP9a6R6CLIyzdR51Is7yYBn'
    'oZ2EI+pWjJg6T4Y0YV3qUoc+hbRjYCPcCaTbKMLS6fgSv1+0x71QkVGC6vVAdTG8jgkPFwmPQm8dOAqYdUJCFyOiRIi4MRAUnLQJ'
    'bjzSn4hkqRr+6iUjRmOHu/0byiiNHafHizD9SPMNB5jUARkCAfdphbUR0BkIodwn3m54nemth+cypl61h+OY+5fyqK7UsgvP6C3A'
    'TTmDBtE5yN5nkaCGbjwc3dD64qmAyU8UNvRGhNig38wJLgaEeTSnxgowoedMdel5T3GhfsTrZdzXby6SxPxOB+jTyr/hJPCR1yI/'
    'A2aumCJ7hOK41xtzhJ6umiJaawodST+G9mnomIKCR/sb8s7CrkW96DJW62R0SYNVLrvQbnpOvqhqdZGBGq+uC96jYB+jfqR4lqVf'
    'iDxaTt04oWFQKkFsFDhaQpwpHtEUdIfjC0RWP4mJWsNeyHQDK5SWYtTrac4U4FonQkuSIX2gHsEuZ9Y7qnxoiuI+CwaFs2F4ehqP'
    'kHph7X/UHId5eUwYSU5DaqmrOJVqAZ/gdJxcMbXSEr2Ih0P6AgQ0YI42Ho54TQJX6J1il+5Wf84RQ+zxtN01EUPmFuecYCGA3gbl'
    'p1KpucqU3mzvdCu8UYEsdcQQ+J5iVTyr1A6r1epxWe1A6gH+xXAi6geFAFENKx85HRik3WUvTo43QrGqlDoM5gCtISnrLJGtCTwC'
    '+8/POA5AJhTAS33q1kHAprjFmxP6ZzrEm3o/xiHeVv48h3idzPuyqYS9talxB2wzJvCASQlhYJQEvGxsr8J/9cP/i/XD/2l6qn+J'
    '6AAZ539mpdbt36yciX7/7S57++yEN3jnl+P373OhmVnJj5/fLFv5i3P89/eDSTP5x/X/t1lF1IbS6+3EPzoOgHT615Act//JXv80'
    'Ux0VG/CUBHljeaU6SVcP6qI/AsYY0Uz7lzFqieDO9MkxWPB9+3Xmdnalb3AAcWtApiOKe+D8ei9vcJR074VmB2/CQdEDSfcl2sWz'
    'eFhmUeaYrCTo5wZd8cA0cUlKGeUWY08/Vcx8kVHTeyHIa92GjgvghZOn8GxYabt7HehrQ/MSBTARLRTf803Cy/GpDcKuzCF645Qy'
    'JwgbHmtUR87J2cj4LLtZJ3zXVVMG9CdRxjSuDDco71myk1y5YfVdjRKGPFQaJXklqmdR6JKEPdIhSLOIULoqOXbMkvj2RJe8ct0N'
    '6Ioe4zeoe8q0eOWkKmJbu3AAhyK8nJYWSg+kGpYv73C6rqpog1IfFRdKGePBK2UZt1haFbUt1qsok/NQjm2PAC70KVuArRThowV2'
    'J+xi5V+fCgJl2GeWtkZP1MskWeCMgFGvipfxacRWV5npviccxkPOryl8MW2QK05MxflALe6JPm3SDk30jx65bm89vWajfjoeqotn'
    'XsgwGLc6n0+4hp8kbJhSBFv6QfERtJuYky+AQ3ecAqOmeF7s/ETpuba3ypzA5SI+Q/PPgG0VOMDivPbqHUYdvstz8o3Zte7zItxv'
    'i5KnqMyhzMoOtQGmwk3pWJbxmBdfKBfRfNDhSA89jlM9D1O0RSyZPK4b1ikZJorwsVE9XHQa0ywnOypG+oydUaYNa7YCNrVwLPM1'
    'CMAln12S4CUL5PdpMyRXSf24QcvKy57KRbTpSuBe9mWkeVqW1Zg8yGUr0Ht+vRHgqVp+4g/HQQ1XpFmpQZa1KpW5NWIERmee+5QS'
    'r+asEfvVxOJQeUjsF9YT1JTFIVJ/lV/JaH7UoFIk1GxBMqSjaXdhGk1DzRQ1r3ywKpQg54Mz80DxBL2SiFv95MaycRmITSJrKNeE'
    '2JDZgsKhSgXh5pOnrNbvjqp7R9Wj0i09wc+m87RpnzAHYmHrqERWgrkphkxLmM43M6lEclXUvVhGr2s4O9C0mrQDmFq5STNdHPkp'
    'mh0EEZ/ONsfGp/nvNRaNwffiyoLph939eaeyjNTG9jFcHn4brZaI8EN9kvolVFMo7ideA/dwlVA5Jy1gI5JTGXLoc0pfIYiiZ3mu'
    'KGpkYlWtdF8EIraoyh7clJGcjUT0v/y3wUtruJGJRASL2vWchxfQy8WNQkoeVh+UQ4tzfGqBPHIx5uxj6c8quCZgrN7tQv9FYA0l'
    '4GUiiFyaBPV2CdIkXEpayQ30oogrZ3llZLBLsyanlidCv9QZanzaEKTQROWKjQNkvrJvFgkgm3B08orcuX5JCAzP1/chKnecEhHT'
    'xoRLY9qQ1XGILdVo6eis9HnRbqaM/57R54U9cVMc/Wxom+ziYdLSooprI/zKXDFDRATpCGN8cRRAGSJrh++RSQavHzXfV3KRk+TA'
    '0QwUP1TbXRVnAHMVcYBAqG/CQxwHtkQHoX8waxDgYirurgiCF/nZDhx8OEXR30HlQ04LmTH9iV3yFAViNN9gZIzyesThg58Elbl7'
    'zmfE08m7Z5gWTwc32fwtNxOTxuRzMhSDqtg59sukNrD61CgtKiaHSTi1oDP1zJAIanJIFx3KZWKkFurXPXFa+P5G0LB7pNB+Nh4H'
    '8M4ocQpyDIER8gxwVYC3Oi2Qi7NKv/pEYDYKymaYhAQV2ECuXeGp2+7ykufggCJqSG5EENOaE9Ql7VT5PIJbL0d4mRhTxFIAmidR'
    'qCG1qDtVfeYozQSAmA4CUN5EimeoZykmTc7VZHMnCz9i8huWFGtuROZkaKGZxNMpAYcAMgUcQrPiUQTYZCd/Hc5QBQ9H+140qMfr'
    'pCCGw6ln6DuRcnWbOMNYEP2ci6Jzk0b+YXVG92iXcszW4grkinyBgfJmJG2XmUYDGv49V2oOlYtbNam3inriBmKUnJ317G1GWSqy'
    'PtqlZbzitBcHxyPjeKyk6yFjauTyIvocvKrfx0y7zkXaqokLp+qWLBgHz85sfdQSUJa/syDl7edfpGe8dWeY0I/vsPvZCQKYZZtK'
    'KWpuNwrC245dz6d6nut9JzcQmhm5F7oqt8wsbE4d1SwDY1UKiSMe05ncxHn3bCYumAuCg609sNE6oL7VvWzAmqZQW//yj//wH5yO'
    'mjIlHY3rAwdTE6Acp30B6u/+OwuKylRVlLhcSGIMfnA26AcrGc4n72ocD0l2naN7SFgTVHThKKPThp2XHF7NSYZ0dCpcGjFN6kke'
    '5WjT1klUA981XdndlYJpZJkS+oOFA7R8K61SkT4IKmqRNuN2DzWarpmAB0hd56UOqA22JYANT27eMiSb6mZKtplzOWHOYNJDhA4i'
    '1B3lsnQDteUBo6Sc61yxpyIa3V/L7t0wJdpBeKaK59HlMOnPrf/wP/8XLw7hlMWCNTE4yGSpBvvBYc70rk9vWByq8PD8aFCq9zZE'
    'khvOxus9lJ2M8vbZnc6dygKsnInHj1ezL1dzQvWoRYKRl7KNU2gvR/CzWgQToaVgRkq/DUChLz3C09ER/EcemQrwcg5ezZVIdqQ4'
    'Ln6QP4rwQwwiLwLQdIkPQ91lg9A58XRUKXpnJhGesnP4YGJEHYySJ0jZvbS8y8TXSfoAGUWxtbn4tIjRyUi4gB2z0MDEvoXSJ6vS'
    'ysWxiLazan+vwa7ndHNKNEA1bC/+zvRWp8kGeRiDmVZ9/LE115ApQZdmyqP6wBPTlRGAkgjOc4Pk1ND/gPcMX0L+4+uJcmxAuFck'
    '+qR+yPWJp+bcs/BnBLf5DEHJDdGTE6GHb1SF9CUD5twbMScT+8R3rAyarxuNVvOPGEfn2VKJ6WbyEX6yGJoXPCM/8EpWKCSpkL/I'
    'qzUVnsWId3c54loBq+KwnfckTs0avMURrGThQAPGT+LmZslUzRvyDLLV7NKVDo1w5qt6fOQGHhcWlKXDDS0tl+7MFszbSTko2CA3'
    '5j5stmAoFHhkxsgj/4qBRww/OWFWlhN/JJg1AolnZvynjULiXnwxm9bBSCbEQasFnWGSphVtaqYdsAGbGBvoT8DeDyKR//kvmr3v'
    'H+xtvaUwtYLFU3ZOZh7fBweN/b2D1r8Gv5+BZQFpvRzHvW4AsnuNDLh++Ju/VUZ6NIXH7qnxTTgQRiHTdMLyKiOHD1rNFVmN+SZp'
    'D7mtQ/hzXArEg7HfUhYX9gvjQbbqbEel1QmmYRnDZIZpDZMdm617dsMJvHrqlrVs9h3P0k93JMW1VQzLbWAv4eHCMe2cvWgzucBY'
    '28U2vCpJU0Cop4yKPEtAf2eBgnoXebyAuwhpMFMRsSpnP7mTewYZB+KuYVjYVTw6F7rNB3kom0a37tfNelPISoUpceY0FrX1UjqS'
    'tDqZUjN0SpYlPpHyDrbumoqoRg7xIyDaeXTo1PkyG53eCYWsRxYK2ufTBTafRxg+WWA5ly5mSmIgLxqmkZAinalkYUOniU1CpKH6'
    'ycsrelM+4U35z0Zc+bv/ARa8K29MlFZ+FuHSJkZMe7n1J4+Y1u7OFCtNyVVToqS93Lo/ShqN90tFSYMGs1HSzCbhmhJNDJDGn8uB'
    'V3lV1f08c7c/Vrw0Z46ykdL0GD7pC1blgktBuvxQWyJcmEINJo9E66HgFKYv1fPW7jqxw2YNHeZWy4YOy/meEzqs3d37swoeZkUX'
    'HT1MTKkxNc+NGGZQ8V9jhmFsrveNnc29Nw2MHdZoUMSwH/7hP/x5/M9Puai9mgP4Z/yzMr/jqzcYAwzhDXS+qBZhBKs2GWAMqvAs'
    'ZM5hVz2NcspVOire4WMFywl7KXzM+lLHKTm7rxHU3Ls8dChX7t3oDy86a2EzlJIPhBxPdf07O+wMoOn+oe6A8jw6bRsGCFRq4NUH'
    'lsPDfLFAchfIvuxjlumD5gU/65VB0QJ3t/f3GxgR/uVB/eD7n/+g1E6b9mM4xLMjDBLeKLrAuDLHZTrAgFxb1HsQRt5zd6NhiCl8'
    '6EiG3vrhWYRUtg0gioX0tKJB2/DcdO1FTUA9rL0hZT54UQpqXOhE5ShOtVn1HSoB0QoI9WgOnEx59j2gAaBk4Q7A7W6a192y7xlg'
    'myshdNET25LogGpO7aGHauzQa9hJz9CRpzB/GnYjisaFxzV48aq+1Qj23raqbnA8Hfwak47F7NZxV86D1xmrYGMK3ubbVtDaq/mx'
    'CGeGl16E6TnWVvCab+rN10EG6szwunGaJj1OxcMQt7abzb2ddw0H4OzjTfojiT901dnefbv3tukMWcHTLjH5sHohRXAysN7sYQ6t'
    'ZrBTbzUOMmOdDivSIeUUrNbrRtDY3arOPhHsuVlWmqfW8EZpiMN+Fw7Kqimq30XROSSVQjU4IGJLSZTF3YNrgIj7gOi+QY/kZlhy'
    'zWTIj5c9JqXVdr53J6yJcDhK38ej82JhvlDKOqab7ZSE/zWxUp20rWoc7qW78T10X8tOEFi/VeNgDFL9DVvy8VJmHxx2tm8Bxmj8'
    'Ze4bh/m3SkvPZF2VgXdchGTdzRAaro8aGpP8iVO5v0+GXTa8z/r+/PAf/4+gyV0yE4OKH9UI4+LuQzlY0goJwz300YRPVU48GgUx'
    'fZN0w57iOpqHVZlzy+zDbunpATRU2coFFnaFg6nSR16XflQrWREkm0c2py19vUFxkqc2TEbpQo7rUWhzK8dRAgBp+8jGiQa/iqRN'
    'rgw3UYbMcDdJq9WNL/XGCAV57MprkXsIbwv2u+yLNj560Um6NjEj1lG0ZDIuIdXTGgweBagQMLyE7OwitLLT9Id2dggvP9crAQdg'
    'lXbYPeMFxs9ffUppKd1Rqjv+OS1pLFWEZSU7gF6DfiUv8xRWc42aupx0iiek+NWnOJNoys0xRYA/6AWPlAwV+93N87jXLQKGhTaa'
    'DVPdqXYvsbPkIR0X8vwShOvC0uB6Vfs2rAyugwXltKAlsZtoVKUjGGon2lEPZp8tZAo5DmJRxkdGe4z/wV4y7rJz8R17/IaRlA7I'
    '1CAuBxz+wHxmOWwaO5JNAW50O46eUW1+9y3tfnSlFwJyFd9z0AlgMRswKDsFEq6xWSFhVkYNyZCaHhjF56IgCs5VMdmXBe1kdC4k'
    'AJQHaK8E0WLpCW4bzu2xhJvdtR3wLQXxAu3gqSjfcM3jifmsGmhhdUIrPkucbZfP+1ISuSVM585DO/Fhj5OgkTN5mh25cnLwekS3'
    'LUZKYwFUpcjiucM7ciPWTaLbzyA5nl2zZ8xKX6oaURLXnLJW/izO1AeN+lalvrP3disotlrN0p/BofrPSSM4de5a9Zc7DZpBsv3Y'
    'DWEFhr3KZYJxa2EymYegoaYJ2hDwR776oAR2fxHYEnrVd4QA9GdO+mEa/PwU4G/CQRqcDmPgS3DUwrvXlMxpyJw94vDgQXIavInR'
    'fis5HQUNFBf7ERKHmn+shbBOh+EZOf6iVIq6meJ5fHYeAYDfjsNePLoJTuNhCqwag4OjFX3AmTfO2eyiVFUarNbByX7joLm3W9cJ'
    'GgD4LrVYIQhwBIw+BiFGSEtromt7fQrrU1S0W+L+peiN9z7uLy7MLy6icxy0D5tjAj9g98GW4w63McAYd7VgobpSWawuBUOMFxEU'
    'F6sLeFdPuY5K5QDtnerd39Rge+2NYrx2GpK7XzJAPI1TeEwHEcZMjUYYIEXHd4ctaRjr8PeIMnhTt29UcJXCZi+C3v3zfw5eqUnR'
    '389o64ASmDKABdKAkgi0u6iiUH2Hzj4RfYTHhTKhC4MpY3MKSYWyarzwq6jfv7Fv6RH+NsOLsD86xxJ/HQ/DwrEIVR8UzsamX2oo'
    '39g3eijvw+EFjgQO4Xg7Rhp6jJctxnIhx2ISRph5eL4kxgKPz+xYoD3baWq8cHADxxLzDp/gz1Z4GWMo4jcc8Lnei669sfyGRyzG'
    '8iv7Ro/lJQWKxtEo4jKDzZ+XaOFZeyV05mXFnZfHdiwTp2Aopguf4M+3IYdyfhejg2XsT0wXhps6g9myb/RgtqJogEOpj0fnAAOj'
    'jVyy9jJ/YpbD59GzUE7MyhN3YsRgqD3bbdU8IBAE3ETMj3pBRfpxhHGif6UCyLfOk4sw9UYWXVx4q6dh34hpGsXpOVHdME4HVk2X'
    'P03d5XBl+bEzTY/dka3YkTWTvlw/9Ah/sRv2LXeq8Dr8HQ3pWwCF1Jdk19CQCFQO6MC+yRnQQdQLr6Nuhh84UwVUdxotOGvIm6on'
    'dkC5C+abKBkC27Nri57hx14PqASjde9EkTeUsB967KBu3+ihNJFFwzga1wOMX69JbsoSev7k6YKcG0x3K5fQkmBtfcnZsPEC7Avn'
    'Ua8nhqLfEB8Axk/UV7/Ews1xCqN3R5WOotNTnhE1qqZ9YyYo6XVxVFtDYJgjk2Rk4gR1nz85fXLqrKUVd4IEw1btCZrTHShsngN9'
    'w6ZzDvuN+SxeEssbwd6KAdcPgIQwZvurIYazd6fuMjN1l9mpu0jwsArD3B8mpzh5GU7uTN2TTnulveQsq4XJu9KlnDqajd2w3xEM'
    'kR4lzwMWAZ2geYuHsTeiNib6cFjgS/tGj+ibIRwEeyDywJiaUQikoFdW/rSFK8+6T5460+btTYIYqT3J6aj5QmMYdwSjGFK0/1/F'
    'GKD/IOwNMJvBNyB3JT4d9lHSodQCekC79o0eEMhHIxTJcIFdRn1xP2EG1JcDMtlj8qeIyXLKZjuBzRteThut2naPRRqag4jujYJQ'
    'S82UbLGPpi4gJAZNEJ06582bPqaziFOWr4ttFCKBUuMeBm8sCcuAoYJHBYsKJKZLtFom3c6aFCxZrUGxxAfa2sbWNooc9cpcULiB'
    'yECMxeChlNagmro930DtAPUKLxCVH426A0KRcTFHcFWihSNdp0HxPTWQBiTAluh01hZStQixS9XWsF86xNOlzjl5We2BOIu2SPzL'
    '0SGhTh4+sXHxJcUKtGG0Cr5YXaDxTCg24SOL74WSybyt8bBUC+og/DT6Zz3c52jMNsZRPzua+0fiwH9cs8cNpLReT/hXYBwqOGEw'
    '4pRGONjQiKzRdJehF/YT9Ei/BlAmktbLJAG5vc9GvhhvtqjMctWRCI8GipaquKi0YkwUHQAILEa98s3EzmO8AMEiTLgKEYRkR+Vm'
    'Ua6b9lVy0psLwBrSht8i0B9jcAfNymGzJgceVc5di0FxwLFVGWclq7XmF8qiMeqrH4A0x8jRC36HEA+isMtxRX425+kHxpivF1H3'
    '2faCzfdUxEy626SMUSEcErv+WzIV1ME1D4/LfAN6+AkVmlrFGfXu0LdlkJiCQbBAyWnGw83zUEUU5TicfLav2diZeKo3HA47Z7Q2'
    'mFHkTtXhnYXSuyu2GWPhvn6NTYgNCacbJsp0B3YRfDfGTE41E+0UVguui0vNDT9pGpmddaob9DY6/lD046J77f150dgnxmM/dGJi'
    'Y1iwNfluxjDsuRFuZonNnI3OPOkG30bBLmE3jU7coZaM35AaJVSwRglGm+ejFPhU3w9lbq+x0QyAaFZ1R3NCGnGvmhfiVUdDpqAL'
    'ulw2niuafhwWCscbW0clePHVfFwObLTWktdeX+RLhg5TJOS+b8dAY6Gb7r4Na0838dppRdtnUExzXhpWrUfBHirDpB33ke1Ds/2Q'
    'gj+zaIUoCKFenU3APcJEnw1tNyFx7RpX9KJ93VqQkVRooEpW4SYZtRcFB8pp5MCZFcqp8QnD1NYxBqgvB6exzW9NQ7BX451z927c'
    '0Et4Gm2iiQgIpK9HFz0o6BDrQ0KBYDuHXONYOhLjFCgER8HF/KnjYRcHvwyWqNMLbrz3SZDJ7sOi5PACIcg3amM/xpzaAt5FbEOW'
    'e5G57m3QnYXDU2zSfTeh0VO30RxHaGUCh+JOUZqhP8znoxZH4v7th//tfwow2nsF6JzLByDH9xO5p8e8voP2EMRO4HdwUFhe8O7l'
    'dM8sIwg0lUsmvWoLwbbFd2EL4qUKI2ZN9nVh2iS1c4oKtToachyyt9sO4BOMwFN0MJQMrJGg04wAN7GdSbtSB3P59ZymaaOT6Rum'
    'R0IbDStDju6d2SScAGjaWkaWL01AAg+ZxuEShRi4mxaCdg47eGN/6eFiIh5AIIQRarvMgFeH/I8PjzntRHiq7xrchBEOI6zvcder'
    'MK0bCrLj/ex5RNp0CVOJVObqltFm2jNI08QncfHpj0gEwhZWNT1hzinUux7b+ppYqJn4DfSJF81qlmP8yz/++/9TiuaY3gstR5At'
    'PH6yYGOHu8zhgZvvIZA9ONQdc1OQsGTExnskE2lDwNYQj28qMV2gEiCWg/RjPLDyC3yPOG8uhlqMeqc5CSuEMOKO3k63sR38LLHE'
    'MYiGgVlW7lJJloHC8Jo4jrhP214voDzAOX3n/MB2tVIj+eA1+u3Rij3m+0rBkA6SjyDckZj5JzgtaWFDdUPgfHWGJCOmFv8wO6aY'
    'r/b2buuoCrM0fwaTtI2YjZMh+vPmlm58J0o3ru8pzbDnnUq6iSDFdKTBPTAOKz/8/u9++P3fH1PdSQ2lj+hz4NHYXQ6K0He6z8lW'
    'UcmSRVUOUf/6qHh7VPqK2pihCWHZPBv82nTID7nujyTn1/EZJ301TIF4zJ9SBfCvsPcTlqNexnpXFvVKwrk06fWAPBPK2vYpaEfn'
    '4WVMOuCUtPqYoBzzscILWGiUikN5u0uEqwCwg2Fyhpc3PznNjNhGBhSK+U04Oq/Swa1YNNvgPL++CK+Li+XsjhhUgkU4On4dLP7/'
    '5L1bcxxJlib2Xr/CC1PTmTmVmQRAsqoa4GVAIEliGgS4AFjsWhatGEBGAjHMzMiJiASIZkHWD5JM+7Ij25ZmJLORrelBs7Zmo1ft'
    '2prpZfaf1B/Q/gSd7xx3D/e4ZAZY7Oqa7p7pJjLCwy/Hj5+bn4vlarrLk4XegAR/A5ierdIpaD476dDXOiHkZTTMoCBhhp+r1p+3'
    '6sC8Mo0vhc3Rnq4ocdH9A4FTBl+8eppuz0zXXT1/6xcrySnKMArG8dk85MomLhN2dTtHtbQc2uiX3jebhU9m0dAqJCVFTb5hM2Ru'
    'zCr1INbhZZcG0dAZmxfsu3aLt7TnSPzZe/T9UJJBfv99SxyLA2TU6LSuVx788Pd/q52nlfap9pZ6rbw+41lwGmVXG/27rk/y6uzd'
    '5sqD9mfvDbRkSFiMJcVtxyR0tElmimrussXkA/OUc9thqWdXJMyRffs8RuVgcSL6+dp2jbRijacGraxRtEpqaYDdN8Ztq7jVIbR7'
    'ckrTrfuouEv51GRn7tffspXo1/OQSKE2HKMAfDy8Uj839iDT2wlHN7kRlAqUHk/AvenXgSRFyTvt83M0e/gQ5nD3E327qoqf2Ofu'
    'J9ALOCWRrgeWkmwJiWd8RX/gQmdTeWJfCl/yeE5jj0htI3WonWYBUe5hlOgq0KMwHHcK+tYh2A0TyoK8rR6ym4/aUHVipuLJokVh'
    'mensre7W8OFJNG2v91e7Oftd7d/VDJgL7/2Fhc1f2Gl1yuhlLkhZcZklIdjuKdwRpmc/PXu0wu93WaInFqVhWx6LP7pZgb5OmO5I'
    'egpdvtM5z6Kxo+hYpWGmSja+1uUgGT4IVuudXPVQN1NNEETUDtbWrjoeYYpHCg+53k+LBKOQMD4cMoHC8z4+toJ1TkpoeUfg7bhg'
    'fek20dF3ZsFMLbpm97t6ucutA9qGZhIiFTwAXuAtDDYasCZGD48Fd+RTPaz71p7E+/awuq8v4vF8IshvERig4nV0bCMhgfyvhre8'
    'obVNh4VarOpHbuknTr08O0qSxOAM7fCiNFJ40ZfXvKVsQUjmM85rVBioMK9O3chF0+Z9mccig1qfJb82tzP2ums3Y4h6sfsvqOpT'
    'gzo9roHSdTQZB1ePsukyTYFaIeNzy4k4wm33PF2mY0irPMZRj+caAO0NtId/9qFFwk9s/mz0UAiVbf3wt/9Zqedoa4Vi03JBRXW/'
    'fOGNx/y7/0fBOYhW/0GDNun+Ob1zLJkLxqmqp557RvBlI29GR29dYbjiNvDXD8tQQdZghjNRYfh/Cqf/4bf/qC1CG2x89sIDIYuN'
    'SNM837oIMtIbYNE8SIxDWFfVukB9sP+Te3ngeQggHDbgWeQVFp25iMzw3XdWTP7uu5Zvvac3h35IrV/GjI0m9nPEzyo8QTLBngzs'
    'KpvSW45o8lur3nnSfit8ifoFRXx93aKC/xFHQWxzs9JHd+60CkWgTmO+L5ceCiuBQtTyBHk07/BHejTp2R3GwToXyZHA0hq97Qa4'
    '+gQL/SAZ8rYH4hGOe8jR6u9ROTsgZwZUSA3oZSC7WECbZEQ369hFvgvBRcUOLNiAvL0D/GL7u3eLsJ9GNCU4i11U4VBw0UMLUsnS'
    'wibwdx39fZONKJ9G3KQjoajHC1x/lEU0nXG5ELpeckthtpzTDpPtN39SvHF1XQ+8hr4DwidOMl2jtcUzLj1a9J48mGVFCgIvjplx'
    'L3xzTz6UQpKoVWbtDkReOtcr6rP3+ItoQj4be7QftlLeL6KDyMT5wP0aFosOqvX8TrmPTSUZGfYBIujzyhR5nS/xXfAvvHJHnnLA'
    'tw5Pp53h8l4cx53fMBmlXo0Yj809uTj/SIh3Gk9Cpx3Cldxgb+WFtlZQ1E/qiWNdvgFNcbyEAwa1QDOLRNRJ6knPnzd1j63YN1aL'
    'nc9erUnZbz2jcoqDAowdSl5dXiWfn66csr5eLLVSanLnTl5epdL4VvrCtZvdYbvZf/v3v/s7N3+BW9uiYgnRdBRX1hYyDaTQjmMg'
    'qyl3Y9qn85MV5xQ4M9bH4Z//k6p87RZYajJz1msccEkZOxRg8bAmRaaG/FP+Sh7GU6mrjOfiAGVX2XYKpHh1rqqoyE0oiLPeaPgR'
    'aEe5pA3tPXdaKmdSQzta/js3E4UWS0p5bEuVLJbZ2N3NcOUeCKE2Qr3ikIpKptZWLcXfiS4iOkKWCgAvGtAZ+qOayAylv5ZpVDYZ'
    'P7ACS6ocm7RHnX2LdDUwqfc8ibcly3BT+qTop4ZsRQUI1zqoOVcGPr+scvGquDRwpGzV7MqgSDhXPU8II6xwNl+Myok4aC9wGYwT'
    'c4kOL5Es26KurQqy3vETuW/WCYdGJNRDVIuCIgl+lCQ4Dk9y8uAYL9hT3wBu96Y2V84CVqLpl5Z+P3svy/aLR1Wxm1ziq2A0zsu7'
    'dzfryrT50uZK1cVPXgTss/em4XXDemiVHGcRz9EXSATORXVZXb5joEd/O6B74N8kVfIhflHiQA1W43OhnA9VchwuiAtscXkE1icz'
    'r95tXfKryKvkQoP5lIuHTmmvbqsCkVr81AOQV3UXTM4RnN1CaS5fKdSzrSZ5ksnIXgnAbUaAIyQ/GIEC7hw8I6KRholNkVbFaHLP'
    '7nFTdU6zmJB0JPofy2ZmxnXVMBZxUXV1Ix/EJgzBMVB0te6KvwiUvsVCaJIOXXCpgjziEReRaWn2WjlWjc2Pbw6xyvECcJpFuua+'
    '+cki+M/dzOrQpdX7SjW6Soturj83UZXrFeLcDjY/6WBBBQvYm5uRizdF3IGp7rnj07rYzfmGDs5lh2a7nKLlju3ovtWuXfiMTuVg'
    'ms6T0ATsIVVfOPzEu0VNawMF3WCXHEXOYueeKJ+A9v3elEsCBop079Ykyg//WcwZlfi2SHumnsVi7792oX0kDtOqMBY7hKprP9zS'
    'eOE6LY1rbqEt0SpcybS1Nchpj2ub+4qTxD4maGXtC2fp45PxElEY3/eoWW4zoR8dfFjAQm8EkooeR+/CYXuNy138178X0+onf0I5'
    'fra2twdHR7uPdvd2j79Rzw52XuwN/kRy9mhSjftPCc6Dzm/j1lo62W9Lx93Z34qE/XH4Dmlg2Qd9OD8Nn8USCefF7tlb0cLzIzjJ'
    'TM82EDbHKWTsEPonRkh0agceDU4xLZ7g6TzdiSYbfqBgMh/nsXX5Y06iyPe0G+7jeXSE+jq6fSud2MBwTIF+YsiJHvmM/3k3xuje'
    'ZbBZk/nQ8Qa/dG+ez80HPz7XNHbKt9VyNmm/2oZULyhknK7IL+2EqgTIKesFi7gZpWVq74EbXXezu94Wd52N7Zpt6vLGdPN96GrY'
    'dz1QXmt3nM0mGawZCKXs1b/X6dUnxNaQ8yDlyTEo0rxZ8Nh4TFNVP2PHLpPef4/PuHGVAoDl+kqffV2/xSoJ2Bhe2v3824e2tb63'
    '05AYTHFakDGbT41u/SSOz+gXd0L79RZl4cwXO1ckLsHHZnxFUj0Q/pZcSJqPWSzjwovOIvYGvx7s73z34pAtUudZNks3bt3CUkjG'
    '4NGCGZzK4smt0zRdfziiMcZX96XLjUva/L+8vbq6SYLR5l367xerq78wFczTy2DWyoMEx+/2MOMFTFoA0WO7Klbn2qsMwPI7Ihhz'
    'OEcUO/VI7aWI4JLFnKHLWW5XkSAqJgckU3WjC/Wkvv9eT4+kkrH4ReSftzqFmn3StJN/wte+JWfSdIHFw10e616sP6gyCDbpVcKa'
    'lzsjPEUhLHqcb2Demx31nGVSRy9Mi7VS/XvwfHXwAXBAcn8BSGrBIIk7MuRM83bIKcBd9J69Achm9SCbGZDpYfkRB7fKGlpuL+Z0'
    'fhA8Z50qR8ickgml/Xk6vueEyeUK1v/Zf0h0aq1AovQScYNIhy4ep+pnuDSPx7nhZPnD4tL8jzVLVMr92Dxkq65IZMVvDQtV2tVM'
    'swj3YT1MtU+HCqLhHxqqRVSBQGANVgZVvIf18MzlCOdj/2E9TF7sqhSih/rZHiMtG/mwMQ+BKiQ5O8GieVZhLVOGGSp2dmGjc+OQ'
    'uXYmvAmNJ2JRJBUbH8r0EYyIhOvbeMUZ9WHHQP58iZKFCIKWTpRsqaLA1il7x55EyBP0PJiGJq8++3s6JQWKndUXGaKGN64iUDuN'
    'Gw+zsIyAuwjuHprKOfWaezNk/BNJPVpDSQjJhIP+herSgwU2CVL8TsMZJxpDfqbeyXgetl47nhVzz6/D/KGXgNVsZSSun8wzmivb'
    'q3lgyY0kI7MBk2eTVxXOLbWLAcPf8dVN5kFH6mRZr7WuEiGWZuvkwiegQOi0ux6eAWa655GUYWH0wN82lRL37MBRfmtVmhRLmRc/'
    'pX3jMEHonNyRp6mUm4MKn5OqvWHQ0tNlyu2Z8g6jCX2g56k1nHJTpmY8ET0T1oHK7diD1WnnaEnlxtCX3Pl6+lP3E+3A62R2ehUN'
    'mRK8RnqnYr1kAWTHV6sW2ucj19UKhnmED56Hp2851v7TTzVxMSmcwNNTYXLVe65fmm13mKLZfUOva77HK/O1ppGVR1N/Bev1bBtI'
    '29UZkr42VHJR/CTQPf80D6E8yab5uTnxvDhL5wGvDYm/CMZOjUVMoeoWQyaeMRlpa6f4NP9dQTy9jFaG+wtb/Rfp9rygVNzOwTNt'
    'a91jk7etGqeJ7y7rrnrxoaCwJSHytMFNMjfUGgIjnJxqj03B9ODfmqGNdRU45LFG8XiMPHqTeE6K0jfu9+W1cSMwGywqdC7RWNnM'
    'qYmfWkPmKrcmyAgNt31QE+r6G0SX3mHT8+xdq1CPHPRGX1jAgIeAlnEoNj0klw6mV9rJjG2Ki2duC/hVzzqnbf7UvVQNNPsgOWM5'
    'j/g3rlX8DFdOEi0pQVXuSeewalaHiitl1F3vuH3X3KH4KT3cuJIlQSWcQasUUnK/GNJkwkCWX+F4+fnq0xMuDzW5ScCFRSScQ6Jo'
    'jrgFfX2UFkW+a6+kqx8+ZI24zMMcU+9PnZueK/uSkBFNkU/e3h6ZtCfIg3mZIH99SHyADdFSQA2OFF0Jn07l8ckV/+s57t4kpinR'
    'AU3bOvWJe1ONjlObjUI76nD2hk45O6S5yMQ3zpVd3nMp6wGCu2iRehjUVqbV4Y80GoacOx93/3xsixQW1a2jaTDWjjM6JwDpZfov'
    'x63GaGlsNdLtFoaFlbu4L1Nk96T2pU4Rpi0qb4ouMmiqPTkuI/hsROxhcmncYMTJxzg3qVbH+svC/nhpk5PZDeXdxk4W8uEU42GI'
    'ztDXD8xki5lwHDuXgR67ZQhYrV1NFo+dq4KDC/dNm8jL2+PKmDg9gXJuC8bdwuDLovbMxKozUeAjJw1FsdyZ2DGLzlv8EfGvdsSC'
    'E8GRVHylX/TOx6Ls52Y0L+fHDWgyb82ry+h1FWFObJBfEwJaGapHM0dInIMym7VBd0u/yDHsRwTMQah0+vZlyF+FVydxkCB7z0Uk'
    'dY5/huF0n3BCnxGXNJLalY+hl9nUaPp1MA3OwiG3sq9yspyOdtOvI2JdJLWHY8fzg/AdWWTH/fNoOAyn+oevZ6O8Rk/etzomac0c'
    'SnexpqUJuiMpTdKF4mRSH8MjPMLIm3keWxHm9E2IXChM46nE9cu7i8gyW36t52ASKn/6KfXYj0cj0htecgYQmb08eRryUbcL2mZh'
    '8ZCOK4QJTZ98nSQdPQkzVJIuV0pkkwnbN/r9/iJtihv2UJGeVtXtpyOxtnT72uhiMxs7W+JCRQZ6Jf846VP81L7OlHmujBI4MG3+'
    '0Ktyhxnz0/J0RQeXsn8b0zhrv9KXacPXnW40pa0rPRUfudJjiHsB6RmlF8ErXBq87r7S1D4cRnyywa3m4Qq9oJ90msN3r+Vb8/P+'
    'Sm9t5XUHV+Z1QPMBMZieg8p5NrF2EsfZfbNfS2xjmFqc9LAMGMdS7xAkMevirUkQ6XizD+uHDxMnU0NvR6J7EGF+C2tBuKRniCac'
    'B6dudjkl+9Ce/Pk9T2LWNPel3zhZ0i31coKx6+aHOxCbyOfGvVTC7jSeTILpMNXe1DZh9BOYNFJd50ipV0tG69En1Af1288ftF53'
    'l3xMjXg9+I4/+EQXJrYzyGWBV2xl6Wo30xhZRXw1kt/7ahk/qgMmnSMb4Gaals64GS0XSug7VyKhn/UDOBXJS814O2yMSNeU00TD'
    '3FSkfW/TPOS3U0heS83Pg9Tp11AA1F/EW/rvLn7niSSvXe0MR7y07Id9aNaC5DRHphE9XE2GSReqfY92tIeqh93+ZfQbQqopzEm9'
    'UxIHuv3k5JUunvq62z8Jg4yf16SfFmNhfyI6VVtT024g9FPTS0sf80rQmzqtZQ3spRvPIAAuXQsopLQuwcl8dlZ3jFCcgD9FNdhO'
    'eTbeibPtcpt3LezN9HNrolSp9RFeHi6Znm6kp6h/LZim177BVGtSjA/D0xgysZAZWHs9zrKkz2ViQE4V5LnijSwSBGHbZ2UEoQ2X'
    'd9XII2GSBnmqWjLEZC5dI855RiZAD1mey4IDIKaX0+NmelH6x/la93y9e37bRV29d++9c49nCEBT5i94N1PPMnnprYdADgLMtU15'
    'VbsY3n6SOU7g2GU7L+VPqISpi3L5NBcPxSzoLbMgH9zXxf2rP7Ty3jm3vbUqW3k6ghU8F/TauoDqfciDJSkVJpOCIGssEPKezpT8'
    'AaHaVx1sXdkqfcMpvtvOzaRM1TVP5B492zFpsjVNpdqHKQFfVGB4gl4OdiPh8vIqhV5p3rYtdT0MeSm3We33MNvBrHvE+Rs3OIWy'
    '4SdFLGFNpBI+2tKuLRr3K+BVs648nfUClc46Zkr/D/sRSi5Mmc92zKhNFgQs+tBrhhqB2o22QHbdBTkm6CyjieOnhp8PF1jWeSE5'
    'DeSffb2+HXEc9k3RYkxHZm0AI+RQfez54koVD8tTdVkAOmgm3BtLBSbxsG5DWDt2RJaKKKLSASd5ctVYkxvcSHhwK5YAFygWrx20'
    'mPIKLOP+ivwibUyra24OHbGIGgSu7m0pv3OCeoSmWXLysECLteSlr/RbeZV5/ygh/447M/y+1X64AQeG73le3yN25ftzavG93GJ8'
    'T5IeyXGdW1E/w6xlJp5AtjCQeBF1dehrp+7ouFSqjqRrjxPZ/S4f5iU48Da8QrXXaixgv4u4bt8gqRQRQP8mnrTyupA6Ax3Rnug/'
    'P0zileRamArNW2xJA8mNC0ON/0JZF8olhICnw1jTLhJy87ZKhtKmLFJygD3FaW0lSXy5F46yqqnxy0P2cCl4GECN1GYiM7Zk9zM+'
    'LGWbkQ/yWgNRfh5FVsBIff5xMDLrdL2BudkD0gU4USYaa2vSA7WWCzmLQGvD2MNxFlgcqgICUhYSRxfxxclDJFeVGPyVntDnurfP'
    '3Sl11J+7P23mTHyvyWrHe+Zstk0fo2/ejnGpw9+4dzlZPJvEuG8UgGqRrd/sYDkXvoy/DAK2SB5DQy7FLcaGNiwQxT61jcrfL5R1'
    '8u9sV7a9BWepR67ufF+5slFXjYPCw2JHbHi0x7afnkej7FfhlXsTVCPdAUF4UNzlhGX84rHt1pZTMS3pGl/X9SypYfyuLXYM0tNg'
    'For3XGqxAjAV8v5jEUL6r8CJRqJ5ocIRJil57yrVMGOk+Iv7K9wU1Dt/tF1+JGzQ0HWdWkwP0rHDeZRUAPcnFMl3vHu8N1DPt54M'
    '1PHg2fO9reOBerK1tzc4/OZPKqBv++DrweF3BgSmXrwunHp5Fjh1UHXt1JdPttRRFkyHsJU5hXxJt52niMdK9Ut2MEBK/CQcdtV2'
    'PE8iFB2ZSqHVll9z9uS0PNKjR9tKzDKFos5g171gHJ1N0bMp8XySkHaDdAjwuyCpxR9hEk2jiS07rkd45j0sVJEnhTyYpr00TKJR'
    'F6XKwiQmbnN5HmXiERj6I4A3k2JBmsg4rzS77T10RhjMEyJHJrkSw0qMMUSsuuoEVZG1XZP9UaaF5UzjKMmnrQd7HI0nat99YwqW'
    'B8lblUe+d5XnravOMBoy3LYK9ZvnwyguVDc+8h66IIuTGVvSlNhfaTza7bGzVUTOr0jkbjnVbKUwjfYtyMLJbMxVEuhrkhM0in53'
    'Cn3jeAay+v56Uy75YUwZck1G89XusOC8faxfPAnGYyKo3j1fNhtzGhfb9ytHcZQUNUD+TVMIMjGTXOJkSf0Wjcinjn6xyLfyNK9n'
    'OBPPSp6ko0/W307QqGeyyhv7lldD6UOHWuRfjmeP+WSi9t8xwmTMnlROBEvGN8+TeDjnLp7OT9otghC+14kIS5pc7cxn5z2hCz2D'
    'MSlfPdUW+CjW92ixIxqqe2i9zXVzRQiCWUFbNo6XVoNgenM1fm3ha0TrQYRFlXjFX6kZ6cGOjnfh+3v6YsKbPjfoXdAqXkmKF/4t'
    'KV2cwa9XXivdFv2/saIJP+vIOD4umuMCyQfHAn4rcFbRa/gkj7qYkUghR1/b51PVlns2ubdSc8hjo2SGDL69WULUlzgG/OR0uogl'
    '5+s0O5Hcv/mFg+O8XHG8CkNhM5eeM7MYjecKB5rWgZoiujuHaOeV8fyROj+OUuiwWlucrYY6bNbSlfLCTW+dzeXEyGubu0cia1zE'
    'uqkXc/2JG59u8s9csDu9E1teG6ouyEjrSbU16P21EV25m9qjo+ojv50+S/Hf3GlHmxDcSO2FpChPkfLmh3/4X5Rpw0c/Qj3iz94X'
    'hClxZc3uP8h04k7GM6khcv2mq9Y5hYrk0PiTEbwP9gc9iN2H6slgf3C4dXxw+CcicHuM8GAaPiecTfJIq+dJ2BtF4zERkniS1+oT'
    '+TfV5B9EoMQRYFL5jr2w6PcOtSjVa8590zmf7fICz/oQX03jGR14CErhuwzZAo/0I3ajTP22e/GZdn+v90e5mvbG0gzMl9NhPdQu'
    '7bkh2PZ4lE9gYZdmorV9ghPHM5RhJtFE7hxZhBVmJ4K3ksYSk5I3DubZecwStTSW3zWN2Q3iVHLH5Z/op2uLvwknQQQlwfvm9uJv'
    'ZudwpSt8c6fum9lVItF62naHb/hJusbrefPP/5GoGHxLdyDGdADrx/Px+JswIES9pnceCHiU61yAyFGg445r9rvr4Ij7jd1k6s9s'
    'pNeB3d2uqmtudljndl8ShEkwg+iTNBCWq0/tYzqi9iTooKarKdSEnSjJHNk1P+Z+Z8xmCjTgg6a7MKBTQKij51z1p0l8nBMdZ7LW'
    'cWRcYYQnPILnidhe0LM+nxpDbTCLOOwOhMawGCymzP/u9uqqdt1H9RWdGQvm5gD1eiyBGibBKHPmVaRWTkrw97Vpwj3qI2Pt6VTh'
    'xs7fpH69SN9Qp++vSC9s7//Elm63RQvLYT2VIQ9+nIQzsdy93w+bMJlM1dr6qut0Kj779iO4ortu/CxW0icQ71FDwbijy+aw4d7l'
    'Mhw8AlW9zX6N6jKiLtgIj7uRmOM0SYWBl/a04+Q1K3Er1uXzjdGldriXilI7pXnY7Su90T1v+h17a5AK7npuuatzTS/6LQpZFY6B'
    'JTyukUGzFY6A10clZz8dzXBe7LMtcsfFPc1iih9qVtRRRVYpim35A20I0x88DlFlKVQwEzkfn4XTpGqa/NxO0/lAE/TSB5axV3By'
    'OaaFD3K2XfziJIrzxArOF/S83PiUYyzKjT1mXAba6QAMt/4z4cfl0Z6D59Z/Jiy5/JnhvqXPDFcGpB15RaeBOVsk+9D3uBghlZ91'
    'eecid3bmFT/QaDJhuQ/0TDCjK5v/ukh1DI345/+ktL/t7GxJNnpM5awnpsqVBzVZ06WRjG1T6+pZ+VnXSx/xobHfiKfZ4i/ktKw8'
    'eJlERIOmCGLTX8ubJZ/rpNzeWj57b3D/oXpT/kS/XHmwogfSDzrXKzpRLZPUa92XPRYPK5MyS5+uU+vKA8PQajMCy0dwybKwskLS'
    'ddUkcNKaj791Es+FPwOqYbJsHlFsp0F/V82g/JE5SEl8aVMCk+Qph7wS7uaL03hM2yX50uWRDoe7R8p/PD2zyZw5BS5i5eRxeVY8'
    'otCHpiNy65rx+N3yAYWyNB2QW9cMyO8WDuhhdU6cagbXr/N02OZJeUsLqWjDd7M4yYyo+3zncQWLrOSOoIT0WY+/cwjp7ExI78ci'
    'ipfRNA9MhhjdbsHn87uTcWD82ehlHgx0CcRvv7n36c7B9vE3zwfqPJuMH9zT/0unRBOUSUjiBafUD7P7K/Ns1PtKo/M9XmKBlLEx'
    '0a733i1pI+3Z2miOwl9GE0BUzROSOxtnqeMC65Kk7o4kp9v8kv77y2KSOut/8RfqvTqJ36GqB6ff1Mnc6dGmmgTJWTTdUKsooTkc'
    '8vvVPFKTHULfc4LQngy/oSu8t7qtp+H4ggtgtrr59dqmczm1of5sNKInkvFd/dna2lre9V9iR5GjF7VG1NYdBVAkQZR5kzKt+9La'
    'hmRy/egNtb62OpnQBxGomqTnXP/ll/QoT4VmVnV3ffZO3f0C/0N/0XJjqeG+oZByFDaT/KObrNfLlEYTdbknLS8fhkTaeDzPwk3c'
    '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'
    'TRHt06QpCnDHjRGAWzfffpn17+10co7EP8D+sKemvz9ZuGR3Pr9zR3355eqqWuX/NN0eHqrx9nDr5tuTheMfdyi/FkfDjyjJ7iTB'
    'KPtJxdghRmwoxD7mzAo8x2ZyK3dO2+d82GogxPJnNxdhXbnTNQruBxfRmUSa/ku2CVrj5xSRVRFqftyHhca9goEnrLpvne03fcd7'
    'e7kiih4brNUwztLFd0t/5t7bqL4xmzv3TOE4d3fV3u40HDu5704zem3daFLr6lrhdoNczhyrkKp7arqopXXQSfkaX9peL7skq1kI'
    'LldutBgpip7pWzcNi4oVQq7XrsPwV8eicFPywz/8DnchqZmztycs099K5ye5S890FOubbHvz8mraW3vt+H/io8HSW8n8VsT1I6Ox'
    'BuPlbpvmViS/YNOjdszwhfVi3mJnMB/wSB2JQCk0V+YDemUgsiVIru359AzBMW069Sq6v7aponv3gdtZnAVj+vX55x1/0/hepn5R'
    'b/K7h8/eR9dvnNCKT/lxh5XOaDp3ohIijW42vJxbVlywIp67B/90E7LBK6LeriRhjkpjZds4STBxg41S0/oeG//h9MNpJtCgJo8T'
    'kvn1tfaid8Wp8W2uPjidjp7WtTidL1uO+cysBbDQNEj94hcq4vNaPWIFJHjIxpC7ZkdT4+faS8TXnWnXuvqFuoMQiiQc4ZwjWSEn'
    'FRKTOELXjGMwb9w6bVzjO3x9N0bTUDB5jfly3L2jc+29mzzNfKQ7Nx/pToOR7shI1uk3Q7wWCiSJ0UD4sL/mNYOsNeEJOQ1pRj6Y'
    'WfuYkEUd9nQSbq35T25m3MQrE+igrr1RT5aO6tnZ/HFPaNyTilG1EUyjj3bvUIUdut0QLtoac98+VqpVNBq0NkoBWF2/tSNmobHy'
    'ZZ1iY6Soz9v68W2Ftlontc2LymqhuaNb+fPgF4XGjqDvN+YXhcYSiFUBD3lhWl+bDWRiLiB+BQ9E2sXXyApycMI3fsiMEYVpW8Df'
    '6Tjgb3CstNNNjir6UBlUoX/N++sSltQISRvKCJ0I4yMm3rXk5r6uP6p0vE4HVdc4dtq8aeC986NlKmlFUxVfoir/+Vzccbgd/Xb9'
    'ZDDTrInsUiObWSixePYhglyhreYM/X5/K0mCqz6ubNtuC7ijIp99+xQgO1WfwrPTghQMSj/Lp+Y8tCwxlyGdy5Dgoj21MhoczSTo'
    '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'
    'vH3NWhhq6anT0oUoYqilLT05NUtbIaNNSZeW0tTR5Jz2YJZxTkh3o9r0GDiMBQcsBS4DRqIPPe4JL+IoQjhMib3APKnSefXBHk4Z'
    'ma1YSAGM+wie4MsFRpXDGYfpBAa+g0oSmm/EVvQkoboYmh+oE6eOjg0mwjyT1F71dqOrpDPqwNnOFX5BBcqLL6JA2XR2l1akqF1o'
    'VLUvkKr9jFqVItXITLqVz1CdMOkt1Zxg8D08kilGcXxFetVzXmcT4q3svGq1z4W0L2CNMPti4cKNGRk7ypaiFDJ+pgU/9IvbNJnK'
    'cuKMVQE2LB46KtiNEeitleVNIIl7WlV+JC2RWdAmnJtD9kGmzEi0DdSoaAfmlEgJ+fXTR/JIwybh3Fnwll0TA3Ynso8s5+6dWBLX'
    '1zE3d3iSUj+aupDAQBOFDoyFM4i+jNnJtjPhrZM2BGSyvgfymmiP24nOZ6vCMvZnjnECZV1NWWah0Adz0jA8t7wZhtuFK5ZQgwil'
    'tUVp+mxtD3w3Cj1c6vn5DKpkeWHjSKPyYEz0DxKooZRtpAOPZiPDwyQP7Il3Mqb5BQIf6YYzC/TW2fccH5CwWnhGRWcN82foJmW8'
    'YG2wHNGd6K/hNKKNYNtnTWTx88kMXSsyxACGaR5X26bahBz0DcBdXvP9mp+y1tI+sdIRMk8A0zk5kllQjacanwmnm6qbZ9GrGZVa'
    '1W3x/oxvke/2OHNvXDCDfJlbLJPdX9zJRMf78yP4OcCI5msIxGHZCXemDXEeeLNt2bX7hgG4By6MM5mRgepHbbzUipsXlJ4AuLkm'
    'cD2w+/4kwh2jZoSMqokRSknAPI2HlFUNeJPROSVR8N7Hp16DB7G+v+2dkozB8b2xiej0FDVYZLmSsoH1RdQn0QE3xYiTQ5OxZFem'
    'pB8Bo5dWLc/Z4UCmKwG+itSK5KbAmI3HOJJCfK+kzS0CAa/AO72uY+dug4O8Lla0bk1Ot98e/lj9Mf2LxfMk9PxtuamEn4G6zLBL'
    'b/2lXXrranJpbnvRraS68KbV3vux2vixypV6Z2eeCh5RVPb7H6t7quynHjDBHodFKiq7sff20N/ksirtbquk6LtD73CvxmU3Rij5'
    'VYtLvl7f3PIq229v994d3h7uBVLnddSKvUfLJZUau+uNNx50IqUbnQgY3OZoWC2HfPvtu713DQf63ig1eoetzkILWsEL/7/7exfF'
    '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'
    'vLeqjqDfW8UwdPxL5yc/+f8ARU4vNbhuJAA='
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
