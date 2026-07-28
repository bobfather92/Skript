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
    'Z1bgOdaTW7lz2j7nw0YNIZY/u7kI68qdrlFwP3gbnUmk6b9km6A1fs4QWRWh5sd9WGjcKxh4wqr71tl+23e8t5crouixwVqN4zRZ'
    'fbf0Z+69jeoas7lzzxROMndX7e1Ow7GT+2CW0mvrRpNYV9cStxvkcuZYhUTdU7NVLa2DTsLX+NL26rpLsoqF4HLlRouRouipvnXT'
    'sChZIeR67ToMf3UsCjclP/z93+EuJDFz9vaEZfpbyfIkc+mZncb6JtvevLycdTZeOf6f+Kh/7a1kdivi+pHRWP3J9W6b5lYku2DT'
    'o7bM8Ln1Yt5iZzAf8EgtiUDJNVfmA3plINITJNf2fHqG4JgmnXoV3d/YVtG9+8DtNE6DCf367LOWv2l8L1O9qNfZ3cOv3kdXr53Q'
    'ik/5cYuVzmi2dKISIo1uNrycW5ZcsCKeuwP/dBOywSui3i4lYY5KYmXbOEkwcYONUtP6Hhv/4fTDSSrQoCaPFyTz62vtVe/yU+Pb'
    'XH1wWi09rStxOr9uOeYzsxbAQtMg9etfq4jPa/mIJZDgIWtD7oodTY2fa2chvu5MuzbVr9UdhFAswlOccyQr5KRCYhJH6JpxDOaN'
    '26SNq32Hr+/GaBoKJq8JX467d3SuvXebp5mNdOfmI92pMdIdGck6/aaI10KBJDEaCB/217xhkLUiPCGjIfXIBzNrHxPSqMWeTsKt'
    'Nf/JzIzbeGUCHdSVN+rJtaN6djZ/3BMa96RkVG0E0+ij3TtUbodu14SLtsbct4+VauSNBo2tQgBW22/tiFlorHxZJ98YKeqztn58'
    'W66t1klt87yymmvu6Fb+PPhFrrEj6PuN+UWusQRilcBDXpjWV2YDmZgLiF/CA5F28RWyghyc8I0fMmNEYdIU8LdaDvhrHCvtdJOh'
    'ij5UBlXo3+b9VQFLKoSkLWWEToTxERNvW3JzX9cfVTpep4Wqaxw7bd7U8N750TKVtKKpii9Rmf98Ju443I5+u34ymGlaR3apkM0s'
    'lFg8+xBBLtdWc4Zut9tbLILLLq5sm24LuKMin31zBJCN1Kfw7LQgBYPSz7KpOQ8tS8xkSOcyJHjbnFkZDY5mEvQlSeZEudKJSGch'
    'ymBLb1r6aAZS9sey91Z1mJjsnnw+zMsupXvJDNTnzMyXsy5aBVpGsx7wpO+7Q+X753V1rbboU92sk5bToR/JdiWharfX10s8x1zI'
    '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'
    'XtyYfvOotWwYBIJuHvNhp9xbyE3rrkrFL9GSCkvRuZu76nhD3SWOn+OILDTx2WrPIrJkNw6sYNGiy0TF0qla3tAj9wi0DQWk4JTW'
    'OWluJmK7XWiWY6EShcHl/IKSKNDkeIVhSMOnnwkNa4+XUhezy9/oaH1/2jtcz2N2UgkrsUTQAyjqIGHu4ulYhhsztcZRDcub4+90'
    'oG37szU5Hemr2+AuKXhMvpGy2TqRG9GrnzpzgjfNDlplzYDHoKxYzdhM3nvsxmdiptFOiukDoI1GmPuvBfeTz/SokbKWsYktgPh8'
    'qFpIagS9pjFYRahqo2QGMBuzkJHvMXTZn43JPUAUJ1T7oJeNQ7N5HxhCJxwJLvR1RlgVr+1Uq596todj2WpgWK2Ht73JErZ/lses'
    'Ht4yAkrX8IE73ZJQag35G2QQvboz7Id6PAP2Oq8U4+wsaIyPHefSZ5YufwvTxHrH0aVHuWL/hJaaZ07jh+GbfWonvn1gfjmaEjJd'
    'aSWdeKrfMmVuSaGkq6U5H/WmVcWO0Y9em5nqTvPU3Iy5OOCehx0ql1etJ8/VLNKI2yFdOMCmqmEiFOLA3g5jRLFahfe3U+wXyBxk'
    'A3jA/cy2PlJYQVp+Fro3f3ZKXCfvTiY3bmEk4cIst47Td3lukTn8p7Pe02d8DBPZwAk9vFWOWBygDC0gTAkJWmbicxKN4IihFOgH'
    'gEEHN7kXlWQsMsAwUevhZdLJwCW6rIqNyloyKwq/uEs58VHzvtvaeJKAuejVdDdbXkHQn0uOcLqwuUjxdzhuqRNPzc2FJEUCA2ci'
    'v+iy4cPHy7jjLoXcd+lYDG4mjmxqJQrWrN9Jxhr3ZSeJuv3LsZuGyfFyoCCgKBXNiuMnCP0lFjiphYVTlI3shXAzBXFnPcZr4IHg'
    'QZCxBZKSZrbVfzApC8i7WNb9cHOVdGOvht8ePaIi6AcSdwMpDv9ObVxcvqgCVXaSBAUbxTBKvwiI7MYzycJW7W+4aWqUlZsy0cCf'
    '557jXgGvFhez+Zp0bghSTrf712h6vSs04G0/TYgRR2g98t4AHa/vHu68Q2u/n94etvYx/d1PnFkSk0raY0sWV4szKWU013m/RSeM'
    '8zP0ss+knSlyOMlbtXu8U+pnTr3SU8gdpna+UuS9OHJRoV/vS46//efgUzoYdD/xdGrsUqLi5Cs/ENf/w61IHlCZ2hJuvqC26zmC'
    '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'
    'EuDg/XV1BP3+Ooah4990fvKD/weXDq1IPyQkAA=='
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
