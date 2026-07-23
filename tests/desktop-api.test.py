import importlib.util
import base64
import json
from pathlib import Path
import tempfile
import threading
import http.client
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("skript_api", ROOT / "scriptforge.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

with tempfile.TemporaryDirectory(dir=ROOT / "tmp") as temp_dir:
    base = Path(temp_dir)
    module.USERDATA_DIR = base / "userdata"
    module.SCRIPTS_DIR = base / "scripts"
    module.USERDATA_DIR.mkdir()
    module.SCRIPTS_DIR.mkdir()
    module._API_TOKEN = "integration-token"

    server = module.ThreadingHTTPServer(("127.0.0.1", 0), module.SFHandler)
    module._MAIN_PORT_VAL = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    def post(path, payload, extra_headers=None):
        headers = {
            "Content-Type": "application/json",
            "X-ScriptForge-Token": module._API_TOKEN,
        }
        headers.update(extra_headers or {})
        request = Request(
            f"http://127.0.0.1:{server.server_address[1]}{path}",
            data=json.dumps(payload).encode("utf-8"),
            headers=headers,
            method="POST",
        )
        with urlopen(request, timeout=5) as response:
            return json.loads(response.read())

    def get(path):
        request = Request(
            f"http://127.0.0.1:{server.server_address[1]}{path}",
            headers={"X-ScriptForge-Token": module._API_TOKEN},
            method="GET",
        )
        with urlopen(request, timeout=5) as response:
            return json.loads(response.read())

    def guest_post(port, path, payload, access_token=""):
        headers = {"Content-Type": "application/json"}
        if access_token:
            headers["X-Collab-Token"] = access_token
        request = Request(
            f"http://127.0.0.1:{port}{path}",
            data=json.dumps(payload).encode("utf-8"),
            headers=headers,
            method="POST",
        )
        with urlopen(request, timeout=5) as response:
            return json.loads(response.read())

    def guest_get(port, path, access_token=""):
        headers = {"X-Collab-Token": access_token} if access_token else {}
        request = Request(
            f"http://127.0.0.1:{port}{path}", headers=headers, method="GET"
        )
        with urlopen(request, timeout=5) as response:
            return json.loads(response.read())

    try:
        connection = http.client.HTTPConnection("127.0.0.1", server.server_address[1], timeout=5)
        request_headers = {"X-ScriptForge-Token": module._API_TOKEN}
        connection.request("GET", "/api/version", headers=request_headers)
        first_response = connection.getresponse()
        assert first_response.version == 11
        assert json.loads(first_response.read())["ok"] is True
        first_socket = connection.sock
        connection.request("GET", "/api/version", headers=request_headers)
        second_response = connection.getresponse()
        assert json.loads(second_response.read())["ok"] is True
        assert connection.sock is first_socket, "Loopback API should reuse its HTTP/1.1 connection"
        connection.close()

        with urlopen(f"http://127.0.0.1:{server.server_address[1]}/favicon.ico", timeout=5) as response:
            assert response.headers.get_content_type() == "image/x-icon"
            assert len(response.read()) > 1_000
        with urlopen(f"http://127.0.0.1:{server.server_address[1]}/favicon.png", timeout=5) as response:
            assert response.headers.get_content_type() == "image/png"
            assert len(response.read()) > 1_000

        script = {
            "version": 4,
            "title": "API Test",
            "lines": [{"type": "scene", "text": "INT. ROOM - DAY", "lineId": "line-1"}],
        }
        saved = post("/api/save-auto", {"title": "API Test", "content": json.dumps(script)})
        assert saved["ok"] is True
        assert Path(saved["path"]).exists()

        loaded = post("/api/load-script", {"path": saved["path"]})
        assert loaded["ok"] is True
        assert json.loads(loaded["content"])["title"] == "API Test"

        legacy_word = br"{\rtf1\ansi ACT I\par SCENE 1\par HAMLET: To be, or not to be.\par}"
        imported_word = post("/api/import-word", {
            "filename": "legacy-script.doc",
            "content": base64.b64encode(legacy_word).decode("ascii"),
        })
        assert imported_word["ok"] is True
        assert imported_word["converter"] == "RTF reader"
        assert any(line["type"] == "character" for line in imported_word["lines"])

        updated_script = {
            **script,
            "title": "API Test Updated",
            "lines": [{"type": "scene", "text": "EXT. UPDATED ROAD - NIGHT", "lineId": "line-1"}],
        }
        updated = post("/api/save-auto", {
            "title": "API Test Updated",
            "path": saved["path"],
            "content": json.dumps(updated_script),
        })
        assert updated["path"] == saved["path"]
        backup_path = Path(saved["path"] + ".bak1")
        assert backup_path.exists()
        assert json.loads(backup_path.read_text("utf-8"))["title"] == "API Test"

        Path(saved["path"]).write_text('{"truncated":', encoding="utf-8")
        recovered = post("/api/load-script", {"path": saved["path"]})
        assert recovered["ok"] is True
        assert recovered["recoveredFrom"].endswith(".bak1")
        assert json.loads(recovered["content"])["title"] == "API Test"

        recovery_workspace = {
            "schema": "com.skript.workspace-recovery",
            "version": 1,
            "activeProjectId": "project-api",
            "projects": [{**script, "projectId": "project-api"}],
        }
        blocked_userdata = base / "blocked-history-userdata"
        blocked_scripts = base / "blocked-history-scripts"
        blocked_userdata.mkdir()
        blocked_scripts.mkdir()
        (blocked_userdata / "recovery_history").write_text(
            "history location unavailable", encoding="utf-8"
        )
        module._atomic_write_bytes(
            blocked_userdata / "recovery.recover", json.dumps(recovery_workspace)
        )
        blocked_entries = module._recovery_entries(blocked_userdata, blocked_scripts)
        assert len(blocked_entries) == 1
        assert blocked_entries[0]["source"] == "Crash recovery"

        recovery_path = module.USERDATA_DIR / "recovery.recover"
        module._atomic_write_bytes(recovery_path, json.dumps(recovery_workspace))
        (module.USERDATA_DIR / "session.lock").write_text("previous-process", encoding="utf-8")
        crash = get("/api/check-recovery")
        assert crash["crashed"] is True
        assert json.loads(crash["content"])["projects"][0]["title"] == "API Test"

        post("/api/clear-recovery", {})
        assert (module.USERDATA_DIR / "session.lock").exists()
        post("/api/start-session", {})
        assert (module.USERDATA_DIR / "session.lock").read_text("utf-8") == module._PROCESS_SESSION_ID
        heartbeat = post("/api/heartbeat", recovery_workspace)
        assert heartbeat["ok"] is True and recovery_path.exists()
        recovery_list = get("/api/recovery/list")
        assert recovery_list["ok"] is True and recovery_list["entries"]
        selected_copy = recovery_list["entries"][0]
        assert selected_copy["id"] and selected_copy["projectCount"] == 1
        restored_copy = post("/api/recovery/load", {"id": selected_copy["id"]})
        assert restored_copy["ok"] is True
        assert json.loads(restored_copy["content"])["projects"][0]["title"] == "API Test"
        diagnostics = get("/api/diagnostics")
        assert diagnostics["ok"] is True
        diagnostic_text = json.dumps(diagnostics)
        assert "API Test" not in diagnostic_text
        assert str(module.USERDATA_DIR) not in diagnostic_text
        preserved = post(
            "/api/end-session",
            {},
            {"X-ScriptForge-Preserve-Recovery": "1"},
        )
        assert preserved["recoveryPreserved"] is True
        assert recovery_path.exists()
        assert json.loads(recovery_path.read_text("utf-8"))["projects"][0]["title"] == "API Test"
        assert (module.USERDATA_DIR / "session.lock").exists()
        assert module._APP_SHUTDOWN_EVENT.is_set()
        module._APP_SHUTDOWN_EVENT.clear()

        post("/api/start-session", {})
        post("/api/end-session", {})
        assert not recovery_path.exists()
        assert not (module.USERDATA_DIR / "session.lock").exists()
        assert module._APP_SHUTDOWN_EVENT.is_set()
        module._APP_SHUTDOWN_EVENT.clear()

        shared = post(
            "/api/collab/create",
            {
                "view_password": "Amber-River-1234",
                "edit_password": "Editor-Key-5678",
                "duration": "24h",
                "title": "API Test",
                "script": script,
            },
        )
        assert shared["ok"] is True
        assert isinstance(shared["collab_port"], int) and shared["collab_port"] > 0
        session = module._COLLAB_SESSIONS[shared["session_id"]]
        assert session["view_pw_hash"].startswith("pbkdf2_sha256$")
        assert session["edit_pw_hash"].startswith("pbkdf2_sha256$")

        auth = guest_post(
            shared["collab_port"], "/api/collab/auth",
            {"session": shared["session_id"], "password": "Editor-Key-5678", "role": "edit"},
        )
        assert auth["ok"] is True and auth["edit"] is True
        assert auth["access_token"] not in session["access_tokens"]
        token_hash = module.hashlib.sha256(auth["access_token"].encode()).hexdigest()
        assert token_hash in session["access_tokens"]

        viewer_auth = guest_post(
            shared["collab_port"], "/api/collab/auth",
            {"session": shared["session_id"], "password": "Amber-River-1234", "role": "view"},
        )
        denied_edit = guest_post(
            shared["collab_port"], "/api/collab/edit",
            {"session": shared["session_id"], "base_revision": 1, "script": script},
            viewer_auth["access_token"],
        )
        assert denied_edit["ok"] is False and "Editor access" in denied_edit["error"]

        since = module._COLLAB_EVENTS[shared["session_id"]]["seq"]
        stream = http.client.HTTPConnection("127.0.0.1", shared["collab_port"], timeout=4)
        stream.request(
            "GET", f"/api/collab/events?session={shared['session_id']}&since={since}",
            headers={"X-Collab-Token": auth["access_token"], "Accept": "text/event-stream"},
        )
        stream_response = stream.getresponse()
        assert stream_response.status == 200
        assert stream_response.getheader("Content-Type").startswith("text/event-stream")
        # Consume the immediate state snapshot before testing a pushed edit.
        while stream_response.readline() not in (b"\n", b"\r\n", b""):
            pass
        edited_script = {
            "title": "API Test",
            "lines": [{"type": "scene", "text": "INT. EDITED ROOM - NIGHT", "lineId": "line-1"}],
        }
        edit = guest_post(
            shared["collab_port"], "/api/collab/edit",
            {"session": shared["session_id"], "base_revision": 1,
             "author": "Remote Editor", "script": edited_script},
            auth["access_token"],
        )
        assert edit["ok"] is True and edit["revision"] == 2
        assert edit["script"]["lines"][0]["text"] == "INT. EDITED ROOM - NIGHT"
        event_lines = []
        while len(event_lines) < 12:
            line = stream_response.readline()
            if not line:
                break
            event_lines.append(line.decode("utf-8").strip())
            if line in (b"\n", b"\r\n") and "event: script" in event_lines:
                break
        assert "event: script" in event_lines
        event_payload = next(line[6:].strip() for line in event_lines if line.startswith("data:"))
        pushed = json.loads(event_payload)
        assert pushed["revision"] == 2
        assert "access_tokens" not in event_payload and "pw_hash" not in event_payload
        stream.close()

        stale_edit = guest_post(
            shared["collab_port"], "/api/collab/edit",
            {"session": shared["session_id"], "base_revision": 1,
             "author": "Offline Editor", "script": {
                 "title": "API Test",
                 "lines": [{"type": "scene", "text": "EXT. OFFLINE STREET - DAY", "lineId": "line-1"}],
             }},
            auth["access_token"],
        )
        assert stale_edit["ok"] is True and stale_edit["revision"] == 3
        assert len(stale_edit["conflicts"]) == 1
        assert stale_edit["script"]["lines"][0]["text"] == "EXT. OFFLINE STREET - DAY"

        note = guest_post(
            shared["collab_port"], "/api/collab/note",
            {"session": shared["session_id"], "line_idx": 0, "author": "Reviewer", "text": "Clear."},
            viewer_auth["access_token"],
        )
        assert note["ok"] is True
        public_notes = guest_get(
            shared["collab_port"], f"/api/collab/notes?session={shared['session_id']}",
            viewer_auth["access_token"],
        )
        assert "ip" not in public_notes["notes"][0]
    finally:
        server.shutdown()
        server.server_close()
        if module._COLLAB_SERVER is not None:
            module._COLLAB_SERVER.shutdown()
            module._COLLAB_SERVER.server_close()

print("Desktop Save, Open, and secure-sharing API tests passed.")
