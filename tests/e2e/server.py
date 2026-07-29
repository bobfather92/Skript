import os
import shutil
import sys
import threading
from pathlib import Path
from http.server import ThreadingHTTPServer


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import skript  # noqa: E402


PORT = int(os.environ.get('SKRIPT_E2E_PORT', '4173'))
RUN_DIR = (ROOT / 'tmp' / 'e2e-data').resolve()
if ROOT.resolve() not in RUN_DIR.parents:
    raise RuntimeError('E2E data directory escaped the workspace')
if RUN_DIR.exists():
    shutil.rmtree(RUN_DIR)

userdata = RUN_DIR / 'userdata'
scripts = RUN_DIR / 'scripts'
userdata.mkdir(parents=True)
scripts.mkdir(parents=True)

skript.USERDATA_DIR = userdata
skript.SCRIPTS_DIR = scripts
skript._MAIN_PORT_VAL = PORT
skript._API_TOKEN = 'skript-e2e-token'
skript.SFHandler.html_bytes = skript._get_html(
    PORT,
    low_perf=False,
    api_token=skript._API_TOKEN,
)

class E2EHandler(skript.SFHandler):
    def do_POST(self):
        if self.path == '/__e2e_shutdown':
            self._json({'ok': True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()
            return
        if self.path == '/__e2e_window_event':
            seq = skript._publish_window_event('request-close')
            self._json({'ok': True, 'seq': seq})
            return
        if self.path == '/__e2e_clear_window_event':
            seq = skript._publish_window_event('')
            self._json({'ok': True, 'seq': seq})
            return
        super().do_POST()


E2EHandler.html_bytes = skript.SFHandler.html_bytes
server = ThreadingHTTPServer(('127.0.0.1', PORT), E2EHandler)
server.daemon_threads = True
print(f'Skript E2E service listening on http://127.0.0.1:{PORT}', flush=True)
try:
    server.serve_forever()
finally:
    server.server_close()
