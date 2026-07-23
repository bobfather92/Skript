import os
import shutil
import sys
import threading
from pathlib import Path
from http.server import ThreadingHTTPServer


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import scriptforge  # noqa: E402


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

scriptforge.USERDATA_DIR = userdata
scriptforge.SCRIPTS_DIR = scripts
scriptforge._MAIN_PORT_VAL = PORT
scriptforge._API_TOKEN = 'skript-e2e-token'
scriptforge.SFHandler.html_bytes = scriptforge._get_html(
    PORT,
    low_perf=False,
    api_token=scriptforge._API_TOKEN,
)

class E2EHandler(scriptforge.SFHandler):
    def do_POST(self):
        if self.path == '/__e2e_shutdown':
            self._json({'ok': True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()
            return
        super().do_POST()


E2EHandler.html_bytes = scriptforge.SFHandler.html_bytes
server = ThreadingHTTPServer(('127.0.0.1', PORT), E2EHandler)
server.daemon_threads = True
print(f'Skript E2E service listening on http://127.0.0.1:{PORT}', flush=True)
try:
    server.serve_forever()
finally:
    server.server_close()
