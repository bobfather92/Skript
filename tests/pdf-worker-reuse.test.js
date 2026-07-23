const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const start = html.indexOf("const PDF_JS_LOCAL =");
const end = html.indexOf('function handlePDFImport(', start);
assert.ok(start >= 0 && end > start, 'PDF engine loader source is present');
const loader = html.slice(start, end);

assert.match(loader, /let _pdfjsPromise = null/);
assert.match(loader, /if \(_pdfjsPromise\) return _pdfjsPromise/);
assert.match(loader, /new Worker\(blobUrl, \{ type: 'module'/);
assert.match(loader, /GlobalWorkerOptions\.workerPort = worker/);
assert.match(loader, /fetch\(workerUrl, \{ cache: 'force-cache' \}\)/);
assert.doesNotMatch(loader, /GlobalWorkerOptions\.workerSrc = workerUrl/);

console.log('PDF worker reuse regression tests passed.');
