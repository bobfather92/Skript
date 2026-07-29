const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
const apiStart = html.indexOf('function sfApiUrl(');
const apiEnd = html.indexOf('async function sfApiFetch(', apiStart);
assert.ok(apiStart >= 0 && apiEnd > apiStart);

const httpContext = { location: { protocol: 'http:', port: '9123' }, window: { _SF_PORT: 9123 } };
vm.createContext(httpContext);
vm.runInContext(html.slice(apiStart, apiEnd), httpContext);
assert.equal(httpContext.sfApiUrl('/api/save-auto'), '/api/save-auto');

const restoredContext = { location: { protocol: 'http:', port: '8768' }, window: { _SF_PORT: 9123 } };
vm.createContext(restoredContext);
vm.runInContext(html.slice(apiStart, apiEnd), restoredContext);
assert.equal(restoredContext.sfApiUrl('/api/open'), 'http://127.0.0.1:9123/api/open');

const fileContext = { location: { protocol: 'file:' }, window: { _SF_PORT: 9123 } };
vm.createContext(fileContext);
vm.runInContext(html.slice(apiStart, apiEnd), fileContext);
assert.equal(fileContext.sfApiUrl('/api/open'), 'http://127.0.0.1:9123/api/open');
assert.ok(!html.includes("fetch('http://127.0.0.1:' + window._SF_PORT"));
assert.ok(html.includes('id="open-changes-btn"'), 'Options must expose versioned changes');
assert.ok(html.includes('data-changes-version="1.1.0.0"'));
assert.ok(html.includes('Changes in 1.1.0.0'));
assert.equal((html.match(/data-changes-version=/g) || []).length, 1, 'Only the official release should appear');
assert.ok(html.includes('data-testid="recovery-centre"'), 'Help must expose Recovery Centre');
assert.ok(html.includes('data-testid="report-problem"'), 'Help must expose Report a Problem');
assert.ok(html.includes('function restoreRecoveryPayload(data)'));
assert.ok(html.includes('function copyDiagnosticInformation()'));
assert.ok(html.includes('event.returnValue ='), 'Unsaved work must trigger the native close warning');
assert.ok(html.includes('data-testid="import-word"'), 'Import ribbon must expose Word import');
assert.ok(html.includes('id="word-import-input"'));
assert.ok(html.includes('function handleWordImport(event)'));
assert.ok(html.includes('function _importDocxLocally(bytes, filename)'), 'DOCX import must have an offline built-in reader');
assert.ok(html.includes('exports.JSZip = JSZip'), 'The bundled Word engine must expose its local ZIP reader');
assert.ok(html.includes('data-testid="import-writerduet"'), 'Import ribbon must expose WriterDuet import');
assert.ok(html.includes('id="writerduet-input"'));
assert.ok(html.includes('function handleWriterDuetImport(event)'));
assert.ok(html.includes("source: 'writerduet'"), 'WriterDuet imports must preserve their source profile');
assert.ok(html.includes('id="wiz-recent-list"'), 'Welcome screen must include recent projects');
assert.ok(html.includes('class="wiz-brand-mark" src="/favicon.png"'), 'Welcome screen must use the packaged Skript icon');
assert.ok(!html.includes('class="wiz-recent-browse"'), 'Open Project already provides the file browser');
assert.ok(html.includes('.wiz-recent-window {\n    width: 100%;'), 'Recent Projects must match the welcome-card width');
assert.ok(html.includes('scripts.slice(0, 3)'), 'Welcome must show no more than three recent projects');
assert.ok(html.includes('#wiz-recent-list { height: auto; overflow: visible;'), 'Welcome recent projects must not scroll');
assert.ok(html.includes('id="wiz-clear-recent"'), 'Welcome Recent Projects must provide a Clear button');
assert.ok(html.includes('id="recent-clear-btn"'), 'Recent Projects modal must provide a Clear button');
assert.ok(html.includes('function confirmClearRecentProjects()'), 'Clear Recent Projects must use the protected API workflow');
assert.ok(html.includes('Your saved project files will remain on this computer.'), 'Clear confirmation must explain that saved projects are retained');
assert.ok(html.includes('id="desktop-titlebar"'), 'Desktop shell must provide Skript-owned window controls');
assert.ok(html.includes('id="desktop-close-modal"'), 'Desktop shell must provide its own save-before-close dialog');
assert.ok(
  html.includes("if (window._SF_NATIVE_TITLEBAR_OVERLAY && desktopCloseApproved)"),
  'An approved Skript close must bypass the browser beforeunload dialog'
);
assert.ok(html.includes('--amber: var(--brand-purple)'), 'Interface accent labels must use Skript purple');
assert.ok(html.includes('#pv-btn-sidebyside { width: 26px'), 'Side-by-side View glyph must fit its background plate');

const editorWorkStart = html.indexOf('const editorUiWork =');
const editorWorkEnd = html.indexOf('function onLineInput(', editorWorkStart);
const editorWorkSource = html.slice(editorWorkStart, editorWorkEnd);
assert.ok(editorWorkSource.includes('setTimeout('), 'Large-document UI work must be debounced');
assert.ok(!editorWorkSource.includes('requestAnimationFrame('), 'Full-document scans must not run every frame');
assert.ok(html.includes('function scheduleAutocomplete(line)'), 'Large autocomplete lists must be debounced');

const collabStart = html.indexOf('async function collabCreate()');
const collabEnd = html.indexOf('// ── Copy link', collabStart);
assert.ok(html.slice(collabStart, collabEnd).includes('timeoutMs: 60000'));

const openStart = html.indexOf('function loadScript()');
const openEnd = html.indexOf('function handleFileLoad(', openStart);
const openSource = html.slice(openStart, openEnd);
assert.ok(openSource.includes("document.getElementById('file-input')?.click()"));
assert.ok(!openSource.includes('sfApiFetch'), 'Open must use only the local file picker');
assert.ok(html.includes('id="file-input"         accept=".script,.sfg,.json" multiple'), 'Project picker must support batch import');
assert.ok(html.includes("const SKRIPT_PROJECT_COLLECTION_SCHEMA = 'com.skript.project-collection'"));
assert.ok(html.includes('function readProjectCollectionData(input)'));
assert.ok(html.includes('const files = Array.from(input?.files || [])'));
assert.ok(html.includes('data-testid="add-script-document"'), 'Navigator must expose script import');

const pdfStart = html.indexOf('async function doExportPDF()');
const pdfEnd = html.indexOf('function _fallbackWindowPrint(', pdfStart);
const pdfSource = html.slice(pdfStart, pdfEnd);
assert.ok(pdfSource.includes('_fallbackWindowPrint(incTitle, incScript, incNotes)'));
assert.ok(pdfSource.includes("sfApiFetch('/api/export-pdf'"), 'Desktop PDF export must suppress browser headers');
assert.ok(pdfSource.includes('getLinesContainer(activeTabId)'), 'PDF export must read only the active script');
assert.ok(html.includes('data-testid="export-include-notes"'), 'Export ribbon must expose Include Notes');
assert.ok(html.includes("includeNotes: incNotes"), 'PDF export must send the Notes choice');
assert.ok(html.includes("type === 'notes' && !includeNotes"), 'Word export must omit Notes when unticked');
assert.ok(html.includes("if (!includeNotes) break;"), 'Fountain export must omit Notes when unticked');
assert.ok(html.includes("buildFDXDocument(includeNotes = exportNotesEnabled())"), 'FDX export must use the Notes choice');

for (const feature of [
  'scanActiveDocumentSuggestions({ notify: false })',
  "data.source === 'pdf'",
  "_editor.addEventListener('touchmove'",
  'function sbGoToPage(delta)',
  "page.className = 'sb-page'",
  "event.stopPropagation();switchToBoard",
]) {
  assert.ok(html.includes(feature), `Missing workflow feature: ${feature}`);
}

console.log('Desktop, import, touch, and storyboard workflow regression tests passed.');
