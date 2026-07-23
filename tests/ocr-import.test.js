const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const html = fs.readFileSync(path.join(__dirname, '..', 'ScriptForge.html'), 'utf8');
const start = html.indexOf('function _ocrItemsFromResult(');
const end = html.indexOf('async function _ocrPDFPages(', start);
assert.ok(start >= 0 && end > start, 'OCR result converter is present');

const context = {};
vm.createContext(context);
vm.runInContext(html.slice(start, end), context);

const viewport = { width: 612, height: 792 };
const fromBlocks = context._ocrItemsFromResult({
  blocks: [{ paragraphs: [{ lines: [
    { text: '  INT. LAB - NIGHT  ', confidence: 96, bbox: { x0: 200, y0: 100, x1: 800, y1: 140 } },
    { text: 'MAYA', confidence: 72, bbox: { x0: 600, y0: 180, x1: 760, y1: 220 } },
  ] }] }],
}, 2, viewport, 2);

assert.equal(fromBlocks.length, 2);
assert.equal(fromBlocks[0].text, 'INT. LAB - NIGHT');
assert.equal(fromBlocks[0].x, 100);
assert.equal(fromBlocks[0].page, 2);
assert.equal(fromBlocks[1]._ocrConfidence, 72);

const tsv = [
  'level\tpage_num\tblock_num\tpar_num\tline_num\tword_num\tleft\ttop\twidth\theight\tconf\ttext',
  '5\t1\t1\t1\t1\t1\t100\t80\t60\t20\t88\tCUT',
  '5\t1\t1\t1\t1\t2\t170\t80\t40\t20\t92\tTO:',
].join('\n');
const fromTsv = context._ocrItemsFromResult({ tsv }, 1, viewport, 1);
assert.equal(fromTsv.length, 1);
assert.equal(fromTsv[0].text, 'CUT TO:');
assert.equal(fromTsv[0]._ocrConfidence, 90);

const ocrStart = html.indexOf('async function _ocrPDFPages(');
const ocrEnd = html.indexOf('function handlePDFImport(', ocrStart);
const ocrSource = html.slice(ocrStart, ocrEnd);
assert.match(ocrSource, /workerPath:'\/vendor\/ocr\/worker\.min\.js'/);
assert.match(ocrSource, /langPath:'\/vendor\/ocr\/lang'/);
assert.match(ocrSource, /corePath:'\/vendor\/ocr\/core'/);
assert.doesNotMatch(ocrSource, /https?:\/\//, 'OCR must not use a remote service or CDN');
assert.match(html, /scannedPages\.length/);
assert.match(html, /_cancelPDFImport\(\)/);

console.log('Offline scanned-PDF OCR regression tests passed.');
