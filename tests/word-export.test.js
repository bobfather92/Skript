const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const html = fs.readFileSync(path.join(__dirname, '..', 'Skript.html'), 'utf8');
assert.ok(!html.includes('cdn.jsdelivr.net/npm/docx'), 'Word export must not require a CDN');

const match = html.match(/<script id="skript-docx-engine"[^>]*>([\s\S]*?)<\/script>/);
assert.ok(match?.[1].includes('var docx ='), 'Bundled DOCX engine is present');

const context = {
  console,
  setTimeout,
  clearTimeout,
  setImmediate,
  clearImmediate,
  Blob,
  TextEncoder,
  TextDecoder,
  Uint8Array,
  ArrayBuffer,
  DataView,
  crypto: globalThis.crypto,
  atob: globalThis.atob,
  btoa: globalThis.btoa,
};
context.window = context;
context.self = context;
context.globalThis = context;
vm.createContext(context);
vm.runInContext(match[1], context, { filename: 'bundled-docx-engine.js' });
assert.ok(context.docx?.Document && context.docx?.Packer, 'DOCX API started');

(async () => {
  const { Document, Packer, Paragraph, TextRun } = context.docx;
  const document = new Document({
    sections: [{
      children: [new Paragraph({ children: [new TextRun({ text: 'Skript export test' })] })],
    }],
  });
  const blob = await Packer.toBlob(document);
  const bytes = Buffer.from(await blob.arrayBuffer());
  assert.equal(bytes.subarray(0, 2).toString('ascii'), 'PK', 'DOCX is a ZIP package');
  assert.ok(bytes.length > 1000, 'DOCX package contains document parts');
  console.log('Offline Word export engine generated a valid DOCX package.');
})().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
