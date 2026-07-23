const fs = require('node:fs');
const path = require('node:path');

const html = fs.readFileSync(path.join(__dirname, '..', 'ScriptForge.html'), 'utf8');
const scripts = [...html.matchAll(/<script([^>]*)>([\s\S]*?)<\/script>/gi)];
let compiled = 0;

for (const [, attributes, source] of scripts) {
  if (/\bsrc\s*=/.test(attributes) || /type\s*=\s*["']application\/json/i.test(attributes)) continue;
  try {
    new Function(source);
    compiled++;
  } catch (error) {
    throw new Error(`Inline script ${compiled + 1} failed to compile: ${error.message}`);
  }
}

console.log(`Compiled ${compiled} inline script blocks successfully.`);
