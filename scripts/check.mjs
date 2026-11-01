// Course consistency checks: EN/FR page parity and no `sorry` outside Exercises.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const enDir = path.join(root, 'website', 'docs');
const frDir = path.join(root, 'website', 'i18n', 'fr', 'docusaurus-plugin-content-docs', 'current');
const leanDir = path.join(root, 'lean', 'LeanDL');

const errors = [];

const list = (dir, ext) =>
  fs.readdirSync(dir, {recursive: true}).filter((f) => String(f).endsWith(ext)).map(String).sort();

const fenceCount = (file) => (fs.readFileSync(file, 'utf8').match(/^```/gm) ?? []).length;
const headingCount = (file) => (fs.readFileSync(file, 'utf8').match(/^#{1,3} /gm) ?? []).length;
const anchors = (file) =>
  [...fs.readFileSync(file, 'utf8').matchAll(/file=(\S+)/g)].map((m) => m[1]).sort().join(',');

const en = list(enDir, '.mdx');
const fr = list(frDir, '.mdx');
for (const f of en) if (!fr.includes(f)) errors.push(`missing French page: ${f}`);
for (const f of fr) if (!en.includes(f)) errors.push(`French page without English page: ${f}`);
for (const f of en.filter((x) => fr.includes(x))) {
  const a = path.join(enDir, f);
  const b = path.join(frDir, f);
  if (fenceCount(a) !== fenceCount(b)) errors.push(`${f}: code block count differs EN/FR`);
  if (headingCount(a) !== headingCount(b)) errors.push(`${f}: heading count differs EN/FR`);
  if (anchors(a) !== anchors(b)) errors.push(`${f}: embedded Lean anchors differ EN/FR`);
}

for (const f of list(leanDir, '.lean')) {
  if (f.endsWith('Exercises.lean')) continue;
  if (/\bsorry\b/.test(fs.readFileSync(path.join(leanDir, f), 'utf8').replace(/--.*$/gm, ''))) {
    errors.push(`sorry outside Exercises: ${f}`);
  }
}

if (errors.length) {
  console.error(errors.join('\n'));
  process.exit(1);
}
console.log(`OK: ${en.length} pages in en and fr, no stray sorry.`);
