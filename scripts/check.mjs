// Course consistency checks. Run from anywhere: `node scripts/check.mjs`.
//  1. EN/FR page parity (pages, code blocks, headings, math blocks, embedded Lean anchors)
//  2. every embedded Lean anchor exists in lean/LeanDL
//  3. every Lean-looking name quoted in a page is declared in lean/LeanDL (or allow-listed)
//  4. no `sorry` outside Exercises; no `axiom`, `admit`, `partial` or `native_decide` in the library
//  5. every module of lean/LeanDL (except Exercises) is imported by lean/LeanDL.lean
//  6. every generated SVG is well-formed
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const enDir = path.join(root, 'website', 'docs');
const frDir = path.join(root, 'website', 'i18n', 'fr', 'docusaurus-plugin-content-docs', 'current');
const leanDir = path.join(root, 'lean', 'LeanDL');
const imgDir = path.join(root, 'website', 'static', 'img');

const errors = [];

const list = (dir, ext) =>
  fs.readdirSync(dir, {recursive: true}).filter((f) => String(f).endsWith(ext)).map(String).sort();
const read = (f) => fs.readFileSync(f, 'utf8');

const fenceCount = (file) => (read(file).match(/^```/gm) ?? []).length;
const headingCount = (file) => (read(file).match(/^#{1,3} /gm) ?? []).length;
const displayMath = (file) => (read(file).match(/\$\$/g) ?? []).length;
const anchors = (file) =>
  [...read(file).matchAll(/file=(\S+)/g)].map((m) => m[1]).sort().join(',');

// 1. parity
const en = list(enDir, '.mdx');
const fr = list(frDir, '.mdx');
for (const f of en) if (!fr.includes(f)) errors.push(`missing French page: ${f}`);
for (const f of fr) if (!en.includes(f)) errors.push(`French page without English page: ${f}`);
for (const f of en.filter((x) => fr.includes(x))) {
  const a = path.join(enDir, f);
  const b = path.join(frDir, f);
  if (fenceCount(a) !== fenceCount(b)) errors.push(`${f}: code block count differs EN/FR`);
  if (headingCount(a) !== headingCount(b)) errors.push(`${f}: heading count differs EN/FR`);
  if (displayMath(a) !== displayMath(b)) errors.push(`${f}: display-math ($$) count differs EN/FR`);
  if (anchors(a) !== anchors(b)) errors.push(`${f}: embedded Lean anchors differ EN/FR`);
}

// 2. anchors exist
const leanFiles = list(leanDir, '.lean');
const leanText = new Map(leanFiles.map((f) => [f.replaceAll('\\', '/'), read(path.join(leanDir, f))]));
for (const [dir, label] of [[enDir, 'en'], [frDir, 'fr']]) {
  for (const f of list(dir, '.mdx')) {
    for (const m of read(path.join(dir, f)).matchAll(/file=(\S+?)#(\S+)/g)) {
      const text = leanText.get(m[1]);
      if (text === undefined) errors.push(`${label}/${f}: unknown Lean file ${m[1]}`);
      else if (!text.includes(`-- ANCHOR: ${m[2]}`) || !text.includes(`-- ANCHOR_END: ${m[2]}`)) {
        errors.push(`${label}/${f}: anchor ${m[1]}#${m[2]} not found`);
      }
    }
  }
}

// 3. quoted Lean names are declared
const declared = new Set();
for (const text of leanText.values()) {
  for (const m of text.matchAll(/^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([A-Za-z_][\w.']*)/gm)) {
    const full = m[1];
    declared.add(full);
    declared.add(full.split('.').pop());
  }
  // constructors and fields
  for (const m of text.matchAll(/^\s*\|\s*([a-z]\w*)/gm)) declared.add(m[1]);
  for (const m of text.matchAll(/^\s+([a-z]\w*)\s*:\s/gm)) declared.add(m[1]);
}
const allow = new Set(['grind', 'omega', 'decide', 'simp', 'rfl', 'induction', 'cases', 'lake', 'elan', 'sorry', 'by_cases', 'exact_mod_cast', 'push_cast', 'norm_cast', 'funext', 'congr', 'rw']);
const nameLike = /^[a-z][A-Za-z0-9]*(_[A-Za-z0-9]+)+$|^[a-z]+[A-Z][A-Za-z0-9]*$/;
for (const [dir, label] of [[enDir, 'en'], [frDir, 'fr']]) {
  for (const f of list(dir, '.mdx')) {
    if (f.startsWith('glossary') || f.startsWith('concepts-index')) continue;
    const body = read(path.join(dir, f)).replace(/```[\s\S]*?```/g, '');
    for (const m of body.matchAll(/`([^`\n]+)`/g)) {
      const tok = m[1].trim();
      if (!nameLike.test(tok) || allow.has(tok) || declared.has(tok)) continue;
      errors.push(`${label}/${f}: \`${tok}\` is quoted but not declared in lean/LeanDL`);
    }
  }
}

// 4. forbidden constructs
for (const f of leanFiles) {
  if (f.endsWith('Exercises.lean')) continue;
  const code = leanText.get(f.replaceAll('\\', '/')).replace(/\/-[\s\S]*?-\//g, '').replace(/--.*$/gm, '');
  for (const word of ['sorry', 'admit', 'axiom', 'partial', 'native_decide']) {
    if (new RegExp(`\\b${word}\\b`).test(code)) errors.push(`${word} in ${f}`);
  }
}

// 5. root import file
const rootImports = read(path.join(root, 'lean', 'LeanDL.lean'));
for (const f of leanFiles) {
  if (f.endsWith('Exercises.lean')) continue;
  const mod = 'LeanDL.' + f.replace(/\.lean$/, '').replaceAll('\\', '.').replaceAll('/', '.');
  if (!rootImports.replace(/\r\n/g, '\n').includes(`import ${mod}\n`)) errors.push(`lean/LeanDL.lean does not import ${mod}`);
}

// 6. SVG well-formedness (balanced tags, one root, no NaN/inf)
for (const f of list(imgDir, '.svg')) {
  const s = read(path.join(imgDir, f));
  const stack = [];
  for (const m of s.matchAll(/<(\/?)([A-Za-z][\w-]*)([^>]*?)(\/?)>/g)) {
    if (m[4] === '/') continue;
    if (m[1] === '') stack.push(m[2]);
    else if (stack.pop() !== m[2]) errors.push(`${f}: mismatched </${m[2]}>`);
  }
  if (stack.length) errors.push(`${f}: unclosed <${stack.at(-1)}>`);
  if (!s.startsWith('<svg')) errors.push(`${f}: does not start with <svg`);
  if (/\b(NaN|nan|inf|-inf)\b/.test(s)) errors.push(`${f}: contains NaN or inf`);
}

if (errors.length) {
  console.error(errors.join('\n'));
  process.exit(1);
}
console.log(`OK: ${en.length} pages in en and fr, anchors and names resolve, no sorry outside Exercises.`);
