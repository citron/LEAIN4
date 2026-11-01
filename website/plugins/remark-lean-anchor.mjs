// Replaces ```lean file=Ch01/Neuron.lean#anchor``` blocks by the real, compiled source region.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {visit} from 'unist-util-visit';

const here = path.dirname(fileURLToPath(import.meta.url));
const leanRoot = path.resolve(here, '..', '..', 'lean', 'LeanDL');

const cache = new Map();

function extract(file, anchor) {
  const full = path.join(leanRoot, file);
  if (!cache.has(full)) cache.set(full, fs.readFileSync(full, 'utf8').split(/\r?\n/));
  const lines = cache.get(full);
  const start = lines.findIndex((l) => l.trim() === `-- ANCHOR: ${anchor}`);
  const end = lines.findIndex((l) => l.trim() === `-- ANCHOR_END: ${anchor}`);
  if (start < 0 || end < 0 || end < start) {
    throw new Error(`Lean anchor not found: ${file}#${anchor}`);
  }
  return lines
    .slice(start + 1, end)
    .filter((l) => !/^\s*-- ANCHOR(_END)?:/.test(l))
    .join('\n');
}

export default function remarkLeanAnchor() {
  return (tree, vfile) => {
    visit(tree, 'code', (node) => {
      if (node.lang !== 'lean' || !node.meta) return;
      const m = /file=(\S+?)#(\S+)/.exec(node.meta);
      if (!m) return;
      try {
        node.value = extract(m[1], m[2]);
      } catch (e) {
        throw new Error(`${e.message} (in ${vfile.path})`);
      }
      node.meta = node.meta.replace(/file=\S+/, '').trim() + ` title="${m[1]}"`;
    });
  };
}
