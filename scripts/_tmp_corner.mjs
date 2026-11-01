import fs from 'node:fs';
import path from 'node:path';
const root = 'c:/Users/wgacq/source/LEAIN4';
const dirs = {en: `${root}/website/docs`, fr: `${root}/website/i18n/fr/docusaurus-plugin-content-docs/current`};

function headingIndex(lines, level, idx) {
  const re = new RegExp('^' + '#'.repeat(level) + ' ');
  let fence = false, c = 0;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('```')) fence = !fence;
    if (!fence && re.test(lines[i]) && ++c === idx) return i;
  }
  throw new Error('heading not found');
}
function insert(file, lang, level, idx, mode, block) {
  const p = path.join(dirs[lang], `${file}.mdx`);
  const text = fs.readFileSync(p, 'utf8');
  if (text.includes(block.split('\n')[0])) return;
  const lines = text.split('\n');
  const h = headingIndex(lines, level, idx);
  let at;
  if (mode === 'before') at = h;
  else {
    let i = h + 1;
    while (lines[i].trim() === '') i++;
    if (/^(```|\$\$|:::|<|\||-|\d+\.|#)/.test(lines[i])) at = h + 1;
    else { while (lines[i].trim() !== '') i++; at = i; }
  }
  lines.splice(at, 0, '', ...block.split('\n'), '');
  fs.writeFileSync(p, lines.join('\n'));
}
const corner = (title, body) => `:::tip[Lean Corner: ${title}]\n${body}\n:::`;

insert('ch07-rnn', 'en', 2, 1, 'para', corner('recursion on `Nat` and hypotheses as arguments',
  'The functions `hE` and `jacRec` are defined by recursion on the time step `t : Nat`: one case for `0`, one for `t + 1`. A theorem such as `jacRec_sq_le` takes its assumptions as ordinary arguments, so to use it you must supply a proof of each. Proofs about such functions go by induction on `t`, following the same two cases.'));
insert('ch07-rnn', 'fr', 2, 1, 'para', corner('r\u00e9cursion sur `Nat` et hypoth\u00e8ses comme arguments',
  'Les fonctions `hE` et `jacRec` sont d\u00e9finies par r\u00e9cursion sur le pas de temps `t : Nat` : un cas pour `0`, un pour `t + 1`. Un th\u00e9or\u00e8me comme `jacRec_sq_le` prend ses hypoth\u00e8ses comme des arguments ordinaires : pour l\u2019utiliser il faut fournir une preuve de chacune. Les preuves sur de telles fonctions se font par r\u00e9currence sur `t`, avec les m\u00eames deux cas.'));
insert('ch08-lstm', 'en', 2, 2, 'para', corner('inequalities on products, over `Rat`',
  'To bound a product you need the bounds of every factor as hypotheses (`0 \u2264 f t`, `a \u2264 f t`) and a proof that multiplies them one step at a time (`prodF_ge`). We work over `Rat`, the exact rationals, because they come with an order that `grind` can use; an abstract ring has no order to speak of.'));
insert('ch08-lstm', 'fr', 2, 2, 'para', corner('in\u00e9galit\u00e9s sur des produits, sur `Rat`',
  'Pour borner un produit, il faut les bornes de chaque facteur comme hypoth\u00e8ses (`0 \u2264 f t`, `a \u2264 f t`) et une preuve qui les multiplie pas \u00e0 pas (`prodF_ge`). Nous travaillons sur `Rat`, les rationnels exacts, car ils portent un ordre que `grind` sait utiliser ; un anneau abstrait n\u2019a pas d\u2019ordre.'));
insert('ch09-transformer', 'en', 2, 2, 'para', corner('abstract fields, lists and permutations',
  'A theorem stated for any `[Field \u03b1] [HasExp \u03b1]` holds for every number type with these operations, from `Rat` to `Float` (as an approximation). `List.Perm l\u2081 l\u2082` says that two lists have the same elements in any order: `attendL_perm` uses it to state precisely that attention cannot see the order of its inputs.'));
insert('ch09-transformer', 'fr', 2, 2, 'para', corner('corps abstraits, listes et permutations',
  'Un th\u00e9or\u00e8me \u00e9nonc\u00e9 pour tout `[Field \u03b1] [HasExp \u03b1]` vaut pour tout type de nombres muni de ces op\u00e9rations, de `Rat` \u00e0 `Float` (comme approximation). `List.Perm l\u2081 l\u2082` dit que deux listes ont les m\u00eames \u00e9l\u00e9ments dans un ordre quelconque : `attendL_perm` l\u2019utilise pour dire pr\u00e9cis\u00e9ment que l\u2019attention ne voit pas l\u2019ordre de ses entr\u00e9es.'));
insert('ch15-jepa', 'en', 2, 1, 'para', corner('`if` inside definitions, and statements about all minimisers',
  '`vreg` is defined with an `if`. To prove something about it, `split` (or `by_cases`) turns the `if` into two goals, one per branch; in a branch whose condition contradicts a hypothesis, `exfalso` and `grind` finish. A statement like `collapse_is_minimal` says that one particular value is below every other value: that is what \u201cminimiser\u201d means in Lean.'));
insert('ch15-jepa', 'fr', 2, 1, 'para', corner('`if` dans les d\u00e9finitions, et \u00e9nonc\u00e9s sur tous les minimiseurs',
  '`vreg` est d\u00e9finie avec un `if`. Pour prouver quelque chose \u00e0 son sujet, `split` (ou `by_cases`) transforme le `if` en deux buts, un par branche ; dans une branche dont la condition contredit une hypoth\u00e8se, `exfalso` et `grind` terminent. Un \u00e9nonc\u00e9 comme `collapse_is_minimal` dit qu\u2019une valeur particuli\u00e8re est inf\u00e9rieure \u00e0 toutes les autres : c\u2019est ce que \u00ab minimiseur \u00bb signifie en Lean.'));

const graph = `
flowchart LR
  c0["0 Lean"] --> c1["1 Neuron"] --> c2["2 Perceptron"] --> c3["3 MLP"] --> c4["4 Autodiff"] --> c5["5 Training"]
  c5 --> c6["6 CNN"]
  c5 --> c7["7 RNN"] --> c8["8 LSTM"]
  c5 --> c9["9 Transformer"]
  c8 -.-> c9
  c6 -.->|"Lean lemmas on sums"| c9
  c5 --> c10["10 VAE"] --> c11["11 GAN"]
  c10 --> c12["12 Diffusion"]
  c11 -.-> c12
  c4 --> c13["13 RL"] --> c14["14 World models"]
  c10 --> c15["15 JEPA"]
  c14 --> c15
  c12 -.-> c15
`.trim();
insert('concepts-index', 'en', 2, 1, 'before',
  `## Prerequisite graph\n\nSolid arrows: you need the previous chapter. Dashed arrows: recommended, but not required.\n\n\`\`\`mermaid\n${graph}\n\`\`\`\n\n*Which chapters you need before reading a given chapter. Arrow \u201c6 to 9\u201d means that the Lean lemmas on sums of Chapter 6 are reused in Chapter 9.*`);
insert('concepts-index', 'fr', 2, 1, 'before',
  `## Graphe des pr\u00e9requis\n\nFl\u00e8ches pleines : le chapitre pr\u00e9c\u00e9dent est n\u00e9cessaire. Fl\u00e8ches en pointill\u00e9s : recommand\u00e9, mais pas obligatoire.\n\n\`\`\`mermaid\n${graph}\n\`\`\`\n\n*Les chapitres n\u00e9cessaires avant de lire un chapitre donn\u00e9. La fl\u00e8che \u00ab 6 vers 9 \u00bb signifie que les lemmes Lean sur les sommes du chapitre 6 sont r\u00e9utilis\u00e9s au chapitre 9.*`);
console.log('ok');
