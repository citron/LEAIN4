# PROJECT_AUDIT.md — LEAIN4, Phase 1 (audit intégral)

*Audité le 2026-11-02 sur la branche `hermes` (commit `35500f1`). Aucun fichier modifié par cet audit. Tous les chiffres proviennent de l'exécution réelle des commandes indiquées.*

---

## 1. Architecture actuelle

```
LEAIN4/
├── lean/
│   ├── lakefile.toml          # 1 lib LeanDL + 21 exécutables de démo
│   ├── lean-toolchain         # leanprover/lean4:v4.35.0
│   ├── LeanDL.lean            # racine : importe tous les modules formels
│   ├── LeanDL/
│   │   ├── Core/              # Foundations, Algebra, Vec, Mat, Rng, Plot
│   │   ├── Ch00/ … Ch17/      # 18 chapitres : Modules.lean (cours),
│   │   │                      # Exercises.lean, Solutions.lean, (+ modules propres)
│   │   └── (Ch06/Conv, Ch09/Attention+Gpt, Ch16/Tools, Ch17/Contrastive, …)
│   └── Demos/                 # 21 exécutables Float (ch01…ch17, cnn, mnist, gru,
│                              # mhead, vae, gan, diffusion, rl, worldmodel, jepa, figures)
├── website/                   # Docusaurus, 21 pages EN + 21 pages FR (parité stricte)
├── scripts/
│   ├── check.mjs              # parité FR/EN, ancres, politique sorry, native_decide
│   ├── audit_axioms.lean      # collecte d'axiomes de tout le `LeanDL`
│   └── get-mnist.{ps1,sh}     # téléchargement des données MNIST
└── .github/workflows/ci.yml   # CI : build Lake + audit axiomes + site
```

**Aucune dépendance externe** : `lakefile.toml` ne contient aucune ligne `require`. Zéro Mathlib, zéro Python/C++/PyTorch. Tout est en Lean 4 pur (`lean/lakefile.toml`, vérifié par grep `require` → aucune occurrence).

## 2. Cartographie des modules et dépendances

Flux des imports (vérifié par extraction des `^import LeanDL.*`) :

```
Core/Foundations ← Algebra ← Vec ← Mat ← Rng/Plot
   ↓ (uniquement vers le bas — aucun import inverse détecté)
Ch01 Neuron ← Ch02 Perceptron ← Ch03 Mlp/Universal ← Ch04 Autodiff/Correct
                                              ↓
Ch05 Loss/Optim ← Ch06 Conv/Cnn ← Ch07 Rnn ← Ch08 Lstm/Gru/CellPath
                                    ↓
Ch09 Attention/PosEnc/Gpt ← Ch10 Vae ← Ch11 Gan ← Ch12 Diffusion
      ← Ch13 Rl ← Ch14 WorldModel ← Ch15 Jepa
Ch16 Tools (dépend de Ch02 pour sq_nonneg) ← Ch17 Contrastive (dépend de Ch16 Tools + Ch05 Loss)
```

- Dépendances **unidirectionnelles** : aucun module `Core` n'importe un chapitre ; aucun chapitre bas n'importe un chapitre haut. Conforme à la cible « couches » du cahier des charges.
- Deux arêtes à surveiller (voir §9, MINEUR-1/-2) : `Ch16 Tools → Ch02 Perceptron` et `Ch09 Attention → Ch06 Conv`.

Le mapping vers les 4 couches cibles :

| Couche cible | Correspondance actuelle |
|---|---|
| Layer 1 — Core | `Core/Foundations, Algebra, Vec, Mat, Rng, Plot` ✅ |
| Layer 2 — Mathematical Foundations | dispersé : `Ch16/Tools` (log, entropy, KL, variance, Jensen), `Ch04/Correct` (chaîne), `Ch03/Universal` (booléen). **Pas de couche unifiée.** |
| Layer 3 — Deep Learning | `Ch01, Ch02, Ch03, Ch04, Ch05, Ch06/Conv, Ch07, Ch08, Ch09/Attention` ✅ |
| Layer 4 — Applications | `Ch06/Cnn, Ch08 (tâches), Ch09/Gpt, Ch10–Ch15, Demos/` ✅ |

## 3. État des fondations mathématiques

- **Types scalaires** : `Rat` pour tout ce qui est prouvé ; `Float` pour tout ce qui s'exécute. La séparation est effective : grep des `def`/`theorem` formels montre que les modules de preuve sont polymorphes (`[Add α] [Mul α]` …) ou sur `Rat` ; les `Float` n'apparaissent que dans les implémentations de couches/démos et dans `Ch00/Tour.lean` (initiation assumée).
- **Classes algebraiques maison** : `Lean.Grind.CommRing` (fourni par `grind`), `HasExp`/`LawfulExp` (Core/Algebra), `LawfulLog` (Ch16/Tools — log défini par ses lois : `log_mul`, `log_inv`, `log_le`).
- **Vectorues/matricielles** : `Vec α n` = `Fin n → α`, `Mat α m n`, avec `dot`, `add`, `smul`, `mulVec`, `mul`, `transpose`, et les lois prouvées (`dot_comm`, `dot_add_left`, `dot_smul_left`, `Mat.mul_assoc`, `Mat.transpose_mul`, …).
- **Absences notables vs la cible Layer 2** : pas de couche *Probability* (uniquement des distributions finies `Dist n` dans Ch16), pas de couche *Calculus* générale (la dérivée n'existe que comme dérivation syntaxique d'`Expr` en Ch04, pas comme limite/analyticité), pas de *Tensors* (les CNN/RNN plats utilisent des `Array Float` aplatis), pas de statistiques au-delà de l'espérance/variabilité finies de Ch16.

## 4. État des implémentations

- 21 exécutables Lake (`lakefile.toml`) : `ch01 ch02 ch03 ch04 ch05 mnist cnn rnn lstm gru gpt mhead vae gan diffusion rl worldmodel jepa ch16 ch17 figures`.
- Campagne du 2026-11-02 : build complet `EXIT=0` (163+ jobs) et toutes les démos exécutées (`lean/full-build-ch17.log`, `lean/run-all.log`, `lean/gru-run.log`, `lean/mhead-run.log`) :
  - CNN/MNIST : 93,2 % → 94,2 %, contrôle de gradient `0.000000` ;
  - LSTM 100 % (T=10…60), GRU 100 % (T=10…40) ;
  - multi-têtes (h=4) : gradient exact `0.000000` sur 918 paramètres + 128 embeddings, tâche à délai 100 % (lr 0,02 et 0,05) ;
  - InfoNCE : effondrement au plancher prouvé `log(n+1)` (écart `0.00`), entraînement 1,61 → 0,24, cosinus final 1,00.
- Chaque démo embarque un **contrôle numérique par différences finies** : c'est un test, pas une preuve (voir §6, F5).

## 5. État des preuves

Extraction mécanique (`grep -c "^theorem\|^lemma"` par répertoire) :

| Zone | thm/lemma | | Zone | thm/lemma |
|---|---|---|---|---|
| Core | 11 | | Ch10–Ch15 | 8+9+10+9+11+13 |
| Ch00 | 1 | | Ch16 Tools | **37** |
| Ch01–Ch05 | 12+16+14+11+17 | | Ch17 Contrastive | 20 |
| Ch06–Ch09 | 13+9+12+15 | | **Total cours (hors exercices)** | **219** |

**Audit d'axiomes exécuté le 2026-11-02** (`lake env lean ../scripts/audit_axioms.lean`) :

```
checked 1720 declarations; using sorry: []; non-standard axioms: []
```

→ **Zéro `sorry`, zéro axiome non standard** sur 1720 déclarations vérifiées (hors stubs d'exercices). Contrairement à ce que le cahier des charges craint, il n'y a **aucun** `axiom`, `partial`, `unsafe` ou `implementedBy` dans la bibliothèque (grep global : 0 occurrence). Les seules constantes non calculatoires sont les trois axiomes standards de Lean (`propext`, `Classical.choice`, `Quot.sound`).

Preuves de correction algorithmique existantes (F3) — le joyau est Ch04 :

- `fwd_value` / `fwd_tangent` : forward-mode exact ;
- `back_spec` : spécification d'accumulateur du reverse-mode ;
- `backprop_correct` : `backprop e x = gradient de e` — **correction générale de l'autodiff, pas un test** ;
- `forward_eq_dot_backprop` : cohérence forward/retro ;
- Ch03 : `xorNet_correct`, `buildNet_correct`, `universal` (universalité d'un MLP à seuil) ;
- Ch09 : `concat_head`, `concat_injective`, `head_concat` (layout multi-têtes exact) ;
- Ch16 : `ensemble_risk_decomp` (décomposition biais–variance d'un ensemble, algèbre exacte sur `Rat`) ;
- Ch17 : `softmax_dist`, `infoNce_ge_zero`, `infoNce_collapse` (plancher `log(n+1)`), `infonce_grad` (gradient `p − onehot`, instance de `Ch05.ceLoss_grad`).

## 6. Contrat de formalisation F1–F5 : écarts

| Niveau | Statut | Détail |
|---|---|---|
| F1 définitions | ✅ quasi complet | Neurone, MLP, autodiff (`Expr`), softmax/CE, CNN, RNN/LSTM/GRU, attention/multi-têtes, VAE, GAN, diffusion, InfoNCE sont définis formellement. |
| F2 propriétés | ✅ fort | 219 théorèmes ; algèbre `dot`/`Mat`, log/KL/Jensen, layout multi-têtes. |
| F3 correction d'algorithmes | 🟡 partiel | **Complète pour l'autodiff Ch04** (`backprop_correct`). Absente pour : softmax/CE numériques (`softmaxF` Float ≠ pont vers le `softmax` formel), optimiseurs (Adam/SGD = implémentations sans spécification prouvée), convolutions (`Net.forward` Float, pas de sémantique formelle de la boucle), LSTM/GRU/attention exécutables. |
| F4 dérivations | ✅ bon | Chaîne prouvée (Ch04), `ceLoss_grad` (softmax−label), `infonce_grad`, gradient multi-têtes **testé numériquement** à 0.000000 mais **non prouvé**. |
| F5 pont modèle↔implémentation | 🔴 quasi absent | C'est **l'écart structurel n°1** du projet. Rien ne relie formellement le `Rat` prouvé au `Float` exécuté. Le pont est *documenté* (les démos s'annoncent « face numérique des théorèmes ») et *validé empiriquement* (contrôles de gradient), jamais démontré. C'est cohérent avec l'honnêteté du projet, mais cela doit être dit dans chaque chapitre et, à terme, partiellement comblé (bornes d'arrondi). |

## 7. État de la documentation

- 21 pages EN, 21 pages FR, parité vérifiée mécaniquement (`node scripts/check.mjs` → `OK: 21 pages in en and fr, anchors and names resolve, no sorry outside Exercises.`).
- Les extraits de code du site sont **ancrés dans le source** (`ANCHOR`/`ANCHOR_END`) et vérifiés à chaque CI : la documentation ne peut pas citer du code inexistant.
- Chaînage FR Ch15↔Ch17 posé (encadrés « lire le chapitre 17 d'abord »), graphe de dépendances mermaid à jour dans l'index.
- Manque vs le format cible (§7 du cahier des charges) : les pages n'ont pas de blocs normalisés *prérequis / objectifs / théorèmes établis / compétences acquises* ; la structure en 7 dimensions (Understanding → Exercises) est suivie de fait mais **étiquetée de façon hétérogène** d'un chapitre à l'autre.
- Le FR en **serveur de dev** ne rend pas la locale (404 SPA) : documenté, le flux correct est `npm run build && npm run serve`. À écrire dans le README.

## 8. État des tests / CI

CI existante (`.github/workflows/ci.yml`) : build Lake + `lake env lean scripts/audit_axioms.lean` (attend `using sorry: #[]`) + `node scripts/check.mjs` + build Docusaurus.

**BLOQUANT-1 : la CI ne construit pas les cibles récentes.** `build-args` = `… rnn lstm gpt vae …` — il manque `gru`, `mhead`, `ch16`, `ch17` (les 4 cibles ajoutées en phases 1–3, présentes dans le README et le lakefile). Une régression sur GRU/multi-têtes/InfoNCE passe actuellement inaperçue sur GitHub.

- Tests unitaires autonomes : il n'y a que les contrôles de gradient intégrés aux démos (bien, mais exécutés localement, pas en CI — la CI ne lance **aucun** `lake exe`).
- `native_decide` est interdit par `check.mjs` (assimilé à `sorry`) — politique saine, déjà appliquée partout.

## 9. Problèmes classés

### BLOQUANT
- **B1 — CI aveugle sur gru/mhead/ch16/ch17.** Fichiers : `.github/workflows/ci.yml`. Conséquence : les 4 modules phares des phases 1–3 ne sont pas compilés en CI. Correction : aligner `build-args` sur la liste du README (21 exécutables) ; envisager d'instancier une variable/étape unique pour ne plus désynchroniser.

### MAJEUR
- **M1 — Pas de pont F5 Rat↔Float.** Fichiers : tous les `Demos/*.lean` vs les modules formels. Conséquence : les théorèmes portent sur le modèle, les démos exécutent une implémentation non reliée. Correction progressive : pour un premier noyau (softmax/CE de Ch05, puis Ch17), prouver des bornes du type « l'écart entre `Float` et le `Rat` arrondi ≤ ε · nombre d'opérations » au moins sur `exp`/`softmax`/`dot` à taille bornée ; à défaut, un théorème de *consistance d'arrondi locale* vaut mieux que rien, et l'absence doit être dite explicitement dans chaque chapitre (l'aire « limites numériques » du format §7).
- **M2 — F3 absent pour les optimiseurs.** `sgdStep`/`adamStep` (Ch03, Ch05, Ch06) n'ont aucune spécification. Correction : spécifier `loss(sgStep θ) ≤ loss θ` sous convexité/disparité de pente sur un modèle-jonction `Rat` (pente bornée, pas de décroissance convexe) ; 2–3 théorèmes sur SGD à pas fixe, Adam explicitement hors scope prouvé.
- **M3 — La sémantique des couches Float (CNN/RNN/GRU/attention exécutables) n'est pas reliée à la sémantique formelle.** `Ch06/Cnn.forward` (Float) vs `Ch06/Conv` (formel) : cohabitation sans pont. Correction : au moins un théorème de *round-trip layout* par architecture (le multi-têtes Ch09 l'a déjà avec `concat_head`/`head_concat` : c'est le gabarit à répliquer pour la convolution).
- **M4 — Pas de couche Probabilité/Statistique unifiée.** Ch16 a `Dist n`, `expect`, `variance`, KL — isolé dans Ch16. Le §3 cible les place en Layer 2. Correction : promouvoir `Dist/expect/variance/KL/Jensen` de `Ch16/Tools` vers `Core/Prob` (alias Ch16 pour compatibilité), sans réécriture.

### MINEUR
- **Mn1 — `Ch16/Tools → Ch02/Perceptron`** (pour `Ch02.sq_nonneg`) : une fondation dépend d'un chapitre. Correction : descendre `sq_nonneg` dans `Core/Algebra` (une ligne de preuve existe déjà) et réorienter l'import.
- **Mn2 — `Ch09/Attention → Ch06/Conv`** (probablement pour des helpers de layout plate). Correction : déplacer les helpers plats communs dans `Core/Mat`.
- **Mn3 — Chaîne de démos jamais exécutée en CI.** La CI ne lance aucun `lake exe`. Correction : job `smoke` qui exécute 3 démos rapides (ch05, gru, ch17) avec bornes de sortie.
- **Mn4 — Format de chapitre non étiqueté** (prérequis/objectifs/théorèmes acquis) : ajouter un front-matter Docusaurus normalisé, chapitre par chapitre, sans réécrire le contenu.
- **Mn5 — Le README ne documente pas le flux site FR** (`npm run build && npm run serve`, jamais `npm start` pour le FR). Une section de 5 lignes suffit.
- **Mn6 — Exercices Ch03 = stub de `def` + `theorem`** (seul chapitre sans exercice de preuve pure) ; Ch02 n'a qu'un exercice. Harmoniser vers ≥2 exercices dont ≥1 preuve par chapitre.

### AMÉLIORATION
- **A1 — Deux parcours (A DL-first / B formal-first)** : créer deux pages d'index de parcours pointant sur la séquence existante (aucunfork de code — le cahier des charges l'interdit, et c'est déjà garanti).
- **A2 — Tenseurs** : garder `Array Float` aplati pour les démos ; n'introduire `Tensor` que si une preuve en a besoin (éviter l'abstraction prématurée, §11).
- **A3 — `lake exe figures` en CI** comme test d'intégration des visualisations.
- **A4 — Jeu de tests « théorèmes annoncés == théorèmes démontrés »** : `check.mjs` vérifie déjà les ancres ; ajouter la vérification que chaque nom de théorème cité dans les docs existe (`#check` généré automatiquement).

## 10. Plan d'exécution incrémental (tâches indépendantes, vérifiables)

1. **B1** — CI `build-args` complète. Vérif : CI verte avec les 21 cibles. *(½ journée)*
2. **Mn1/Mn2** — `sq_nonneg → Core/Algebra`, helpers plats → `Core/Mat`. Vérif : `lake build LeanDL` + audit axiomes + `check.mjs`. *(1 j)*
3. **Mn3/Mn5** — job smoke CI + section FR du README. Vérif : CI lance 3 démos ; README dit `build && serve`. *(½ j)*
4. **M4** — promotion `Core/Prob` de la partie probabilités de Ch16. Vérif : build complet + audit. *(1–2 j)*
5. **M2** — spécification SGD sur modèle `Rat` (1–2 théorèmes). Vérif : audit axiomes vert. *(2–3 j)*
6. **M1 (noyau)** — borne d'arrondi sur `dot`/`softmaxF` à taille bornée, puis énoncé de consistance Ch17. Vérif : preuves vertes, démos inchangées. *(plusieurs jours, découpage en sondages comme pour Ch17)*
7. **M3** — round-trip layout convolution (gabarit `concat_head`). *(2–3 j)*
8. **Mn4/Mn6/A1** — industrialisation pédagogique (front-matter par chapitre, harmonisation exercices, pages de parcours). *(au fil de l'eau)*

Contraintes d'exécution validées par l'audit : Lean 4.35.0, zéro Mathlib, `grind`/`omega`/`norm_cast`/`decide` (pas de `ring`/`linarith`/`norm_num`/`field_simp`), `native_decide` interdit, ancres `ANCHOR/ANCHOR_END` obligatoires, parité FR/EN à chaque ajout.

- **M4 — RÉSOLU.** La théorie des probabilités finies de Ch16 (`LawfulLog`, `Dist`, lois de `dot`, `expect`/`variance`/`entropy`/`kl`/`crossEntropy`, Gibbs, décomposition CE, décomposition biais-variance d'ensemble) est promue en **`Core/Prob.lean`** (couche 1) ; `Ch16/Tools.lean` devient la page pédagogique qui ré-exporte cette couche, sans aucune modification des preuves. Les ancres du site FR/EN ont suivi (`Core/Prob.lean#…`) ; `check.mjs` est vert.
- **M2 — RÉSOLU pour SGD.** Nouveau bloc `sgd_spec` dans `Ch05/Optim.lean` (sur `Rat` exact, hypotheses explicites `0 < a`, `0 < η`, `η·a < 2`) : `sgd_step_contract` (un pas n'augmente jamais la perte), `sgd_loss_decreases` (chaque itéré reste sous la perte initiale — stabilité de toute la trajectoire), `sgd_critical_step` (au pas `η = 1/a`, convergence en un coup sur le minimiseur). Momentum/Adam gardent leurs théorèmes existants (`ema_const`, `bias_correction`). Docs FR/EN mises à jour (ancre `sgd_spec`) ; audit axiomes : 1754 déclarations, `using sorry: []`.
- **M3 — PREMIERES INSTANTIATIONS ARCHITECTURES (noyau convexe).** Noyau commun prouvé en Core : **`Dist.convex_bound`** (`Core/Prob.lean`) — une combinaison convexe (`w ≥ 0`, `Σw = 1`) de valeurs dans `[-M, M]` reste dans `[-M, M]`. Version séquentielle du drift : **`drift_bound_seq`** (`Core/Algebra.lean`) — facteur par pas `c t` avec `|c t| ≤ 1`, budget linéaire `t·ε` (les portes GRU varient pas à pas, le facteur constant de M1 ne suffit plus). Instantiations de chapitre : **`gru_mix_bound` + `gru_state_bound`** (`Ch08/Gru.lean#gru_bound`) — la porte de mise à jour du GRU est un mélange convexe, donc tout état caché de toute séquence reste borné (l'hypothèse `|n| ≤ M` est exactement le `tanh`, `0 ≤ z ≤ 1` est exactement le sigmoid) ; **`softmax_blend_bound`** (`Ch17/Contrastive.lean#softmax_blend`) — le blend d'attention sur valeurs bornées reste borné (le softmax est une distribution, `softmax_dist`). Le multi-têtes Ch09 avait déjà son round-trip (`concat_head`/`head_concat`). Docs FR/EN : ch08 (« La porte est un théorème » / « The gate is a theorem »), ch09 (fait 5, « quatre faits » → « cinq faits » FR/EN). **Round-trip convolution — RÉSOLU.** Nouveau bloc `cnn_row` dans `Ch06/Conv.lean` : `imgRow`/`kwin` relient la disposition plate du net (`K[c*9+a*3+b]`, `x[i*28+j]`) aux `Vec` typés ; `cnn_row` prouve que la cellule de colonne `j` du net égale terme à terme `conv1d (kwin K a) (imgRow x a) j` (le type-vérificateur impose $28-3+1=26$), et `cnn_cell_rows` identifie la double boucle complète à trois applications formelles de `conv1d` — le gabarit `concat_head` répliqué. Docs FR/EN ch06 (« La boucle à plat est la convolution » / « The flat loop *is* the convolution ») ; l'encadré d'honnêteté ch06 est mis à jour (cellule prouvée, pooling/dense toujours vérifiés numériquement).
- **M1 — PREMIER PONT `Rat`↔`Float` (budget d'arrondi).** Nouveau bloc dans `Core/Algebra.lean` : lois de la valeur absolue sur `Rat` exact (`abs_mul`, `abs_add_le`, `abs_nonneg`, `abs_le_one_of_interval`) puis **`drift_bound`** : si la dynamique exacte est non expansive (`|c| ≤ 1`) et que chaque pas de la trajectoire perturbée — celle de la machine — dévie de `|eₜ| ≤ ε`, alors `|vₜ − wₜ| ≤ t·ε` : l'erreur croît linéairement, jamais exponentiellement, tant que l'exact est stable. Instanciation SGD : `sgd_rounding_drift` dans `Ch05/Optim.lean` (plage stable `0 < ηa < 2`). C'est le pont demandé par le contrat — le `Float` n'a pas de loi exacte dans le noyau Lean, donc le pont honnête est un budget d'erreur paramétré, pas une égalité. Docs FR/EN ch05 (`abs_laws`, `drift_bound`, `sgd_spec`) ; audit : 1787 déclarations, `using sorry: []`.

### Avancement (même jour, après audit)

- **B1 — RÉSOLU.** `ci.yml` : `build-args` contient les 21 cibles ; smoke `lake exe ch05 && ch16 && ch17` ajouté (validé localement `SMOKE_EXIT=0`).
- **Mn1 — RÉSOLU.** `sq_nonneg` descendu dans `Core/Algebra` (namespace `LeanDL`) ; `Ch02.sq_nonneg` devient un alias d'une ligne, `Ch16/Tools` importe `Core/Algebra` et non plus Ch02.
- **Mn2 — RÉSOLU.** Nouveau `Core/Sum.lean` (`cnt`, `vsum`, `vsum_add`, `vsum_smul`, `vsum_zero`, `vsum_comm`) ; `Ch05/Norm`, `Ch06/Conv` et `Ch09/Attention` consomment Core ; l'arête `Ch09 → Ch06` a disparu.
- **Mn3 — RÉSOLU** (job smoke CI) et **Mn5 — RÉSOLU** (README : `npm run build && npm run serve` pour le bilingue, le piège `npm start`/FR y est documenté).
- Vérifications après ces corrections : `lake build` complet 180 jobs `EXIT=0` ; audit axiomes `using sorry: []; non-standard axioms: []` (1720 déclarations) ; `node scripts/check.mjs` → `OK: 21 pages…` exit 0.

---

**Verdict de la Phase 1** : le projet est structurellement sain — dépendances unidirectionnelles, zéro `sorry`, zéro axiome non standard sur 1720 déclarations (audit exécuté), documentation à parité mécaniquement vérifiée. Les écarts avec le contrat sont concentrés : un (B1) trivial, deux structurels (M1 pont Rat↔Float, M3 sémantique des couches flottantes) qui définissent le vrai chantier de formalisation, et un ensemble de rangements (Mn*) sans risque. Le MLP est déjà, à un chevron près (M2), le meilleur candidat pour le premier exemple F1→F5 complet demandé par la Phase 3.

---

## Phase 4 — Ch18 « Efficacité » (RÉSOLU)

Le contrat Phase 4 (MoE, quantification, distillation, scaling laws) est bouclé dans un nouveau chapitre **`Ch18/Efficiency.lean`**, prouvé sur `Rat` exact, sans Mathlib, sans `sorry` (audit : **1889 déclarations, `using sorry: []; non-standard axiomes: []`** après intégration) :

- **Quantification** : `quant` (plancher) avec `quant_le`/`quant_lt`/`quant_err_lt` (erreur < un pas de grille), `roundq` (au plus proche) avec `roundq_err_le` (≤ s/2, borne atteinte), `quant_quant` (idempotence — un modèle quantifié se re-sauve sans perte). Preuves via `Rat.floor_le`, `Rat.lt_floor_add_one`, `Rat.mul_le_mul_of_nonneg_right`, `Rat.inv_mul_cancel`, `push_cast; grind`.
- **MoE** : `balance_ge` — pour tout routeur (`p ≥ 0`, `Σp = 1`), `Σ pᵢ² ≥ 1/E`, preuve par somme de carrés `Σ (pᵢ − 1/E)² ≥ 0` développée avec `vsum_add`/`vsum_smul`/`vsum_const`/`vsum_nonneg` (nouveau bloc `RatLaws` dans `Core/Sum.lean`). `balance_collapse` — le routeur effondré `oneAt0` est une distribution (`vsum_oneAt0`, induction sur `Fin (E+1)`) et paie exactement `1 = E·(1/E)`.
- **Distillation** : héritée de `Core/Prob` — `distill_ge_entropy` (`CE(T,S) = H(T) + KL ≥ H(T)`, via `Dist.crossEntropy_eq_entropy_add_kl` + `Dist.kl_nonneg`) et `distill_teacher` (`CE(T,T) = H(T)`, plancher atteint via `Dist.kl_self`).
- **Scaling** : `inv_antitone` (via `Rat.inv_mul_cancel` + `Rat.lt_of_mul_lt_mul_right`), `data_scale` (`N < N' ⇒ C/N' < C/N`), `data_scale_double` (`C/2N = ½·C/N`, via `Rat.mul_inv`), `train_decay` (décroissance exponentielle `cᵗ·(L₀−L∞)` via les projections de `Ch05.powN_le_one`).
- **Exercices/corrigés** : 3 énoncés (`exercise_quant_mono`, `exercise_quant_translate`, `exercise_uniform_attains`) avec corrigés prouvés dans `Solutions.lean` (ancres `ex1..ex3`, `sol1..sol3`).
- **Démo exécutable** `lake exe ch18` (`Demos/Ch18.lean`, cible Lake ajoutée) : les quatre expériences `Float` reproduisent les quatre théorèmes (erreurs mesurées sous les bornes prouvées, uniforme = 1/E = 0.125, effondrement = 1.0, CE = H + KL au chiffre imprimé, distillation SGD 200 pas → KL = 0 ≥ H(T) vrai à chaque pas, chaque doublement de N divise l'excès par deux). Validée localement par `lake env lean --run Demos/Ch18.lean` (le `.exe` fraichement compilé est bloqué par le contrôle d'application Windows, comme `ch16` ; CI Linux exécute `lake exe ch18`).
- **Docs FR/EN paritaires** : `ch18-efficiency.mdx` (22 pages au `check.mjs`), ancres `quant`/`balance`/`distill`/`scaling` dans `Efficiency.lean` ; glossaires FR/EN, index FR/EN, README (cible `ch18`), ROADMAP (ligne Efficacité + Phase 4 « fait »), CI (`build-args` + smoke `ch18`).
- **`scripts/check.mjs`** : allow-list enrichie des tactiques noyau citées dans les pages (`exact_mod_cast`, `push_cast`, `norm_cast`, `funext`, `congr`, `rw`) — ce sont des tactiques de Lean 4 core, pas des noms LeanDL.

Limites honnêtes documentées dans la page : quantification scalaire seulement (clip/plage/calibrage = ingénierie) ; le routeur est un vecteur de poids, pas un réseau appris ; distillation sur distributions finies ; la loi d'échelle prouvée est la **forme** (`C/N` décroissant, moitiés), pas les coefficients empiriques.

---

## Phase 5 (partielle) — Ch10 : l'ELBO formalisé (RÉSOLU)

Le trou « la perte VAE est une borne inférieure de la log-vraisemblance, non prouvée » (signalé dans les docs Ch10 FR/EN) est comblé par **`Ch10/Elbo.lean`**, prouvé sur `Rat` exact, sans Mathlib, sans `sorry` :

- **`evidence_bound`** (ancre `elbo`) : pour une jointe finie `P` (poids `p(zᵢ,x) > 0`, non normalisée), un facteur de vraisemblance `e`, l'évidence `m = Σᵢ P.w i · e i = p(x)` et tout encodeur `q` : `q.expect (log e) − q.kl P ≤ log m`. Preuve : inégalité tangente `log t ≤ t − 1` (`LawfulLog.log_le`) appliquée aux poids d'importance `P.w i · e i · (q.w i)⁻¹ · m⁻¹ > 0`, monotonie du dot (`dot_mono`), développement exact du log (`LawfulLog.log_mul`/`log_inv`), puis l'annulation exacte `elbo_usum` (`Σ qᵢ·Pᵢeᵢ/qᵢ/m = (Σ Pᵢeᵢ)/m = 1` — sur `Rat`, `qᵢ·qᵢ⁻¹ = 1`, sans arrondi).
- **`elbo_gap`** : identité — la borne est exactement `−KL(q ‖ postérieure)` : `log m − (E_q[log e] − KL(q‖P)) = Σ qᵢ log(qᵢ / (Pᵢeᵢ/m))`. Développée via `dot_sub`/`dot_add_right`/`dot_smul_const` et `q.sum1`.
- **`elbo_gap_ge_zero`** : conséquence de Gibbs (`Dist.kl_nonneg q post`) — l'écart est `≥ 0`, zéro ssi l'encodeur est la postérieure. Le terme KL de la perte est le prix de l'approximation variationnelle, pas un régulariseur arbitraire.
- Lemmes utilitaires du fichier : `dot_congr` (annulation sous le dot par induction sur `Fin`), `dot_pos` (une évidence stricte est `> 0`), `elbo_usum`.
- Intégré dans `LeanDL.lean` ; build LeanDL 86 jobs `EXIT=0` ; audit : **1919 déclarations, `using sorry: []; non-standard axiomes: []`** ; docs FR/EN `ch10-vae.mdx` : la phrase « non formalisé ici » est remplacée par la section « The ELBO, proved / L'ELBO, prouvé » avec ancres `#elbo` et `#elbo_gap` ; `node scripts/check.mjs` → `OK: 22 pages… CHECK=0`.

Limite honnête : le chapitre 10 gaussien (continume) reste l'analogue continu ; le théorème prouvé couvre l'espace latent fini (identités en sommes finies) — c'est la signification exacte de la perte, la version à intégrales gaussiennes garde ses hypothèses déclarées.

## Phase 4.6 — Ch09 : le bloc Transformer assemblé et prouvé (RÉSOLU)

`lean/LeanDL/Ch09/Transformer.lean` assemble le bloc complet (layerNorm pré-norme,
attention multi-têtes causale avec projection de sortie sur la concaténation prouvée
`concat_head`/`head_concat`, FFN à activation abstraite `σ`, deux résiduelles) sur une
séquence typée `Mat α T d`, et démontre pour le bloc entier :

- `blockOut_no_leak` : si deux séquences coïncident sur les lignes `j ≤ t`, la sortie en
  `t` est identique — remontée de congruence (seqNorm, `causal_no_leak` par tête,
  concaténation, projection, résiduelle, FFN). C'est ce qui licence l'entraînement
  parallèle sur séquences entières.
- `blockOut_shift` : ajouter une constante à toute la séquence laisse la sortie inchangée
  (`layerNorm_shift` propagé ; la résiduelle ne récupère la constante qu'une fois).

Preuves sur corps exact `α` avec `HasAct`/`HasExp` ; la démo `gpt` calcule la même
structure en `Float`. Audit après intégration : 1928 déclarations, aucun `sorry` hors
Exercises, aucun axiome non standard. Docs FR/EN Ch09 complétées (ancre
`#transformer_props`).

## Phase 4.7 — Finitions du plan de correction (RÉSOLU)

- **Tests de propriétés** (`lean/Demos/Props.lean`, cible `props`, étape CI) : les théorèmes prouvés sont exercés sur des entrées pseudo-aléatoires à graine fixe. Vérifications `Rat` exactes via `decide` (forme fermée `sgdQuad` = `powN`, contraction `η·a ≤ 1` ; bornes `|x−quant| < s`, `|x−roundq| ≤ s/2` ; `Σp² ≥ 1/8`), miroirs `Float` avec tolérances (softmax, layerNorm mean0/var1/invariance au décalage, lignes d'attention causales `j > t` invisibles) via les aides natives `Float.beq`/`Float.abs` — jamais de `Decidable` sur des propositions `Float` (réduction runtime à `sorry`). 6/6 PASS en local.
- **Allow-list `check.mjs`** externalisée dans `scripts/tactic-allowlist.json` (édition sans toucher au script).
- **Figures Ch18** calculées par le Lean lui-même (`lake exe figures`) : `quantization.svg` (dents de scie plancher vs arrondi — les deux profils des bornes prouvées) et `moe_balance.svg` (`E·Σp²` selon le biais du routeur, départ au plancher prouvé 1) ; insérées dans les pages FR/EN.
- **Exercices Ch18 4-5** : `exercise_pow_add` (loi de puissance multiplicative — le socle algébrique des lois d'échelle) et `exercise_distill_gap` (l'écart de distillation est *exactement* le KL), corrigés prouvés (`sol4`, `sol5`), docs FR/EN appariées (liste, ancres, indices, corrigés).

Vérifications : `lake build` 87 jobs ; audit `checked 1933 declarations; using sorry: []; non-standard axioms: []` ; `lake exe props` 6/6 PASS ; `node scripts/check.mjs` 22 pages FR/EN.


## Phase 5.5 — Ch17 : le couple apparié en forme fermée (RÉSOLU)

- **`matched hi lo`** (1 positif, 1 négative) : InfoNCE se replie en fonction élémentaire de l'écart de similarité.
- **`matched_mass`** : masse softmax du positif = `1/(1+exp(lo-hi))` exactement (sigmoïde de l'écart) — courbe d'accuracy de tout papier contrastif.
- **`matched_loss`** : perte = `log(1+exp(lo-hi))` (softplus de l'écart négatif) — la température et l'échelle des scores sont le même bouton.
- **`matched_equal`** : `hi = lo` (modèle aveugle) donne exactement `log 2` et masse `1/2`.
- **`matched_mono`** : la perte décroît quand l'écart croît — sous hypothèse `hmono` NOMMÉE (monotonie de `exp` : propriété analytique de l'exponentielle réelle, non dérivable des seules lois `exp_add`/`exp_zero` — tout morphisme `(Q,+)→(Q\{0},·)` satisfait ces lois ; les morphismes sauvages rendent `exp` décroissante). Frontière honnête de la couche algébrique.
- **`log_mono` dérivé** (log croissant sur les positifs) depuis la borne tangente `log t ≤ t-1` appliquée au rapport `x/y` via `log_div` — aucun nouvel axiome. Helpers `div_le_one_of_le`, `div_pos'` en `Core`-style dans `RatLaws` de Ch17.

Verifications : `lake build LeanDL` 87 jobs ; audit `checked 1987 declarations; using sorry: []; non-standard axioms: []` ; `node scripts/check.mjs` 22 pages ; `npm run build` embarque `matched_mass`/`matched_loss` FR et EN.


## Phase 6a — Infrastructure partielle (RÉSOLU)

- **Item 2 (passe arrière sur tableaux, correction prouvée) : clos de fait.** `Ch04/Correct.lean` contient déjà `back_spec` (invariant du balayage : taille préservée, la coordonnée `j` gagne `s * (e.deriv j).eval x`), `backprop_correct` (`backprop` = gradient formel évalué) et `forward_eq_dot_backprop` (mode direct = `dot dx (grad e)`). Le "chantier le plus lourd" du Roadmap était donc déjà payé — le Roadmap ne le disait pas.
- **Item 3 (gabarit pédagogique) : clos.** `scripts/check.mjs` règle 7 : chaque page de chapitre EN embarque ≥ 4 ancres Lean ; chaque page EN a `## Exercises`, chaque page FR a `## Exercices`. Test négatif vérifié (section supprimée => check rouge, restaurée => vert).
- **Item 1 (tenseur générique) : reste ouvert** — dernier gros chantier identifié.

Verifications : `check.mjs` vert 22 pages ; build 87 jobs ; audit 1987 déclarations propres.


## Phase 6b — Tenseur générique (RÉSOLU)

- `lean/LeanDL/Core/Tensor.lean` (nouveau, couche Core) : `Tensor α m n := Fin (m*n) → α` — forme dans le type, stockage à plat ligne par ligne, le layout réel des librairies.
- Pont prouvé avec la couche formelle : `row`/`col`/`unflat` (arithmétique `div`/`mod` des strides, `row_unflat`, `col_unflat`), `toMat`/`fromMat` inverseux (`toMat_fromMat`, `fromMat_toMat` — `Nat.div_add_mod`), `flatMulVec_eq` : la boucle à plat d'une couche dense EST le `Mat.mulVec` prouvé, entrée par entrée.
- Pièges d'API rencontrés et règle : `Nat.div_lt_of_lt_mul`/`Nat.mod_lt` attendent `i.val < n * m` (multiplication dans l'ordre `n * m`), la unification désunifie les paramètres implicites de `row`/`col` — les passer en paramètres EXPLICITES ; `Nat.add_mul_mod_self` n'existe pas, c'est `Nat.add_mul_mod_self_right : (x + y * z) % z = x % z` ; `Nat.add_mul_div_left` réduit `(j + n*i)/n` (forme `n * i`, pas `i * n`).
- Exécutable : property test `prop_tensor` dans `Demos/Props.lean` — 300 tenseurs Rat exacts, `flatMulVec == Mat.mulVec` sur chaque sortie + round-trip cellule par cellule, 7/7 PASS.
- Docs FR/EN : section « Des formes vérifiées aux tenseurs à plat » dans la page Ch03 (la forme typée y est introduite).

Verifications : build 88 jobs ; audit **2007 déclarations propres** (0 sorry, 0 axiome non standard) ; `lake exe props` 7/7 PASS ; `check.mjs` 22 pages. Phase 6 ENTIÈREMENT close.


## Phase 7 — Frontières Float sans Mathlib (RÉSOLU)

**(a) Monotonie de `exp` : la frontière analytique nommée.**
- `Core/Algebra.lean` : `class MonotoneExp {α} [LE α] [HasExp α] : Prop` avec `exp_mono : a ≤ b → exp a ≤ exp b`. La doc explique pourquoi ce n'EST PAS une loi algébrique : tout morphisme de groupes `(Q,+) → (Q\{0},·)` satisfait `exp_add`/`exp_zero`, et des morphismes sauvages rendent `exp` décroissante. La monotonie est la propriété ANALYTIQUE de l'exponentielle réelle, déclarée une fois pour toutes dans la classe.
- Ch17 : `matched_mono` prend l'hypothèse de monotonie via `[MonotoneExp (α := Rat)]` (l'implicite `α` exige l'annotation), Solutions/Exercises alignés, docs FR/EN réécrites honnêtement.
- Piège évité : ne PAS mettre la monotonie dans `LawfulExp` — l'environnement sans Mathlib n'expose pas `LinearOrder` utilisable comme contrainte ; `[LE α]` suffit pour `a ≤ b`.

**(b) `Core/Interval.lean` : arithmétique d'intervalles certifiée sur `Rat`.**
- `structure Interval {lo hi : Rat}` (bornes EXACTES), `Mem`, inclusion `⊆`.
- Opérations + théorèmes d'encadrement tout `grind` : `add_spec`, `neg_spec`, `sub_spec` ; `mul_spec` par la **règle des quatre coins** (`box_max`, `box_min`, construits avec les lemmes de monotonie signés `Rat.mul_le_mul_of_nonneg_*` et les helpers nonpos dérivés par négation) ; `inv_le_inv_core` (multiplier par `(x·y)⁻¹ ≥ 0`), `invPos_spec`, `divPos_spec`, `widen_spec` (marge d'arrondi en `Rat` exact).
- Certificats fermés vérifiés par `grind`. Pièges d'API : `decide` ne réduit PAS `Rat.mul` au kernel (constructeurs intelligents avec normalisation gcd) — `grind` le fait via sa normalisation de corps ; `grind` ne déplie pas les projections de structure — les certificats passent par `show` (formes littérales) ; trop de coins en dénominateurs sous `show` provoque un timeout `isDefEq` (200 000 heartbeats) — rester sur des entiers/petits rationnels.
- Le piège de DÉPENDANCE est documenté par l'exemple : `x - x = 0` pour tout `x`, mais `I - I` a DOUBLE largeur — l'encadrement est son, jamais exact.
- `native_decide` reste interdit par `check.mjs` (règle 4) : tout est `grind`.
- Docs FR/EN : section « Certified intervals / Intervalles certifiés » dans Ch05, après l'encadré « What the hand-coded training is not » — le pont entre la démo Float sans garantie et le fait rationnel vérifiable.

Verifications : build **89 jobs** ; audit **2084 déclarations propres** (0 sorry, 0 axiome non standard) ; `check.mjs` 22 pages ; build website FR/EN OK.

## Phase I — Illustrations massives (RÉSOLU)

Objectif : rendre le cours compréhensible par l’image. 13 nouvelles figures, avec parité FR/EN stricte.

- **Courbes générées par Lean** (`lake exe figures`, `Demos/Figures.lean`, primitives `Core/Plot.lean`) :
  `chain_stack` (vanishing gradients), `lr_stability` (falaise d’apprentissage SGD), `infonce_floor`
  (plancher log N, effondrement), `entropy_coin` (entropie binaire), `kl_asymmetry` (KL non symétrique),
  `softmax_sharp` (température), `float_drift` (dérive accumulée Float, visualisée à l’échelle des ulps
  en unités 1e-12), `matched_gap` (loss appariée, plancher log 2 du modèle aveugle).
- **Schémas statiques** : `tensor_layout` (la matrice EST son buffer plat row-major, pont `Core/Tensor`),
  `interval_arith` (encadrements add/mul de `Core/Interval`), `dependency_gap` (X − X a double largeur,
  x − x = 0), `four_corners` (règle des quatre coins de `mul_spec`).
- **QA visuel** rendu dans un navigateur (les modèles de vision ne lisent pas les SVG) : a détecté et fait
  corriger l’axe Y dégénéré de `float_drift` et deux légendes tronquées.
- **Parité** vérifiée par script : chaque figure est référencée dans la page EN et la page FR.

Vérification : build 89 jobs ; audit 2084 déclarations propres (0 `sorry`, 0 axiome non standard) ;
`check.mjs` 22 pages vertes ; `npm run build` website vert.

## Phase I2 — Illustrations salve 2 (RÉSOLU)

9 figures supplémentaires (Ch02, Ch03, Ch04, Ch06, Ch07, Ch08, Ch09, Ch10, Ch13), toutes générées par Lean via `lake exe figures` et insérées FR/EN par `<Figure>`. QA visuel par rendu navigateur : `xor_points` passé en lieux géométriques (lineSvg relie les points, un nuage de 2 points devient une ligne), titre `elbo_parts` raccourci (troncature à droite). Vérifications : build 89 jobs, audit 2084 déclarations propres (0 sorry, 0 axiome non standard), `check.mjs` 22 pages. Site : 43 SVG.


## Phase I3 — Illustrations salve 3 (RÉSOLU)

9 figures supplémentaires (Ch01, Ch05, Ch11, Ch14, Ch15, Ch16, Ch17, Ch18), toutes générées par Lean via `lake exe figures` et insérées FR/EN par `<Figure>`. QA visuel par rendu navigateur : six titres tronqués à droite ont été raccourcis (mode_collapse, weight_decay, dream_drift, spread_collapse, infonce_mass, quant_grid, sigmoid_deriv). Vérifications : build 89 jobs, audit 2084 déclarations propres (0 sorry, 0 axiome non standard), `check.mjs` 22 pages. Site : 52 SVG.


## Phase I4 — Illustrations salve 4 (RÉSOLU)

8 figures supplémentaires (Ch01, Ch03, Ch04, Ch06, Ch07, Ch08, Ch09, Ch10), générées par Lean et insérées FR/EN. Fix infrastructure : `Core/Plot.lean` échappe le XML (`esc` sur `&`, `<`, `>` dans titres, axes, légendes) — découvert par QA navigateur : `cell_hold.svg` était invalide (le `<` nu de « `f < 1` » tronquait le titre à la ligne 16). Légende `mlp_stairs` raccourcie après troncature. Toutes les figures regénées. Vérifications : build 89 jobs, audit 2085 déclarations propres (0 sorry, 0 axiome non standard), `check.mjs` 22 pages. Site : 60 SVG.


## Phase I5 — Illustrations salve 5 (RÉSOLU)

9 figures supplémentaires (Ch02, Ch05, Ch11, Ch12, Ch13, Ch14, Ch15, Ch16, Ch17) : toutes les pages de chapitre ont désormais au moins 3 figures, Ch18 en a 4. QA navigateur/vision : 5 figures corrigées après troncature de titre ou courbe hors cadre (`perceptron_bound` rééquilibré en x ∈ [0.14, 1] pour que 1/γ² tienne sous 60, `snr_decay` en y ∈ [0, 12] pour que le pic SNR ≈ 11.5 tienne, `nce_temp` en y ∈ [0, 1.5], `planning_horizon` rebalisé en 0.1·1.25ᵏ vs 0.25k pour rendre le croisement visible vers k = 17, légendes et captions FR/EN alignées dessus). Vérifications : build 89 jobs, audit 2085 déclarations propres (0 sorry, 0 axiome non standard), `check.mjs` 22 pages. Site : 69 SVG.



## Phase U — Cours ultime : vitrine, kit, théorie (RÉSOLU)

**Vitrine** : `LICENSE` = texte officiel EUPL-1.2 (SPDX, anglais) + en-tête de copyright — l'UEPL n'a pas de version 2 officielle, v1.2 est la dernière ; lien EUR-Lex pour le texte français authentique. README complété (table Ch18, section licence, garanties CI). Recherche locale FR/EN sur le site (`@easyops-cn/docusaurus-search-local`, index `search-index.json` EN + FR).

**Kit d'entraînement (Ch05, `Kit.lean`)** : attente exacte du dropout (`drop_exp`), clipping par morceaux signé et borné (`clip`, `clip_align`, `clip_bounded`), AdamW vs L2 couplé (`decay_sgd_eq`), premier pas Adam sans biais (`adam_first_step_unbiased`), variance d'une mise à l'échelle (`var_smul` — le lemme derrière Xavier/He), somme géométrique finie et budget LR (`geom_sum`, `lr_decay_total`). Exercices 3-4 + solutions prouvées, docs FR/EN.

**Théorie de l'apprentissage (`Core/Theory.lean`)** : trois atomes exacts sur `Rat` — (1) atome de l'union bornée : à poids positifs l'espérance domine chaque terme pondéré (`dot_nonneg`, `dot_ge_head`), c'est exactement l'inégalité itérée de toute borne de généralisation à classe finie ; (2) symétrie train=test : sous la pièce équitable l'espérance est la moyenne (`coin`, `coin_expect_avg`) — le nombre est identique des deux côtés tant que l'hypothèse est indépendante du point, l'écart est créé par l'ajustement ; (3) No Free Lunch : sous étiquettes uniformes toute prédiction — déterministe (`nfl_coin`) ou randomisée (`nfl_coin_mix`) — a une erreur 0-1 espérée exactement 1/2. Les traductions Hoeffding/Chernoff sont signalées comme pas analytique sur `exp`, jamais masquées. Docs FR/EN dans Ch16 (« Théorie de l'apprentissage : les trois atomes »), exercices 6-7 + solutions prouvées.

Vérifications : build 91 jobs, audit 2184 déclarations propres (0 `sorry` hors Exercices, 0 axiome non standard), `check.mjs` 22 pages FR/EN, ancres résolues.
