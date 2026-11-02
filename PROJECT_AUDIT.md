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
- **M3 — PREMIERES INSTANTIATIONS ARCHITECTURES (noyau convexe).** Noyau commun prouvé en Core : **`Dist.convex_bound`** (`Core/Prob.lean`) — une combinaison convexe (`w ≥ 0`, `Σw = 1`) de valeurs dans `[-M, M]` reste dans `[-M, M]`. Version séquentielle du drift : **`drift_bound_seq`** (`Core/Algebra.lean`) — facteur par pas `c t` avec `|c t| ≤ 1`, budget linéaire `t·ε` (les portes GRU varient pas à pas, le facteur constant de M1 ne suffit plus). Instantiations de chapitre : **`gru_mix_bound` + `gru_state_bound`** (`Ch08/Gru.lean#gru_bound`) — la porte de mise à jour du GRU est un mélange convexe, donc tout état caché de toute séquence reste borné (l'hypothèse `|n| ≤ M` est exactement le `tanh`, `0 ≤ z ≤ 1` est exactement le sigmoid) ; **`softmax_blend_bound`** (`Ch17/Contrastive.lean#softmax_blend`) — le blend d'attention sur valeurs bornées reste borné (le softmax est une distribution, `softmax_dist`). Le multi-têtes Ch09 avait déjà son round-trip (`concat_head`/`head_concat`). Docs FR/EN : ch08 (« La porte est un théorème » / « The gate is a theorem »), ch09 (fait 5, « quatre faits » → « cinq faits » FR/EN). Reste pour M3 : round-trip layout convolution (`gabarit concat_head`).
- **M1 — PREMIER PONT `Rat`↔`Float` (budget d'arrondi).** Nouveau bloc dans `Core/Algebra.lean` : lois de la valeur absolue sur `Rat` exact (`abs_mul`, `abs_add_le`, `abs_nonneg`, `abs_le_one_of_interval`) puis **`drift_bound`** : si la dynamique exacte est non expansive (`|c| ≤ 1`) et que chaque pas de la trajectoire perturbée — celle de la machine — dévie de `|eₜ| ≤ ε`, alors `|vₜ − wₜ| ≤ t·ε` : l'erreur croît linéairement, jamais exponentiellement, tant que l'exact est stable. Instanciation SGD : `sgd_rounding_drift` dans `Ch05/Optim.lean` (plage stable `0 < ηa < 2`). C'est le pont demandé par le contrat — le `Float` n'a pas de loi exacte dans le noyau Lean, donc le pont honnête est un budget d'erreur paramétré, pas une égalité. Docs FR/EN ch05 (`abs_laws`, `drift_bound`, `sgd_spec`) ; audit : 1787 déclarations, `using sorry: []`.

### Avancement (même jour, après audit)

- **B1 — RÉSOLU.** `ci.yml` : `build-args` contient les 21 cibles ; smoke `lake exe ch05 && ch16 && ch17` ajouté (validé localement `SMOKE_EXIT=0`).
- **Mn1 — RÉSOLU.** `sq_nonneg` descendu dans `Core/Algebra` (namespace `LeanDL`) ; `Ch02.sq_nonneg` devient un alias d'une ligne, `Ch16/Tools` importe `Core/Algebra` et non plus Ch02.
- **Mn2 — RÉSOLU.** Nouveau `Core/Sum.lean` (`cnt`, `vsum`, `vsum_add`, `vsum_smul`, `vsum_zero`, `vsum_comm`) ; `Ch05/Norm`, `Ch06/Conv` et `Ch09/Attention` consomment Core ; l'arête `Ch09 → Ch06` a disparu.
- **Mn3 — RÉSOLU** (job smoke CI) et **Mn5 — RÉSOLU** (README : `npm run build && npm run serve` pour le bilingue, le piège `npm start`/FR y est documenté).
- Vérifications après ces corrections : `lake build` complet 180 jobs `EXIT=0` ; audit axiomes `using sorry: []; non-standard axioms: []` (1720 déclarations) ; `node scripts/check.mjs` → `OK: 21 pages…` exit 0.

---

**Verdict de la Phase 1** : le projet est structurellement sain — dépendances unidirectionnelles, zéro `sorry`, zéro axiome non standard sur 1720 déclarations (audit exécuté), documentation à parité mécaniquement vérifiée. Les écarts avec le contrat sont concentrés : un (B1) trivial, deux structurels (M1 pont Rat↔Float, M3 sémantique des couches flottantes) qui définissent le vrai chantier de formalisation, et un ensemble de rangements (Mn*) sans risque. Le MLP est déjà, à un chevron près (M2), le meilleur candidat pour le premier exemple F1→F5 complet demandé par la Phase 3.
