# LEAIN4 — état du projet

Document en quatre parties sans chevauchement : **état vérifié** (mesures du dépôt actuel), **travaux terminés**, **limites connues**, **prochaines tâches**. Une information historique n'est jamais présentée comme un état courant ; la chronologie détaillée vit dans l'historique Git.

## 1. État vérifié du dépôt

Mesures reproductibles sur la branche courante (commandes exactes) :

| Contrôle | Commande | Résultat mesuré |
|---|---|---|
| Bibliothèque + exercices résolus | `cd lean && lake build LeanDL` | 0 erreur ; seuls `sorry` = exercices déclarés dans les `Exercises.lean` |
| Toutes les cibles et exécutables | `lake build LeanDL ch01 ch02 ch03 ch04 ch05 mnist cnn rnn lstm gru gpt minigpt mhead vae gan diffusion rl bellman worldmodel jepa ch16 ch17 ch18 ch19 capstone figures` | vert (mêmes cibles que README et CI) |
| Audit des axiomes | `lake env lean ../scripts/audit_axioms.lean` | 2 770 déclarations vérifiées ; aucun `sorry` ; aucun axiome non standard |
| Consistance du site | `node scripts/check.mjs` | 27 pages FR/EN en parité, ancres Lean résolues, figures SVG bien formées, **couverture du syllabus** : chaque page de chapitre (position de navigation) a sa ligne dans le tableau d'accueil FR et EN |
| Fumée des exécutables | `lake exe <nom>` pour ch01…ch05, ch16…ch19, capstone, gru, mhead, gan, rl, bellman, minigpt, jepa | tous rc=0 (capstone ≈ 32 s, gan ≈ 47 s, le reste < 5 s) |
| CI | `.github/workflows/ci.yml` sur la branche | jobs `lean` + `website` ; Node 26, audit d'axiomes, tests de propriétés, MNIST de régression, build statique bilingue |

Licence : **EUPL-1.2** (`LICENSE`). Chaîne : Lean 4.35.0, sans Mathlib pour les modèles et les preuves. Site : Docusaurus 3.10.2, Node ≥ 20 (`.nvmrc` = 26).

Vocabulaire de statut utilisé partout dans le cours (contrat de preuve) :

- **Démontré formellement** — théorème Lean accepté, énoncé avec son domaine et ses hypothèses.
- **Démontré sous hypothèses nommées** — loi algébrique représentée par une classe (`LawfulLog`, `LawfulExp`, `MonotoneExp`) ou une hypothèse explicite ; la frontière analytique est déclarée, pas masquée.
- **Vérifié numériquement** — test exécutable, différences finies, invariant `Float` avec tolérance affichée.
- **Observé expérimentalement** — résultat d'entraînement, une graine sauf mention.
- **Simplifié / non modélisé** — aspect volontairement absent (nommé à l'endroit du résultat).

## 2. Travaux terminés (résumés ; le détail est dans `git log`)

- **Cœur** : arithmétique exacte sur `Rat`, `Vec`/`Mat`/`Tensor` (forme dans le type, stockage plat, `flatMulVec_eq`), autodiff direct/inverse prouvé correct (`backprop_correct`), arithmétique d'intervalles rationnels certifiée (`Core/Interval.lean`), classes de lois nommées (`LawfulLog`, `LawfulExp`, `MonotoneExp`).
- **Chapitres 0-15** : neurone → perceptron → MLP → autodiff → MNIST 96 % → CNN → RNN → LSTM/GRU → attention/Transformer (bloc assemblé, `blockOut_no_leak`, `blockOut_shift` ; **pile de blocs quelconque `stack_no_leak` par récurrence sur la liste** + mini-GPT empilé exécutable `minigpt`, backward chaîné à travers la pile certifié par différences finies sur tous les paramètres) → autoencodeur/VAE (ELBO prouvé : `evidence_bound`, `elbo_gap`) → **10.5 Boltzmann** (machine canonique 4 états : normalisation, conditionnelles de Gibbs, invariance de l'équilibre sous un balayage complet, forme d'énergie — tout en `Rat` exact) → GAN (discriminateur optimal, effondrement de modes prouvé sur le jouet) → diffusion (algèbre closed-form du processus, monotonie) → RL (Bellman un état, `tdIter_error` géométrique exact, REINFORCE bandit ; **MDP fini complet : contraction de Bellman en norme sup `cheb_le`, unicité `fixed_point_unique`, taux géométrique `vIter_rate`, démo exacte `bellman` en `Rat`**) → world models (borne de propagation d'erreur) → JEPA (effondrement minimiseur global, contraction EMA).
- **Chapitre 16** (outils) : distributions finies strictement positives sur `Rat`, espérance/variance, entropie, CE = H + KL, Gibbs KL ≥ 0, biais-variance (`ensemble_risk_decomp`), atomes de théorie d'apprentissage (algèbre de la borne d'union, base binaire sans information). Frontière `LawfulLog` affichée.
- **Chapitre 17** : InfoNCE exact (softmax distribution, perte ≥ 0, plancher `log (n+1)`, gradient `p − onehot`), couple apparié en forme fermée (softplus de l'écart, hypothèse de monotonie de `exp` nommée via `MonotoneExp`).
- **Chapitre 18** : quantification (bornes exactes sur scalaire et grille uniforme), MoE — **pénalité de concentration** `E · Σ fᵢ² ≥ 1` prouvée pour toute matrice de routage (`frac_sum`, `balancing_ge`) ; la distinction avec la loss Switch `E Σ fᵢ Pᵢ` est documentée (Fedus, Zoph & Shazeer 2021, arXiv:2101.03961) ; distillation `CE = H + KL` ; modèle illustratif d'échelle `L(N) = L∞ + C/N` (monotonie et doublement prouvés, posé comme modèle).
- **Chapitre 19** : CLIP symétrique (moyenne de deux InfoNCE, plancher partagé, bornes exactes, 5 000 batchs sans violation).
- **Chapitre 20 (capstone)** : recette decay + clipping + schedule ; `recipe_step_eq` (invisible dans la boîte), `recipe_closed` (forme fermée), `recipe_iter_sq_le` (le carré de la perte ne croît jamais — quadratique scalaire, taux constant), `recipe_budget` (budget de schedule fini). La page dit explicitement que ces preuves **scalaires** ne certifient pas le parcours **vectoriel** MNIST (compagnon exécutable ; une graine = démonstration, pas évaluation statistique).
- **Site** : 27 pages × FR/EN, parité structurelle automatisée, 69 figures data-driven générées par Lean (`lake exe figures`), 19 schémas d'architecture `arch_*.svg`, portraits de créateurs sous licence libre, recherche locale FR/EN, contrôle de couverture du syllabus dans `check.mjs`.
- **Relecture qualité (2026-11-09)** : pass systématique FR/EN piloté par LanguageTool (API publique, sans compte) + scanners maison (`scripts/lt_pass.py`, `scripts/scan_quality.py`) : accents restaurés dans le corps des phrases et les captions/alt de figures (~100 défauts ASCII), typographie FR (espace insécable avant `;:!?`) hors frontmatter/code/math, virgules d'introductions et de subordonnants ajoutées sur les contextes signalés, harmonisation EN (`optimizer`, `handwritten`, `hyperparameter`, `multimodal`, `afterward`, virgules). Le scan de qualité `scan_quality.py` remonte 0 défaut restant.
- **CI** : job `lean` (build complet, audit, propriétés, MNIST déterministe, fumée des 15 exécutables) + job `website` (`npm ci`, `check.mjs`, build statique), Node 26.

## 3. Limites connues (frontières assumées)

- **Analyse réelle hors périmètre** : pas de construction du log/exp réels ni de la dérivée comme limite (choix sans Mathlib) ; les lois sont portées par des classes nommées. Le lien entre la table de dérivées d'`Expr` et la dérivée réelle n'est pas démontré.
- **Float non certifié** : les propriétés IEEE-754 et la propagation des arrondis ne sont pas formalisées ; `Rat` porte les preuves, `Float` les expériences.
- **Probabilités finies et discrètes** : densités continues, lois gaussiennes générales et conventions `0 · log 0` / KL infini ne sont pas dans le modèle `Dist`.
- **Jouets explicites** : Boltzmann 4 états (pas de RBM réaliste, pas de temps de mélange), GAN deux modes (pas de théorie minimax), diffusion = algèbre des pas (pas de théorie de la mesure), RL = politique fixe (l'opérateur de Bellman sur MDP fini est prouvé contraction/point fixe/taux — la convergence stochastique de Q-learning, TD et SARSA reste hors périmètre), mini-GPT = empilé et entraîné (preuve de non-fuite de la pile ; entraînement sur petits corpus, pas d'échelle).
- **Quantification** : bornes sur un scalaire et une grille uniforme ; pas la certification d'un réseau quantifié complet (outliers, activations, accumulation entre couches).
- **Expériences** : une graine, jeux de données réduits ; les comparaisons multi-graines (moyenne ± dispersion) ne sont pas systématiques.
- **Scaling** : le modèle `L(N)=L∞+C/N` est posé, pas dérivé empiriquement ; les axes paramètres / tokens / calcul des scaling laws contemporaines ne sont pas distingués dans la preuve.

## 4. Prochaines tâches (par ordre de valeur)

1. **Projets de synthèse** : pipeline MNIST de bout en bout, mini-GPT, apprentissage de représentations (deux encodeurs + InfoNCE/CLIP + sonde linéaire) — cahier des charges, critères de réussite, grille séparant garanties prouvées et objectifs empiriques.
2. **Parcours de prérequis** : le module de préparation et les cartes de dépendances sont livrés (page `prerequisites`, bannières Ch05/10/11/13) ; reste à étendre les bannières aux autres chapitres lourds.
3. **Évaluation multi-graines hors CI** : benchmark séparé rapportant moyenne et dispersion ; la CI garde l'exécution déterministe comme test de non-régression.
4. **Fiches de preuve** : pour chaque résultat important, une fiche courte (énoncé, hypothèses, type numérique, code, validation, limites) — le contrat de statut de la section 1 est en place, les fiches restent à généraliser.
5. **Pont Rat ↔ Float** — livré : `Core/Rounding.lean` définit le modèle d'arrondi nommé (`RoundingModel : fl, u, |δ| ≤ u`, débordement/sous-débit exclus explicitement), prouve en général `k` la borne produit de Higham (`prod_one_add_delta : |∏(1+δᵢ) − 1| ≤ γₖ`) et la borne du produit scalaire arrondi (`flDot_error : |flDot − dot| ≤ γ₍₂ₙ₎ · Σ|xᵢyᵢ|`), étendue à une couche dense (`flMulVec_error`). L'instanciation binary64 (`u = 2⁻⁵³`) est une hypothèse de plateforme **« Vérifié numériquement »** — le test `prop_rounding_f` de `Props` mesure l'erreur flottante contre la borne prouvée ; Lean n'a pas de théorie IEEE-754. Reste à faire : faire de l'ε par pas de `drift_bound_seq` une conséquence de `u`. **IEEE-754 (livré)** : `Core/Ieee754.lean` spécifie la grille binaire par binade (structure nommée `Grid : pick, bound, nearest, fixed` — aucun `axiom`, aucun `native_decide` sur les bornes) et **prouve** la réduction `Grid → RoundingModel` avec `u = 2⁻ᵖ` (`toRoundingModel`) : l'hypothèse du T9 devient un théorème sur la grille. S'ajoutent l'idempotence sur le domaine (`idempotent`), la grille fixe `2⁻ᵖ·ℤ` et son arrondi constructif à un `floor` (`fixedGrid_fixed`), et les constantes binary64 calculées par `decide` (2⁵³, 2⁵², 2⁻⁵², 2⁻⁵³, demi-ulp). Ce qui n'est PAS prouvé : que le `Float` de la machine soit cette grille (hypothèse de plateforme, statut « Vérifié numériquement ») — signatures observées par `prop_ieee754` dans `Props` : `1 + 2⁻⁵³ == 1` (demi-ulp, égalité vers le pair), `1 + 2⁻⁵² ≠ 1`, `1 + 3·2⁻⁵³ == 1 + 2⁻⁵¹` (égalité vers le pair du haut), `0.1 + 0.2 ≠ 0.3`.
6. **Lien dérivée formelle ↔ différences finies** : développement exact du premier ordre pour le fragment polynomial de `Expr` (`eval e (x + h·eⱼ) = eval e x + h · deriv j e x + h² · R`), qui justifie les contrôles de gradient des démos.
7. **RL, opérateur d'optimalité** : Bellman avec `max` sur les actions, contraction, unicité de `V*`. La convergence stochastique (Q-learning/TD) reste hors périmètre.

## Questions closes (décisions appliquées)

- Numérotation : pas de renumérotation ; chapitres ajoutés à la suite ; Ch10.5 inséré entre VAE et GAN par `sidebar_position: 11.5`. — **appliqué**
- Outils mathématiques : distributions finies sur `Rat`, logarithme abstrait à lois nommées, analyse réelle hors périmètre. — **appliqué** (Ch16)
- GPU / gros modèles : hors périmètre. — **confirmé**
- UEPL « v2 » : n'existe pas ; licence retenue **EUPL-1.2**. — **appliqué**
- Correction prouvée des passes arrière sur tableaux : acquise en `Ch04/Correct.lean` (`backprop_correct`) ; les passes arrière sur `Array` (CNN 2D, RNN, LSTM, mini-GPT) restent vérifiées par différences finies. — **état documenté**
