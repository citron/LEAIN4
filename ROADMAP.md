# LEAIN4 — audit et plan d'amélioration

État : audit terminé, **plan à valider** avant toute restructuration (le cahier des charges demande de travailler de façon incrémentale après validation). La phase 0 ci-dessous est déjà réalisée.

## 1. Audit

**Compilation et vérifications (mesurées)**

- `lake build` de la bibliothèque et des 17 exécutables : 156 tâches, aucune erreur, aucun avertissement hors `sorry` des fichiers d'exercices.
- `scripts/audit_axioms.lean` : 1 476 déclarations, aucun `sorry`, aucun axiome autre que `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/check.mjs` : parité FR/EN, ancres Lean, noms cités, absence de `sorry` hors exercices, imports de la racine, SVG bien formés.
- Les 17 exécutables tournent sans erreur (paramètres réduits pour les plus longs).

**Ce qui est démontré, ce qui est seulement testé**

- Démontré (≈ 120 théorèmes) : propriétés des abstractions, correction de l'autodiff (modes direct et inverse), gradients de CNN-1D, RNN et cellule LSTM à une dimension, propriétés d'attention, borne d'erreur des rollouts imaginés, effondrement de JEPA, etc.
- Seulement vérifié par différences finies : les passes arrière écrites à la main sur tableaux (CNN 2D, RNN à n unités, LSTM, mini-GPT).
- Non modélisé : arrondis de `Float` ; la table des dérivées d'`Expr` est une *définition* (le lien avec la vraie dérivée réelle n'est pas démontré, faute d'analyse réelle sans Mathlib).
- Résultats expérimentaux : une graine, jeux-jouets. Les échecs sont rapportés (LSTM ne bat pas le RNN sur notre tâche, GAN instable, régularisateur de variance de poids 5 détourné par les distracteurs).

**Prérequis implicites repérés**

| Chapitre | Prérequis supposé mais non enseigné |
|---|---|
| 3-4 | dérivée, règle de la chaîne, dérivées usuelles ; produit matrice-vecteur |
| 5 | probabilités élémentaires, logarithme, exponentielle, espérance |
| 6-8 | sommes indexées, suites géométriques, majoration de produits |
| 9-10 | distribution de probabilité, loi normale, divergence KL |
| 11-12 | densités, somme de variables gaussiennes indépendantes |
| 13-14 | espérance, processus de décision markovien, constante de Lipschitz |
| 15 | variance, covariance, plongements |

**Lacunes par rapport au programme cible**

| Thème | État |
|---|---|
| Fondements mathématiques (algèbre linéaire, analyse, probabilités, statistiques, information) | absents : seulement des rappels épars ; `Mat.mul` et ses lois ajoutés |
| Perceptron, MLP, activations, pertes, descente de gradient, rétropropagation, autodiff | couverts (Ch 1-5) |
| Optimisation stochastique, régularisation | couverts ; **généralisation** : décomposition biais-variance démontrée sur distributions finies (Ch16, `ensemble_risk_decomp`) + démo numérique ; pas de théorie asymptotique (hors périmètre, analyse) |
| CNN, RNN, LSTM, GRU | couverts ; **GRU** implémenté (Ch08/Gru.lean, gradient vérifié 2·10⁻⁸, curriculum 100 % à T=10..40) |
| Attention, Transformers | couverts ; **attention multi-têtes implémentée** (layout démontré en `Ch09/Attention.lean` : `concat_head`/`head_concat`, bloc exécutable `Demos/MHead.lean`, gradient vérifié 0.000000) ; empilement de blocs décrit, non implémenté |
| Autoencodeurs, VAE, GAN, diffusion | couverts |
| Apprentissage contrastif et auto-supervisé | couverts ; **InfoNCE formalisé** (Ch17) : softmax distribution (`softmax_dist`), perte ≥ 0 (`infoNce_ge_zero`), plancher d'effondrement `log (n+1)` exact (`infoNce_collapse`), gradient `p − onehot` hérité de `ceLoss_grad` (`infonce_grad`) ; démo `lake exe ch17` : effondrement → perte 0.24 < log 5, cosinus 1.00 |
| Efficacité (déploiement) | couverts ; **Ch18 formalisé** : quantification (`quant_le`/`quant_err_lt` : erreur < un pas ; `roundq_err_le` : ≤ s/2 ; `quant_quant` : idempotence), MoE (`balance_ge` : Σp² ≥ 1/E, `balance_collapse` : effondrement = 1 = E·(1/E)), distillation (`distill_ge_entropy` : CE = H + KL ≥ H, `distill_teacher` : plancher atteint), scaling laws (`data_scale` : strictement décroissant, `data_scale_double` : doubler divise par 2, `train_decay` : décroissance exponentielle) ; démo `lake exe ch18` |
| Apprentissage par renforcement | couvert (bandit, Q-learning, REINFORCE) ; MDP général non formalisé |
| World models, JEPA | couverts |
| Architectures multimodales | **absentes** |
| Mixture of Experts, quantification, distillation | **absents** |
| Scaling laws, limites théoriques | **absents** |
| Projets de synthèse | **absents** |
| Tenseur générique | absent : `Vec`/`Mat` indexés par `Fin`, tableaux `Float` pour l'exécution, deux mondes non reliés par preuve |

**Exigences pédagogiques (par chapitre)**

- Présents partout : intuition, implémentation, démonstrations, exemples exécutables, exercices.
- Corrigés : exercices Lean avec corrigé prouvé dans tous les chapitres 1-15 (ajoutés) ; indices et corrigés dépliables dans les pages (ajoutés dans cette phase).
- Incohérents : les chapitres 7, 8, 9, 15 n'avaient pas de « Coin Lean » (ajoutés) ; la section « limites et variantes » n'existe de façon explicite que dans environ la moitié des chapitres ; pas de section « problème » systématique ; les exercices en prose ne sont pas gradués.
- Autonomie : seules dépendances externes, l'installation de Lean/VS Code (inévitable) et une vidéo en Ch 1.

## 2. Programme cible proposé

| Partie | Chapitres |
|---|---|
| I Fondations | 0 Tour de Lean ; **M Outils mathématiques (nouveau)** |
| II Réseaux de neurones | 1 Neurone ; 2 Perceptron/XOR ; 3 MLP ; 4 Autodiff ; 5 Entraînement, MNIST ; **généralisation (nouveau, intégré au 5 ou séparé)** |
| III Données structurées | 6 CNN ; 7 RNN ; 8 LSTM **et GRU** ; 9 Transformer (**multi-têtes, bloc empilé**) |
| IV Génératifs | 10 VAE ; 11 GAN ; 12 Diffusion |
| V Représentations | **16 Contrastif et auto-supervisé (nouveau)** ; 15 JEPA ; **multimodal (nouveau)** |
| VI Décision | 13 RL ; 14 World models |
| VII Passage à l'échelle | **MoE, quantification, distillation (nouveau)** ; **scaling laws et limites (nouveau)** |
| VIII Synthèse | **3 projets : mini-GPT complet, pipeline MNIST de bout en bout, agent qui rêve** |

Le chapitre « Outils mathématiques » resterait sans Mathlib : lois de probabilité **finies** sur `Rat`, espérance, entropie, divergence KL, inégalité de Gibbs (KL ≥ 0), décomposition de l'entropie croisée, loi des grands nombres *non* traitée (hors de portée sans analyse), dérivées via l'autodiff déjà démontré.

Progression Lean proposée (chaque notion à son premier besoin) : types et fonctions (0-1) → structures et classes de types (1) → tactiques `decide`, `grind` (1-2) → types dépendants (3) → inductifs et récursion structurelle (4) → listes, `Fin`, sommes (5-6) → récursion sur `Nat` et hypothèses (7) → bornes sur `Rat` (8) → corps abstraits et permutations (9) → `if`, `split`, minimiseurs (15). À compléter pour les nouveaux chapitres (distributions finies, `Finset`-like par listes, inégalités).

## 3. Plan par phases (le projet reste compilable à chaque étape)

| Phase | Contenu | Critère d'acceptation |
|---|---|---|
| 0 (fait) | Audit ; corrigés et indices ; Coin Lean manquants ; graphe des prérequis ; ce plan | build, audit des axiomes et `check.mjs` verts |
| 1 (fait) | Chapitre 16 « Outils mathématiques » (Lean + FR/EN) : distributions finies sur `Rat`, espérance, variance, entropie, KL, Gibbs, CE = H + KL ; exécutable `lake exe ch16` (écart d'arrondi `Rat`/`Float` imprimé) ; 5 exercices + corrigés prouvés | build complet vert avec `ch16` ; théorèmes dont Gibbs et biais-variance ; exercices avec corrigés compilés |
| 2 | GRU implémenté (fait) ; généralisation : biais-variance démontré sur distributions finies, `ensemble_risk_decomp`, exercé dans `lake exe ch16` (fait) ; **multi-têtes d'attention implémentées** (layout prouvé `concat_head`/`head_concat`, bloc exécutable `lake exe mhead`, gradient 0.000000) (fait) | passes arrière vérifiées par différences finies ; propriétés démontrées |
| 3 | Apprentissage contrastif (InfoNCE) formalisé (fait) : Ch17 — softmax distribution, perte ≥ 0, plancher `log (n+1)`, gradient `p − onehot` ; 3 exercices + corrigés prouvés ; démo entraînée `lake exe ch17` (loss 1.61 → 0.24, cosinus 1.00). **Reste : réordonnancement de JEPA** (lire Ch15 après Ch17) et sonde linéaire |
| 4 (fait) | **Chapitre 18 « Efficacité »** : quantification exacte sur `Rat` (`quant`, `roundq`, -bornes d'erreur, idempotence), MoE (`balance_ge` par somme de carrés, `balance_collapse` exact), distillation (héritée de `Core/Prob` : `CE = H + KL`, `KL ≥ 0`), scaling (`inv_antitone`, `data_scale`, `data_scale_double`, `train_decay` via `powN_le_one`) ; 3 exercices + corrigés prouvés ; démo Float `lake exe ch18` | chaque propriété exacte séparée des mesures |
| 4.5 (fait) | **Ch10 : ELBO formalisé** (`Ch10/Elbo.lean`) — `evidence_bound` (borne inférieure de la log-vraisemblance, inégalité tangente + annulation exacte des poids d'importance sur `Rat`), `elbo_gap` (l'écart = KL vers la postérieure), `elbo_gap_ge_zero` (Gibbs) ; docs FR/EN complétées (sections « The ELBO, proved » / « L'ELBO, prouvé », ancres `#elbo`, `#elbo_gap`) | audit 1919 déclarations propres ; build 86 jobs ; `check.mjs` 22 pages |
| 4.6 (fait) | **Ch09 : bloc Transformer assemblé et prouvé** (`Ch09/Transformer.lean`) — `blockOut` (pré-norme + multi-têtes causales + FFN + résiduelles, formes dans le type `Mat α T d`) ; `blockOut_no_leak` (aucune fuite du futur pour le bloc entier, remontée de congruence depuis `causal_no_leak`), `blockOut_shift` (invariance par décalage global, via `layerNorm_shift`) ; docs FR/EN (« The block, assembled and proved » / « Le bloc, assemblé et prouvé », ancres `#transformer_props`) | audit 1928 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 4.7 (fait) | **Finitions du plan** — tests de propriétés exécutables `lake exe props` (checks `Rat` exacts via `decide` + miroirs `Float` tolérants, 6/6 PASS, intégrés CI) ; allow-list de tactiques de `check.mjs` externalisée en `scripts/tactic-allowlist.json` ; figures Ch18 générées par `lake exe figures` (`quantization.svg`, `moe_balance.svg`) et insérées FR/EN ; exercices Ch18 4-5 (loi de puissance multiplicative, écart de distillation = KL exact) avec corrigés prouvés | audit 1933 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5.1 (fait) | **Ch11 : effondrement de modes prouvé** (`Ch11/Gan.lean`, section `TwoModes`) — jouet à deux modes : `collapseReward` vs `coverReward`, `cover_simplify`, `mode_collapse_reward` (couvrir bat strictement s'effondrer, via `inv_antitone` de Ch18 — squelette algébrique de tout argument d'effondrement) ; docs FR/EN (« Mode collapse, proved » / « L'effondrement de modes, prouvé », ancre `#collapse`) | audit 1941 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5.2 (fait) | **Ch12 : monotonie du processus direct prouvée** (`Ch12/Diffusion.lean`) — `cumA_nonneg` et `noise_monotone` : ajouter un pas VP `(a,s)` avec `0 ≤ a ≤ 1` ne diminue jamais la variance de bruit des données propres (`1 − ā² ≤ 1 − (ā·a)²`) ; la conception du planning (α_t décroissant) est un théorème de l'algèbre des pas, pas un axiome ; docs FR/EN avec frontière d'honnêteté (pas de théorie de la mesure gaussienne) | audit 1946 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5.3 (fait) | **Ch13 : TD itéré à convergence géométrique exacte** (`Ch13/Rl.lean`) — `tdIter` + `tdIter_error` : `k` mises à jour TD contre cible fixe multiplient l'erreur par `(1-η)ᵏ` exactement (composition de `tdUpdate_error` par récurrence) ; docs FR/EN avec frontière d'honnêteté (convergence stochastique hors périmètre) | audit 1956 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5.4 (fait) | **Ch18 : plancher de balancing pour la matrice de routage complète** (`Ch18/Efficiency.lean`) — `frac` (fraction de tokens par expert), `frac_sum` (normalisation par token + `vsum_comm` → `Σᵢ fᵢ = 1`), `balancing_ge` : la perte auxiliaire `E · Σᵢ fᵢ² ≥ 1` pour TOUT routeur (le plancher `balance_ge` survit au cas batch réel) ; docs FR/EN (« The floor survives the full router matrix ») | audit 1962 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5.5 (fait) | **Ch17 : le couple apparié en forme fermée** (`Ch17/Contrastive.lean`) — `matched hi lo` (1 positif, 1 négative) : `matched_mass` prouve que la masse softmax du positif vaut exactement `1/(1+exp(lo-hi))` (la sigmoïde de l'écart de similarité), `matched_loss` que la perte est `log(1+exp(lo-hi))` (softplus de l'écart), `matched_equal` que l'aveuglement coûte exactement `log 2`, `matched_mono` que la perte décroît avec l'écart — avec l'hypothèse de monotonie de `exp` NOMMÉE (frontière analytique honnête : les lois algébriques seules ne suffisent pas) ; dérivation de `log_mono` (log croissant) depuis la borne tangente, sans nouvel axiome ; helpers `div_le_one_of_le`/`div_pos'` en `RatLaws` ; docs FR/EN (« The matched pair, in closed form ») | audit 1987 déclarations propres ; build 87 jobs ; `check.mjs` 22 pages |
| 5 | Multimodal (deux modalités jouets alignées) ; projets de synthèse | projets exécutables de bout en bout |
| 6 | Infrastructure : tenseur générique ; passe arrière sur tableaux avec preuve de correction (ou vérification systématique) ; script qui exige les sections du gabarit pédagogique dans chaque chapitre | `check.mjs` étendu |

## 4. Questions à valider

1. Numérotation : **tranché (phase 1)** — nouveaux chapitres ajoutés à la suite (16 et plus), pas de renumérotation ; le graphe des prérequis renvoie Ch16 depuis les chapitres 3, 5, 9, 10, 11, 13.
2. Outils mathématiques : **tranché (phase 1)** — distributions finies sur `Rat`, logarithme abstrait à lois nommées ; analyse réelle explicitement hors périmètre, écart `Rat`/`Float` affiché par la démo.
3. Ordre de priorité des phases 1 à 5.
4. Phase 6 (correction prouvée des passes arrière sur tableaux) : à lancer, sachant que c'est le chantier le plus lourd et que les tests par différences finies actuels couvrent déjà le besoin pratique ?
5. Les performances (GPU, gros modèles) restent hors périmètre : confirmé ?
