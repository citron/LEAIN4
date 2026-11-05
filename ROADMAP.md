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
| 6a (fait) | **Phase 6 partielle** — item 2 clos de fait : la passe arrière sur tableaux est DÉJÀ prouvée correcte en `Ch04/Correct.lean` (`back_spec` : le balayage `Array` ajoute `s * ∂ⱼe` à la coordonnée `j`, taille préservée ; `backprop_correct` : `backprop` renvoie l'évaluation du gradient formel ; `forward_eq_dot_backprop` : mode direct = produit scalaire tangentiel) ; item 3 clos : `check.mjs` étendu (règle 7) — exige de chaque page de chapitre ≥ 4 ancres Lean embarquées et une section `## Exercises`/`## Exercices`, test négatif vérifié | build 87 jobs ; audit 1987 déclarations propres ; `check.mjs` 22 pages ; reste Phase 6 item 1 (tenseur générique) |
| 6b (fait) | **Phase 6 item 1 : tenseur générique** — `Core/Tensor.lean` : `Tensor α m n` = tenseur 2-D dont la FORME est dans le TYPE mais STOCKÉ À PLAT (`Fin (m*n) → α`, layout ligne par ligne comme les vraies librairies) ; `row`/`col`/`unflat` = l'arithmétique div/mod des strides, avec `row_unflat`/`col_unflat` prouvés ; `toMat`/`fromMat` inverseux (`toMat_fromMat`, `fromMat_toMat` via `Nat.div_add_mod`) ; `flatMulVec` = la boucle à plat d'une couche entièrement connectée, PROUVÉE égale au `Mat.mulVec` formel entrée par entrée (`flatMulVec_eq`) ; property test exécutable `prop_tensor` (300 tenseurs Rat exacts, PASS) ; docs FR/EN Ch03 « Des formes vérifiées aux tenseurs à plat » | build 88 jobs ; audit 2007 déclarations propres ; props 7/7 PASS ; `check.mjs` 22 pages |
| 7 (fait) | **Frontières Float sans Mathlib** — (a) monotonie de exp centralisée dans une classe nommée `MonotoneExp` (`Core/Algebra.lean`) : la frontière analytique est déclarée UNE fois, Ch17 l'instancie `[MonotoneExp (α := Rat)]` et `matched_mono` l'utilise via `MonotoneExp.exp_mono` ; (b) `Core/Interval.lean` : arithmétique d'intervalles rationnels CERTIFIÉE — `Interval {lo hi : Rat}`, `Mem`, add/neg/sub/mul/invPos/divPos/widen chacun avec son théorème d'encadrement (`add_spec`, `mul_spec` par la règle des quatre coins, `inv_le_inv_core`, etc.), certificats fermés vérifiés par `grind` (pas de `native_decide`), piège de dépendance I−I documenté ; docs FR/EN Ch05 « Intervalles certifiés » | build 89 jobs ; audit 2084 déclarations propres ; `check.mjs` 22 pages |
| I (fait) | **Illustrations massives du cours** — 13 nouvelles figures pour rendre chaque notion visible. Courbes générées par Lean (`lake exe figures`, `Demos/Figures.lean`, primitives `Core/Plot.lean`) : `chain_stack` (empilement des gradients, pire cas (1/4)^L vs typique), `lr_stability` (falaise de stabilité SGD), `infonce_floor` (plancher log N d’InfoNCE et effondrement), `entropy_coin` (entropie binaire, max en p=1/2), `kl_asymmetry` (KL(p,q) ≠ KL(q,p)), `softmax_sharp` (température), `float_drift` (dérive de 10 000 additions de 0.1, à l’échelle des ulps en unités 1e-12), `matched_gap` (loss appariée log(1+exp(lo-hi)) et plancher log 2). Schémas statiques : `tensor_layout` (la matrice EST son buffer plat row-major, k = i*n + j), `interval_arith` (encadrements add/mul), `dependency_gap` (X − X a double largeur), `four_corners` (règle des quatre coins de mul_spec). Insérées FR/EN via `<Figure>` avec QA visuel navigateur (axe float dégénéré et légendes tronquées corrigés) | 30 SVG dans `website/static/img/` ; build 89 jobs ; audit 2084 déclarations propres ; `check.mjs` 22 pages |
| I2 (fait) | **Illustrations salve 2** — 9 figures de plus pour les chapitres qui n’en avaient qu’une, toutes générées par Lean (`lake exe figures`) : `xor_points` (les deux classes du XOR sur les diagonales qui se croisent — aucune droite ne sépare), `relu_dead` (ReLU vivante max(0,x) vs unité morte plate à 0), `depth_signal` (log10 du gradient de couche 0 vs profondeur), `conv_window` (heatmap 8×8, la fenêtre 3×3 est un produit scalaire glissant), `rnn_chain` (log10 du gradient à travers T pas déroulés), `lstm_gates` (les quatre courbes f/i/tanh/f·c~), `attention_causal` (heatmap 6×6, triangle blanc = pas de fuite), `elbo_parts` (-log p(x) et KL(q‖p), les deux moitiés de l’ELBO), `td_bootstrap` (V(s_i)=0.5^i vers la vraie valeur 1). Insérées FR/EN via `<Figure>` ; QA visuel navigateur : xor_points repensé en lieux géométriques (lineSvg relie les points), titre elbo_parts raccourci | 43 SVG dans `website/static/img/` ; build 89 jobs ; audit 2084 déclarations propres ; `check.mjs` 22 pages |
| I3 (fait) | **Illustrations salve 3** — 9 figures pour les pages qui n'en avaient que deux, générées par Lean (`lake exe figures`) : `sigmoid_deriv` (cloche sigma(1-sigma), pic 1/4 — l'evanescence des gradients en germe), `weight_decay` (SGD sur (w-1)^2 : lam=1 se stabilise a 0.5), `mode_collapse` (couvrir les modes a/(a+0.5) strictement au-dessus de l'effondrement a/(a+1)), `dream_drift` (la borne de composition explose en L=1.2, sature en L=0.5), `spread_collapse` (dispersion JEPA 2d^2, nulle exactement a l'effondrement), `bias_var` (risque d'ensemble = biais^2 + variance/n, plancher plat), `infonce_mass` (masse sur le positif : aveugle 1/(n+1) vs ecart 2), `quant_grid` (dent de scie d'arrondi, borne +/-s/2 atteinte aux milieux), `scaling_shape` (train_decay : chute geometrique vers le plancher Linf). Inserees FR/EN via `<Figure>` dans Ch01, Ch05, Ch11, Ch14, Ch15, Ch16, Ch17, Ch18 ; QA visuel navigateur, six titres raccourcis apres troncature constatee | 52 SVG dans `website/static/img/` ; build 89 jobs ; audit 2084 declarations propres ; `check.mjs` 22 pages |
| I4 (fait) | **Illustrations salve 4** — 8 figures pour les pages restantes a 2 figures, generees par Lean : `neuron_halfplane` (le neurone est un demi-plan, la droite w.x = b), `mlp_stairs` (4 unites ReLU plient sin en segments droits), `fd_drift` (difference centrale de sin en Float : courbe en U, plancher a 2^-52 — le mur de l'epsilon machine), `rf_growth` (champ receptif 2L+1 des 3x3 empiles vs 5x5 plat), `lag_copy` (tache memoire y_t = x_(t-3), l'impulsion doit sortir 3 pas apres), `cell_hold` (etat de cellule f^t : f=1 plat, 0.95 lent, 0.5 effondrement RNN), `attn_sharp` (poids softmax de la cle dominante e^beta/(e^beta+3) vs 1/4 uniforme), `beta_vae` (distortion 1/(1+beta) vs taux beta/(1+beta)). Inserees FR/EN dans Ch01, Ch03, Ch04, Ch06, Ch07, Ch08, Ch09, Ch10. **Fix infrastructure** : `Core/Plot.lean` echappe desormais le XML (`esc` : & < >) dans tous les titres/axes/legendes — `cell_hold.svg` etait invalide (titre tronque par le `<` nu de `f < 1`) ; toutes les figures regerees | 60 SVG dans `website/static/img/` ; build 89 jobs ; audit 2085 declarations propres ; `check.mjs` 22 pages |
| 5 | Multimodal (deux modalités jouets alignées) ; projets de synthèse | projets exécutables de bout en bout |
| 6 | Infrastructure : tenseur générique ; passe arrière sur tableaux avec preuve de correction (ou vérification systématique) ; script qui exige les sections du gabarit pédagogique dans chaque chapitre | `check.mjs` étendu |

## 4. Questions à valider

1. Numérotation : **tranché (phase 1)** — nouveaux chapitres ajoutés à la suite (16 et plus), pas de renumérotation ; le graphe des prérequis renvoie Ch16 depuis les chapitres 3, 5, 9, 10, 11, 13.
2. Outils mathématiques : **tranché (phase 1)** — distributions finies sur `Rat`, logarithme abstrait à lois nommées ; analyse réelle explicitement hors périmètre, écart `Rat`/`Float` affiché par la démo.
3. Ordre de priorité des phases 1 à 5.
4. Phase 6 (correction prouvée des passes arrière sur tableaux) : à lancer, sachant que c'est le chantier le plus lourd et que les tests par différences finies actuels couvrent déjà le besoin pratique ?
5. Les performances (GPU, gros modèles) restent hors périmètre : confirmé ?
