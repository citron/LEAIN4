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
| Optimisation stochastique, régularisation | couverts ; **généralisation** limitée à « surapprentissage » (pas de décomposition biais-variance, pas de théorie) |
| CNN, RNN, LSTM | couverts ; **GRU** seulement esquissé, non implémenté |
| Attention, Transformers | couverts (une tête, un bloc) ; multi-têtes et empilement décrits, non implémentés |
| Autoencodeurs, VAE, GAN, diffusion | couverts |
| Apprentissage contrastif et auto-supervisé | **absent** (JEPA est traité sans son contexte) |
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
| 1 | Chapitre « Outils mathématiques » (Lean + FR/EN) ; recaps de prérequis liés depuis les chapitres 3, 5, 9, 10 | 6 théorèmes dont Gibbs ; exécutable ; exercices avec corrigés |
| 2 | GRU implémenté ; généralisation (biais-variance démontré sur distributions finies, expérience de surapprentissage) ; multi-têtes d'attention | passes arrière vérifiées par différences finies ; propriétés démontrées |
| 3 | Apprentissage contrastif (InfoNCE) puis réordonnancement de JEPA | expérience avec sonde linéaire ; théorèmes sur la perte |
| 4 | Passage à l'échelle : MoE (routage, équilibrage), quantification (borne d'erreur démontrée), distillation (température), scaling laws (régression en loi de puissance, limites) | chaque propriété exacte séparée des mesures |
| 5 | Multimodal (deux modalités jouets alignées) ; projets de synthèse | projets exécutables de bout en bout |
| 6 | Infrastructure : tenseur générique ; passe arrière sur tableaux avec preuve de correction (ou vérification systématique) ; script qui exige les sections du gabarit pédagogique dans chaque chapitre | `check.mjs` étendu |

## 4. Questions à valider

1. Numérotation : insérer les nouveaux chapitres dans l'ordre pédagogique (renumérotation de tous les fichiers, glossaire et liens) ou les ajouter à la suite (16 et plus) en ajustant seulement le graphe des prérequis ?
2. Outils mathématiques : se limiter aux distributions **finies** (rigoureux sans Mathlib) acceptable, ou souhaitez-vous aussi l'analyse réelle (hors de portée sans Mathlib) ?
3. Ordre de priorité des phases 1 à 5.
4. Phase 6 (correction prouvée des passes arrière sur tableaux) : à lancer, sachant que c'est le chantier le plus lourd et que les tests par différences finies actuels couvrent déjà le besoin pratique ?
5. Les performances (GPU, gros modèles) restent hors périmètre : confirmé ?
