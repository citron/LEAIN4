import LeanDL.Core.Rounding
/-!
# IEEE-754 : la grille binaire, source du modèle d'arrondi

`Core/Rounding.lean` pose l'arrondi flottant comme hypothèse nommée
(`RoundingModel : fl x = x·(1+δ), |δ| ≤ u`). Ce module en montre la
**source** : la grille du format binaire IEEE-754, spécifiée sur `Rat`
sans Mathlib, et la preuve que **toute grille engendre un
`RoundingModel`** avec `u = 2⁻ᵖʳᵉᶜ` — l'hypothèse de T9 devient un
théorème sur la grille.

Design (indépendance Mathlib) : les binades sont indexées par des `Nat`
et le pas de grille s'écrit `2^b / 2^prec` — uniquement des puissances
`Nat` et de la division. Aucune puissance à exposant relatif, donc
aucune algèbre `zpow` (le cœur Lean 4.35 sans Mathlib n'en fournit
aucune loi).

* `Grid` : structure de grille — binades `[2^b, 2^(b+1))`, pas
  `2^b / 2^prec`, arrondi à demi-pas près, **le résultat d'un arrondi
  est un point de grille** (cœur d'IEEE-754 : le représentable), points
  de grille fixes. Les champs sont des **hypothèses nommées** — zéro
  axiome, et le débordement est exclu par contrat (comme dans T9).
* `Grid.toRoundingModel` : réduction vers `RoundingModel`, `u = 2⁻ᵖʳᵉᶜ`.
* `Grid.grid_idem` : **idempotence** `fl (fl x) = fl x` — l'arrondi est
  stable : arrondir deux fois ne change rien.

Ce qui reste **hypothèse de plateforme** (unique en son genre, assumée) :
que le `Float` de Lean (binary64, roundTiesToEven) implémente cette
grille. Lean n'a aucune théorie IEEE-754 ; sa signature **observable**
est testée dans `Demos/Props.lean` : `1 + 2⁻⁵³ = 1`, `1 + 2⁻⁵² ≠ 1`,
lie paire `1 + 3·2⁻⁵³ = 1 + 2⁻⁵²`. Statut : « Vérifié numériquement ».
-/

namespace LeanDL.Core.Ieee754

/-! ## 1. Algèbre des puissances de 2 (exposants natifs, `Rat`) -/

theorem Rat_pow_add (x : Rat) (m n : Nat) : x ^ (m + n) = x ^ m * x ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Rat.pow_zero]; grind
  | succ k ih =>
    rw [Nat.add_succ, Rat.pow_succ, Rat.pow_succ x k, ih]
    grind

theorem pow2_ne_zero (n : Nat) : (2 : Rat) ^ n ≠ 0 := by
  induction n with
  | zero => rw [Rat.pow_zero]; grind
  | succ k ih => rw [Rat.pow_succ]; grind

theorem pow2_pos (n : Nat) : (0 : Rat) < (2 : Rat) ^ n := by
  induction n with
  | zero => rw [Rat.pow_zero]; grind
  | succ k ih => rw [Rat.pow_succ]; grind

theorem pow2_ge_one (n : Nat) : (1 : Rat) ≤ (2 : Rat) ^ n := by
  induction n with
  | zero => rw [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat_pow_add, Rat.pow_one]
    grind

/-- `1 < 2^(n+1)` : tout exposant **strictement** positif dépasse 1. -/
theorem one_lt_pow2 (n : Nat) : (1 : Rat) < (2 : Rat) ^ (n + 1) := by
  induction n with
  | zero => rw [Nat.zero_add, Rat.pow_one]; grind
  | succ k ih =>
    rw [Rat_pow_add, Rat.pow_one]
    grind

/-- Monotonie stricte : `m < n → 2^m < 2^n`. -/
theorem pow2_lt {m n : Nat} (h : m < n) : (2 : Rat) ^ m < (2 : Rat) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  rw [Rat_pow_add]
  have hg : (2 : Rat) ^ m * 1 < (2 : Rat) ^ m * (2 : Rat) ^ (k + 1) :=
    Rat.mul_lt_mul_of_pos_left (one_lt_pow2 k) (pow2_pos m)
  grind

/-- Monotonie large. -/
theorem pow2_le {m n : Nat} (h : m ≤ n) : (2 : Rat) ^ m ≤ (2 : Rat) ^ n := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact Rat.le_refl
  · exact Rat.le_of_lt (pow2_lt h)

/-- Réciproque : `2^m ≤ 2^n → m ≤ n` (unicité de la binade). -/
theorem pow2_le_imp {m n : Nat} (h : (2 : Rat) ^ m ≤ (2 : Rat) ^ n) : m ≤ n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · exfalso
    have h2 := pow2_lt hgt
    grind

/-! ## 2. Bornes absolues (le cœur n'a pas de loi `abs_le`) -/

theorem abs_le_split {x u : Rat} (h : Rat.abs x ≤ u) : -u ≤ x ∧ x ≤ u := by
  grind [Rat.abs.eq_1]

theorem abs_le_intro {x u : Rat} (h1 : -u ≤ x) (h2 : x ≤ u) : Rat.abs x ≤ u := by
  grind [Rat.abs.eq_1]

/-! ## 3. La grille binaire (spécification par hypothèses nommées) -/

/-- Échelle de la binade `b` : `2^b`. -/
def scale (b : Nat) : Rat := (2 : Rat) ^ b

/-- Unité de la grille de précision `prec` : `2^prec`. -/
def unit (prec : Nat) : Rat := (2 : Rat) ^ prec

/-- Pas de la grille dans la binade `b` : `2^b / 2^prec`. -/
def step (prec b : Nat) : Rat := scale b / unit prec

/-- Domaine normalisé : `x ∈ [2^bmin, 2^bmax)`. -/
def inDomain (bmin bmax : Nat) (x : Rat) : Prop :=
  scale bmin ≤ x ∧ x < scale bmax

-- ANCHOR: grid
/-- Un **format de grille binaire** de précision `prec ≥ 1`, binades
normalisées `bmin ≤ b < bmax`, arrondi `fl` et binade `pick`, spécifiés
sur `Rat` par des **hypothèses nommées** (champs de la structure —
jamais des axiomes) :

* `band` : `2^pick x ≤ x < 2^(pick x + 1)` — la binade de `x` ;
* `pickDom` : la binade de `x` est normalisée ;
* `nearest` : `|fl x − x| ≤ step(prec, pick x) / 2` — arrondi au plus
  proche, à demi-pas près (le réglage de la lie — `roundTiesToEven` —
  est un raffinement de la même inégalité ; voir la page du chapitre) ;
* `onGrid` : `fl x` est **représentable** — multiple du pas de SA
  binade, dans le domaine. C'est le cœur d'IEEE-754 : l'arrondi produit
  un nombre **du format** (pas de débordement : contrat, comme dans
  `RoundingModel`) ;
* `fixed` : les points de grille sont des points fixes. -/
structure Grid where
  prec : Nat
  hp : 1 ≤ prec
  bmin : Nat
  bmax : Nat
  hlt : bmin + 1 ≤ bmax
  pick : Rat → Nat
  fl : Rat → Rat
  band :
    ∀ x, inDomain bmin bmax x →
      scale (pick x) ≤ x ∧ x < scale (pick x + 1)
  pickDom :
    ∀ x, inDomain bmin bmax x → bmin ≤ pick x ∧ pick x + 1 ≤ bmax
  nearest :
    ∀ x, inDomain bmin bmax x →
      Rat.abs (fl x - x) ≤ step prec (pick x) / 2
  onGrid :
    ∀ x, inDomain bmin bmax x →
      ∃ k, inDomain bmin bmax (fl x) ∧
        fl x = (k : Rat) * (scale (pick (fl x)) / unit prec)
  fixed :
    ∀ x b k, inDomain bmin bmax x → bmin ≤ b → b + 1 ≤ bmax →
      scale b ≤ x → x < scale (b + 1) →
      x = (k : Rat) * (scale b / unit prec) →
      fl x = x
-- ANCHOR_END: grid

/-! ## 4. Réduction : la grille engendre le modèle d'arrondi de T9 -/

/-- Inverse renverse l'ordre sur les positifs (pattern de
`Core/Rounding.lean`). -/
theorem inv_le_inv {a b : Rat} (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) :
    a⁻¹ ≤ b⁻¹ := by
  have hP : 0 ≤ a⁻¹ * b⁻¹ :=
    Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr ha)) (Rat.le_of_lt (Rat.inv_pos.mpr hb))
  have hmul := Rat.mul_le_mul_of_nonneg_right h hP
  have h1 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by grind
  have h2 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by grind
  rw [h1, h2] at hmul
  exact hmul

/-- L'arrondi étendu : identité hors domaine, `fl` dans le domaine
(exclusion du débordement, contrat du modèle, comme dans T9). -/
noncomputable def Grid.flExt (g : Grid) : Rat → Rat :=
  fun x => @dite Rat (inDomain g.bmin g.bmax x)
    (Classical.propDecidable _) (fun _ => g.fl x) (fun _ => x)

-- ANCHOR: reduction
/-- **Réduction** : toute grille est un `RoundingModel` de paramètre
`u = (2^prec)⁻¹ = 2⁻ᵖʳᵉᶜ`. Dans le domaine : `δ := (fl x − x) · x⁻¹` ;
`2^pick x ≤ x` transforme la borne **absolue** à demi-pas en borne
**relative** : `(2^pick x / 2^prec / 2)·x⁻¹ = (2^pick x · x⁻¹)·(2·2^prec)⁻¹ ≤
(2^prec)⁻¹`. Hors domaine : `δ = 0`. L'hypothèse `RoundingModel.rel`
devient un théorème sur la grille. -/
noncomputable def Grid.toRoundingModel (g : Grid) : RoundingModel where
  fl := g.flExt
  u := (unit g.prec)⁻¹
  u_nonneg := Rat.le_of_lt (Rat.inv_pos.mpr (pow2_pos g.prec))
  rel := by
    intro x
    classical
    by_cases hx : inDomain g.bmin g.bmax x
    · unfold Grid.flExt
      rw [dif_pos hx]
      -- On garde `scale`/`unit` opaques : `grind` traite `scale b` comme
      -- atome, et le terme `2 ^ g.pick x` empoisonne son anneau (instance
      -- HPow non standard dans le graphe d'imports complet).
      have hsb := g.band x hx
      obtain ⟨hn1, hn2⟩ := abs_le_split (g.nearest x hx)
      have hsb0 : (0 : Rat) < scale (g.pick x) := by
        unfold scale
        exact pow2_pos (g.pick x)
      have hU0 : (0 : Rat) < unit g.prec := by
        unfold unit
        exact pow2_pos g.prec
      have hpos : (0 : Rat) < x := by grind
      have hxI : (0 : Rat) ≤ x⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hpos)
      have hx1 : x * x⁻¹ = 1 := by grind
      have hp2 : (0 : Rat) < 2 * unit g.prec := by grind
      have hsx : scale (g.pick x) * x⁻¹ ≤ 1 := by
        have h := Rat.mul_le_mul_of_nonneg_right hsb.1 hxI
        rw [hx1] at h
        exact h
      have hinv : (2 * unit g.prec)⁻¹ ≤ (unit g.prec)⁻¹ :=
        inv_le_inv hp2 hU0 (by grind)
      have hn : (0 : Rat) ≤ (2 * unit g.prec)⁻¹ :=
        Rat.le_of_lt (Rat.inv_pos.mpr hp2)
      have hkey : step g.prec (g.pick x) / 2 * x⁻¹ =
          (scale (g.pick x) * x⁻¹) * (2 * unit g.prec)⁻¹ := by
        unfold step
        grind [Rat.div_def]
      have hkey' : -(step g.prec (g.pick x) / 2) * x⁻¹ =
          -((scale (g.pick x) * x⁻¹) * (2 * unit g.prec)⁻¹) := by
        unfold step
        grind [Rat.div_def]
      have hhi : (g.fl x - x) * x⁻¹ ≤ (scale (g.pick x) * x⁻¹) * (2 * unit g.prec)⁻¹ := by
        have h := Rat.mul_le_mul_of_nonneg_right hn2 hxI
        rw [hkey] at h
        exact h
      have hlo : -((scale (g.pick x) * x⁻¹) * (2 * unit g.prec)⁻¹) ≤ (g.fl x - x) * x⁻¹ := by
        have h := Rat.mul_le_mul_of_nonneg_right hn1 hxI
        rw [hkey'] at h
        exact h
      have hle : (scale (g.pick x) * x⁻¹) * (2 * unit g.prec)⁻¹ ≤ (unit g.prec)⁻¹ := by
        have h := Rat.mul_le_mul_of_nonneg_right hsx hn
        grind
      refine ⟨(g.fl x - x) * x⁻¹, abs_le_intro ?_ ?_, by grind⟩
      · -- −u ≤ δ
        have h := Rat.neg_le_neg hle
        grind
      · -- δ ≤ u
        grind
    · unfold Grid.flExt
      rw [dif_neg hx]
      exact ⟨0, by
        rw [Rat.abs_zero]
        exact Rat.le_of_lt (Rat.inv_pos.mpr (pow2_pos g.prec)), by
        rw [Rat.add_zero, Rat.mul_one]⟩
-- ANCHOR_END: reduction

/-! ## 5. Idempotence : arrondir deux fois ne change rien -/

-- ANCHOR: idem
/-- **Idempotence** : dans le domaine, `fl (fl x) = fl x`. `onGrid`
pose `fl x` comme point de grille de SA binade, dans le domaine ;
`fixed` appliqué à ce point donne `fl (fl x) = fl x`. C'est la propriété
qui rend l'arrondi **stable** — sans elle, les schémas numériques
dérivent à chaque opération. -/
theorem Grid.grid_idem (g : Grid) (x : Rat) (hx : inDomain g.bmin g.bmax x) :
    g.fl (g.fl x) = g.fl x := by
  obtain ⟨k, hdom, heq⟩ := g.onGrid x hx
  have hsb := g.band (g.fl x) hdom
  have hb := g.pickDom (g.fl x) hdom
  exact g.fixed (g.fl x) (g.pick (g.fl x)) k hdom hb.1 hb.2 hsb.1 hsb.2 heq
-- ANCHOR_END: idem

/-! ## 6. Constantes binary64 (calcul exact sur `Rat`) -/

-- ANCHOR: binary64
/-- `2^53 = 9007199254740992` — premier entier non représentable en
binary64 ; le pas de la binade de `1` vaut `2⁻⁵²`, son demi-pas `2⁻⁵³`
(l'epsilon machine d'IEEE double est `2⁻⁵²`). -/
example : (2 : Rat) ^ 53 = 9007199254740992 := by
  decide

/-- `2^52 = 4503599627370496`. -/
example : (2 : Rat) ^ 52 = 4503599627370496 := by
  decide
-- ANCHOR_END: binary64

/-! ## 7. La grille fixe `2⁻ᵖ · ℤ` : arrondi constructif -/

/-- Sur la grille fixe des dyadiques de pas `2⁻ᵖ` (la grille de mantisses
d'une binade normalisée, translatée), l'arrondi au plus proche — à zéro
prés, égalité vers l'infini — est **constructif** : un seul `floor`. -/
noncomputable def fixedGrid (p : Nat) (x : Rat) : Rat :=
  ((Rat.floor (x * (2 : Rat) ^ p + 1 / 2) : Int) : Rat) / (2 : Rat) ^ p

-- ANCHOR: gridfixed
/-- **Les points de grille sont des points fixes** : `k · 2⁻ᵖ` se
round vers lui-même (un demi-pas de part et d'autre, `floor (k + ½) = k`). -/
theorem fixedGrid_fixed (p : Nat) (k : Nat) :
    fixedGrid p ((k : Rat) / (2 : Rat) ^ p) = (k : Rat) / (2 : Rat) ^ p := by
  unfold fixedGrid
  have hp : (0 : Rat) < (2 : Rat) ^ p := pow2_pos p
  have hmul : ((k : Rat) / (2 : Rat) ^ p) * (2 : Rat) ^ p = (k : Rat) := by
    push_cast
    grind [Rat.div_def]
  have hfl : Rat.floor ((k : Rat) + 1 / 2) = (k : Int) := by
    have h1 : (k : Int) ≤ Rat.floor ((k : Rat) + 1 / 2) := by
      rw [Rat.le_floor_iff]
      push_cast
      grind
    have h2 : Rat.floor ((k : Rat) + 1 / 2) < (k : Int) + 1 := by
      rw [Rat.floor_lt_iff]
      push_cast
      grind
    omega
  rw [hmul, hfl]
  push_cast
  grind
-- ANCHOR_END: gridfixed

end LeanDL.Core.Ieee754
