import LeanDL.Core.Prob
import LeanDL.Core.Sum
import LeanDL.Core.Vec

/-!
# Chapter 10.5 - Boltzmann machines (formal core)

The canonical restricted Boltzmann machine: one visible bit, one hidden
bit, energy `E(v,h)` with coupling `g`, biases `a` (hidden) and `b`
(visible), gauge `exp(0) = 1`. We build the four Boltzmann weights `u`,
the partition function `Z`, the exact Gibbs distribution `w = u / Z`
over `Rat`, the Gibbs conditionals `qh` and `qv`, and prove:

* positivity and normalization of the distribution (`w_pos`, `w_sum`);
* positivity and normalization of the conditionals (`qh_pos`, `qh_sum`);
* the hidden marginals after one sweep (`therm_hidden`);
* the Gibbs factorization of the visible update (`gibbs_factor`);
* invariance of the equilibrium under one full Gibbs sweep
  (`sweep_invariance`);
* the odds-ratio parameter identities (`odds_hidden_on`,
  `odds_hidden_off`);
* the energy form `u = exp(-E)` (`boltzmann_form`, `partition_form`).

Contrastive divergence is the practical shadow of `sweep_invariance`:
a chain that has thermalized samples exactly from the model, and one
sweep is the minimum work that keeps it there.
-/

open Lean.Grind
open LeanDL

namespace LeanDL.Ch105

section Field


theorem div_pos' {x y : Rat} (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  rw [Rat.div_def]
  exact Rat.mul_pos hx (inv_pos' hy)

theorem inv_ne_zero' {a : Rat} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h
  have h1 : (1 : Rat) = 0 := by
    calc
      (1 : Rat) = a⁻¹ * a := (inv_mul_cancel' ha).symm
      _ = 0 * a := by rw [h]
      _ = 0 := Rat.zero_mul a
  exact absurd h1 (by decide)

theorem mul_ne_zero' {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have key : a * b * (b⁻¹ * a⁻¹) = 1 := by
    calc
      a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := Rat.mul_assoc a b _
      _ = a * ((b * b⁻¹) * a⁻¹) := by rw [← Rat.mul_assoc b b⁻¹ a⁻¹]
      _ = a * (1 * a⁻¹) := by rw [Rat.mul_inv_cancel b hb]
      _ = a * a⁻¹ := by rw [Rat.one_mul]
      _ = 1 := Rat.mul_inv_cancel a ha
  have h1 : (1 : Rat) = 0 := by
    calc
      (1 : Rat) = a * b * (b⁻¹ * a⁻¹) := key.symm
      _ = 0 * (b⁻¹ * a⁻¹) := by rw [h]
      _ = 0 := Rat.zero_mul _
  exact absurd h1 (by decide)

theorem field_eq {x z y w : Rat} (hy : y ≠ 0) (hw : w ≠ 0) (h : x * w = z * y) :
    x / y = z / w := by
  rw [Rat.div_def, Rat.div_def]
  have L : (x * w) * (y⁻¹ * w⁻¹) = x * y⁻¹ := by
    calc
      (x * w) * (y⁻¹ * w⁻¹) = x * (w * (y⁻¹ * w⁻¹)) := Rat.mul_assoc x w _
      _ = x * (y⁻¹ * (w * w⁻¹)) := by
          rw [← Rat.mul_assoc w y⁻¹ w⁻¹, Rat.mul_comm w y⁻¹, Rat.mul_assoc y⁻¹ w w⁻¹]
      _ = x * (y⁻¹ * 1) := by rw [Rat.mul_inv_cancel w hw]
      _ = x * y⁻¹ := by rw [Rat.mul_one]
  have R : (z * y) * (y⁻¹ * w⁻¹) = z * w⁻¹ := by
    calc
      (z * y) * (y⁻¹ * w⁻¹) = z * (y * (y⁻¹ * w⁻¹)) := Rat.mul_assoc z y _
      _ = z * ((y * y⁻¹) * w⁻¹) := by rw [← Rat.mul_assoc y y⁻¹ w⁻¹]
      _ = z * (1 * w⁻¹) := by rw [Rat.mul_inv_cancel y hy]
      _ = z * w⁻¹ := by rw [Rat.one_mul]
  rw [← L, ← R, h]

end Field

section Model

-- ANCHOR: canonical_model
/-- Canonical Boltzmann weights over the four states `(v,h)` ordered
`(0,0) (0,1) (1,0) (1,1)`, with the gauge `exp(-E 0 0) = 1`. -/
def u (a b g : Rat) : Vec Rat 4 :=
  fun s => if s.val = 0 then 1 else if s.val = 1 then a
           else if s.val = 2 then b else g
def Z (a b g : Rat) : Rat := 1 + a + b + g

theorem Z_pos (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    0 < Z a b g := by
  unfold Z
  grind

theorem u_pos (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g)
    (s : Fin 4) : 0 < u a b g s := by
  cases s with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      unfold u
      grind

theorem w_sum (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    Vec.dot (fun s => u a b g s / Z a b g) (fun _ => (1 : Rat)) = 1 := by
  have hZ : (1 + a + b + g) * (1 + a + b + g)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt (by grind))
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold u Z
  simp only [Rat.div_def]
  push_cast
  grind


/-- The Gibbs distribution: mass `u s / Z` on each state. -/
def w (a b g : Rat) : Vec Rat 4 := fun s => u a b g s / Z a b g

/-- The Gibbs distribution is strictly positive on every state. -/
theorem w_pos (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    ∀ s : Fin 4, 0 < w a b g s := by
  intro s
  have hZ : 0 < Z a b g := Z_pos a b g ha hb hg
  show 0 < u a b g s / Z a b g
  exact div_pos' (u_pos a b g ha hb hg s) hZ

/-- The Gibbs distribution is a probability distribution. -/
def model (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) : Dist 4 where
  w := w a b g
  pos := w_pos a b g ha hb hg
  sum1 := w_sum a b g ha hb hg
-- ANCHOR_END: canonical_model


end Model

section Gibbs

-- ANCHOR: gibbs_conditionals
/-- Gibbs conditional on the visible: `p(h | v)`. -/
def qh (a b g : Rat) (v h : Nat) : Rat :=
  if v = 0 then
    if h = 0 then 1 / (1 + a) else a / (1 + a)
  else
    if h = 0 then b / (b + g) else g / (b + g)
/-- Gibbs conditional on the hidden: `p(v | h)`. -/
def qv (a b g : Rat) (h j : Nat) : Rat :=
  if h = 0 then
    if j = 0 then 1 / (1 + b) else b / (1 + b)
  else
    if j = 0 then a / (a + g) else g / (a + g)
/-- Visible half-index and hidden half-index of a state. -/
def vOf (n : Nat) : Nat := n / 2
def hOf (n : Nat) : Nat := n % 2
/-- One full Gibbs sweep from visible state `v` to state `t`: draw the
hidden unit from the visible, then the visible from the hidden. -/
def sweep (a b g : Rat) (v t : Nat) : Rat :=
  qh a b g v (hOf t) * qv a b g (hOf t) (vOf t)
-- ANCHOR_END: gibbs_conditionals

/-- Nat-indexed face of the Boltzmann weights. -/
def uNat (a b g : Rat) (s : Nat) : Rat :=
  if s = 0 then 1 else if s = 1 then a else if s = 2 then b else g

theorem qh_pos (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g)
    (v h : Nat) : 0 < qh a b g v h := by
  have h1 : 0 < (1 : Rat) * (1 + a)⁻¹ :=
    Rat.mul_pos (by grind) (inv_pos' (by grind))
  have h2 : 0 < a * (1 + a)⁻¹ :=
    Rat.mul_pos ha (inv_pos' (by grind))
  have h3 : 0 < b * (b + g)⁻¹ :=
    Rat.mul_pos hb (inv_pos' (by grind))
  have h4 : 0 < g * (b + g)⁻¹ :=
    Rat.mul_pos hg (inv_pos' (by grind))
  unfold qh
  simp only [Rat.div_def]
  push_cast
  grind

theorem qh_sum (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) (v : Nat)
    (v0 : v = 0 ∨ v = 1) : qh a b g v 0 + qh a b g v 1 = 1 := by
  have hA : (1 + a) * (1 + a)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have hBG : (b + g) * (b + g)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  rcases v0 with rfl | rfl
  · unfold qh
    simp only [Rat.div_def]
    push_cast
    grind
  · unfold qh
    simp only [Rat.div_def]
    push_cast
    grind

/-- Hidden marginals after one sweep: thermalizing the hidden unit
from equilibrium reproduces the equilibrium hidden marginal. -/
theorem therm_hidden (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    uNat a b g 0 / Z a b g * qh a b g 0 0 + uNat a b g 1 / Z a b g * qh a b g 0 0
        + uNat a b g 2 / Z a b g * qh a b g 1 0 + uNat a b g 3 / Z a b g * qh a b g 1 0
        = (1 + b) / Z a b g ∧
    uNat a b g 0 / Z a b g * qh a b g 0 1 + uNat a b g 1 / Z a b g * qh a b g 0 1
        + uNat a b g 2 / Z a b g * qh a b g 1 1 + uNat a b g 3 / Z a b g * qh a b g 1 1
        = (a + g) / Z a b g := by
  have hA : (1 + a) * (1 + a)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have hBG : (b + g) * (b + g)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have hZ : (1 + a + b + g) * (1 + a + b + g)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt (by grind))
  constructor
  · unfold uNat Z qh
    simp only [Rat.div_def]
    push_cast
    grind
  · unfold uNat Z qh
    simp only [Rat.div_def]
    push_cast
    grind

/-- Gibbs factorization of the visible update: the thermal hidden
marginal times the visible conditional equals the exact target mass. -/
theorem gibbs_factor (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    (1 + b) / Z a b g * qv a b g 0 0 = uNat a b g 0 / Z a b g ∧
    (1 + b) / Z a b g * qv a b g 0 1 = uNat a b g 2 / Z a b g ∧
    (a + g) / Z a b g * qv a b g 1 0 = uNat a b g 1 / Z a b g ∧
    (a + g) / Z a b g * qv a b g 1 1 = uNat a b g 3 / Z a b g := by
  have hB : (1 + b) * (1 + b)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have hAG : (a + g) * (a + g)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  have hZ : (1 + a + b + g) * (1 + a + b + g)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ (Rat.ne_of_gt (by grind))
  constructor
  · unfold uNat Z qv
    simp only [Rat.div_def]
    push_cast
    grind
  · constructor
    · unfold uNat Z qv
      simp only [Rat.div_def]
      push_cast
      grind
    · constructor
      · unfold uNat Z qv
        simp only [Rat.div_def]
        push_cast
        grind
      · unfold uNat Z qv
        simp only [Rat.div_def]
        push_cast
        grind

-- ANCHOR: sweep_invariance
/-- Gibbs sweep invariance: one full sweep of the Gibbs chain from the
equilibrium distribution lands back on the equilibrium distribution,
state by state. This is the exact, finite shadow of the ergodic
theorem behind contrastive divergence. -/
theorem sweep_invariance (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    ∀ t : Fin 4,
      uNat a b g 0 / Z a b g * sweep a b g (vOf ((⟨0, by omega⟩ : Fin 4) : Nat)) t.val
        + uNat a b g 1 / Z a b g * sweep a b g (vOf ((⟨1, by omega⟩ : Fin 4) : Nat)) t.val
        + uNat a b g 2 / Z a b g * sweep a b g (vOf ((⟨2, by omega⟩ : Fin 4) : Nat)) t.val
        + uNat a b g 3 / Z a b g * sweep a b g (vOf ((⟨3, by omega⟩ : Fin 4) : Nat)) t.val
        = uNat a b g t.val / Z a b g := by
  intro t
  cases t with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      have hA : (1 + a) * (1 + a)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
      have hB : (1 + b) * (1 + b)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
      have hBG : (b + g) * (b + g)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
      have hAG : (a + g) * (a + g)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
      have hZ : (1 + a + b + g) * (1 + a + b + g)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ (Rat.ne_of_gt (by grind))
      unfold uNat Z sweep vOf hOf qh qv
      simp only [Rat.div_def]
      push_cast
      grind

/-- Odds-ratio
-- ANCHOR_END: sweep_invariance
 parameter recovery: conditioning the hidden unit on the
visible unit being on, the ratio of its conditionals is the coupling
over the visible bias. -/
theorem odds_hidden_on (_a b g : Rat) (hb : 0 < b) (hg : 0 < g) :
    (g / (b + g)) / (b / (b + g)) = g / b := by
  have hne : b + g ≠ 0 := Rat.ne_of_gt (by grind)
  have hdiv : b / (b + g) ≠ 0 := by
    rw [Rat.div_def]
    exact mul_ne_zero' (Rat.ne_of_gt hb) (inv_ne_zero' hne)
  have hinv : (b / (b + g))⁻¹ = (b + g) * b⁻¹ := by
    rw [Rat.div_def, Field.inv_mul, Field.inv_inv, Rat.mul_comm]
  rw [Rat.div_def, Rat.div_def, hinv]
  grind

/-- Hidden-off odds ratio: `p(h=1 | v=0) / p(h=0 | v=0) = a`. -/
theorem odds_hidden_off (a : Rat) (ha : 0 < a) :
    (a / (1 + a)) / (1 / (1 + a)) = a := by
  have hne : 1 + a ≠ 0 := Rat.ne_of_gt (by grind)
  have hdiv : 1 / (1 + a) ≠ 0 := by
    rw [Rat.div_def, Rat.one_mul]
    exact inv_ne_zero' hne
  have hinv : (1 / (1 + a))⁻¹ = 1 + a := by
    rw [Rat.div_def, Rat.one_mul, Field.inv_inv]
  rw [Rat.div_def, Rat.div_def, hinv]
  grind
end Gibbs

-- ANCHOR: energy_form
section Energy

/-- A nonzero square is positive. -/
theorem sq_pos' {a : Rat} (h : a ≠ 0) : 0 < a * a := by
  by_cases hpos : 0 < a
  · exact Rat.mul_pos hpos hpos
  · have hn : 0 < -a := by grind
    have hprod : 0 < (-a) * (-a) := Rat.mul_pos hn hn
    have neg2 : (-a) * (-a) = a * a := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [neg2] at hprod
    exact hprod

/-- `exp x * exp (-x) = 1`: the exponential never vanishes. -/
theorem exp_neg_mul [HasExp Rat] [LawfulExp Rat] (x : Rat) :
    HasExp.exp x * HasExp.exp (-x) = 1 := by
  rw [← LawfulExp.exp_add, show x + -x = (0 : Rat) from by grind, LawfulExp.exp_zero]

/-- **`exp` is strictly positive** on `Rat`: `exp x = (exp (x/2))^2`, a nonzero square. -/
theorem exp_pos' [HasExp Rat] [LawfulExp Rat] (x : Rat) : 0 < HasExp.exp x := by
  have key : HasExp.exp x = HasExp.exp (x / 2) * HasExp.exp (x / 2) := by
    have h : x / 2 + x / 2 = x := by grind
    have hc := LawfulExp.exp_add (x / 2) (x / 2)
    rw [h] at hc
    exact hc
  rw [key]
  refine sq_pos' (by
    intro heq
    have h1 := exp_neg_mul (x / 2)
    rw [heq, Rat.zero_mul] at h1
    exact absurd h1 (by grind))

/-- `exp (-x) = (exp x)⁻¹`. -/
theorem exp_neg_eq_inv [HasExp Rat] [LawfulExp Rat] (x : Rat) :
    HasExp.exp (-x) = (HasExp.exp x)⁻¹ := by
  have hne : HasExp.exp x ≠ 0 := Rat.ne_of_gt (exp_pos' x)
  calc HasExp.exp (-x) = 1 * HasExp.exp (-x) := (Rat.one_mul _).symm
    _ = ((HasExp.exp x)⁻¹ * HasExp.exp x) * HasExp.exp (-x) := by
        rw [inv_mul_cancel' hne]
    _ = (HasExp.exp x)⁻¹ * (HasExp.exp x * HasExp.exp (-x)) :=
        Rat.mul_assoc _ _ _
    _ = (HasExp.exp x)⁻¹ * 1 := by rw [exp_neg_mul]
    _ = (HasExp.exp x)⁻¹ := Rat.mul_one _

variable [HasExp Rat] [LawfulExp Rat]

/-- The energy of the canonical machine: gauge `E 0 0 = 0`. -/
def E (α β δ : Rat) : Vec Rat 4 :=
  fun s => if s.val = 0 then 0 else if s.val = 1 then -α
           else if s.val = 2 then -β else -δ

/-- The Boltzmann form: weights are exponentials of the energy. -/
theorem boltzmann_form (α β δ : Rat) :
    u (HasExp.exp α) (HasExp.exp β) (HasExp.exp δ)
      = fun s => HasExp.exp (-E α β δ s) := by
  funext s
  cases s with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    · unfold u E
      show (1 : Rat) = HasExp.exp (-(0 : Rat))
      rw [show (-(0 : Rat)) = (0 : Rat) from by grind, LawfulExp.exp_zero]
    · unfold u E
      show HasExp.exp α = HasExp.exp (-(-α))
      rw [show (-(-α) : Rat) = α from by grind]
    · unfold u E
      show HasExp.exp β = HasExp.exp (-(-β))
      rw [show (-(-β) : Rat) = β from by grind]
    · unfold u E
      show HasExp.exp δ = HasExp.exp (-(-δ))
      rw [show (-(-δ) : Rat) = δ from by grind]
-- ANCHOR_END: energy_form


/-- The partition function is the total mass of `exp(-E)`. -/
theorem partition_form (α β δ : Rat) :
    Z (HasExp.exp α) (HasExp.exp β) (HasExp.exp δ)
      = Vec.dot (fun s : Fin 4 => HasExp.exp (-E α β δ s)) (fun _ => (1 : Rat)) := by
  rw [← boltzmann_form]
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold u Z
  push_cast
  grind


end Energy

end LeanDL.Ch105
