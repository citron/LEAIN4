import LeanDL.Ch13.Rl
import LeanDL.Ch02.Perceptron

/-!
# Chapter 15 — JEPA: predicting in representation space

A Joint-Embedding Predictive Architecture encodes a context `x` and a target `y` with encoders,
and trains a predictor to map the context's embedding to the target's embedding. Its main
danger is *collapse*: the cheapest way to predict is to embed everything to the same point. We
prove that collapse is a global minimiser, that the EMA target moves geometrically, and that a
variance penalty removes collapse as a minimiser. Embeddings are scalars here, to keep the
statements short; the same proofs work coordinate-wise.
-/

namespace LeanDL.Ch15

open Lean.Grind LeanDL.Ch13

section Collapse

variable {X α : Type} [CommRing α]

-- ANCHOR: jepa_loss
/-- The JEPA loss on one pair: squared distance between the predicted embedding of the context
`x` and the embedding of the target `y`. `enc` embeds the context, `tgt` the target. -/
def jepaLoss (enc tgt : X → α) (pred : α → α) (x y : X) : α :=
  (pred (enc x) - tgt y) * (pred (enc x) - tgt y)

/-- **Collapse has zero loss.** If both encoders output the same constant and the predictor is the
identity, the loss is `0` on every pair of inputs, whatever the data. -/
theorem collapse_zero (c : α) (x y : X) :
    jepaLoss (fun _ => c) (fun _ => c) (fun z => z) x y = 0 := by
  simp only [jepaLoss]
  grind

/-- Over the rationals the loss is never negative, so collapse is a **global minimiser**: the loss
alone cannot prefer an informative representation. -/
theorem collapse_is_minimal {X : Type} (enc tgt : X → Rat) (pred : Rat → Rat) (x y : X) (c : Rat) :
    jepaLoss (fun _ => c) (fun _ => c) (fun z => z) x y ≤ jepaLoss enc tgt pred x y := by
  rw [collapse_zero]
  simp only [jepaLoss]
  exact LeanDL.Ch02.sq_nonneg _
-- ANCHOR_END: jepa_loss

end Collapse

section Ema

variable {α : Type} [CommRing α]

-- ANCHOR: ema
/-- Exponential moving average: the target parameter `t` moves a fraction `1 - m` towards the
context parameter `θ`. -/
def ema (m t θ : α) : α := m * t + (1 - m) * θ

/-- One update multiplies the distance between target and context parameters by `m`. -/
theorem ema_error (m t θ : α) : ema m t θ - θ = m * (t - θ) := by
  simp only [ema]
  grind

/-- Iterating `k` updates towards a *fixed* `θ`: the distance is multiplied by `mᵏ`. -/
def emaIter (m θ t0 : α) : Nat → α
  | 0 => t0
  | k + 1 => ema m (emaIter m θ t0 k) θ

theorem emaIter_error (m θ t0 : α) (k : Nat) : emaIter m θ t0 k - θ = pw m k * (t0 - θ) := by
  induction k with
  | zero => simp only [emaIter, pw]; grind
  | succ k ih =>
    simp only [emaIter, pw]
    rw [ema_error]
    grind
-- ANCHOR_END: ema

end Ema

section Variance

variable {α : Type} [CommRing α]

-- ANCHOR: variance
/-- Sum of a list. -/
def sumL : List α → α
  | [] => 0
  | a :: t => a + sumL t

/-- Total pairwise squared distance of a batch of (scalar) embeddings; `0` iff all are equal. -/
def spread (l : List α) : α := sumL (l.map fun x => sumL (l.map fun y => (x - y) * (x - y)))

theorem sumL_replicate_zero (n : Nat) (z : α) (hz : z = 0) : sumL (List.replicate n z) = 0 := by
  induction n with
  | zero => simp only [List.replicate, sumL]
  | succ n ih => simp only [List.replicate, sumL, ih, hz]; grind

/-- **A collapsed batch has zero spread.** -/
theorem spread_const (n : Nat) (c : α) : spread (List.replicate n c) = 0 := by
  simp only [spread, List.map_replicate]
  apply sumL_replicate_zero
  apply sumL_replicate_zero
  grind

/-- Two embeddings have spread `2 (a - b)²`. -/
theorem spread_pair (a b : α) : spread [a, b] = 2 * ((a - b) * (a - b)) := by
  simp only [spread, List.map, sumL]
  grind

/-- Over the rationals a pair has zero spread only if it is collapsed. -/
theorem spread_pair_eq_zero (a b : Rat) (h : spread [a, b] = 0) : a = b := by
  rw [spread_pair] at h
  have h2 : (a - b) * (a - b) = 0 := by grind
  by_cases hlt : a - b < 0
  · have := Rat.mul_pos (show 0 < -(a - b) by grind) (show 0 < -(a - b) by grind)
    grind
  · by_cases hgt : 0 < a - b
    · have := Rat.mul_pos hgt hgt
      grind
    · grind

/-- The variance penalty: nothing when the spread already reaches `γ`, `γ - spread` otherwise. -/
def vreg (γ s : Rat) : Rat := if s < γ then γ - s else 0

/-- Total objective: prediction loss plus `w` times the variance penalty. -/
def total (loss s w γ : Rat) : Rat := loss + w * vreg γ s

/-- **The penalty removes collapse as a minimiser.** A representation that predicts perfectly (loss
`0`) and keeps spread `≥ γ` scores `0`; the collapsed representation (loss `0`, spread `0`) scores
`w γ > 0`. -/
theorem collapse_not_optimal (w γ s : Rat) (hw : 0 < w) (hγ : 0 < γ) (hs : γ ≤ s) :
    total 0 s w γ < total 0 0 w γ := by
  simp only [total, vreg]
  have h1 : ¬ s < γ := by grind
  have h2 : (0 : Rat) < γ := hγ
  simp only [h1, h2, ↓reduceIte]
  have := Rat.mul_pos hw hγ
  grind
-- ANCHOR_END: variance

end Variance

end LeanDL.Ch15
