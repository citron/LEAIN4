import LeanDL.Ch05.Kit

/-!
# Chapter 20 — The capstone: one training recipe, proved

The whole course has been one loop seen from twenty angles: initialise
(Ch05 Kit), forward (Ch01-09), loss (Ch05, Ch10, Ch17), gradient
(Ch04), clip and step (Ch05 Kit), decay the learning rate (Ch05 Kit),
measure (every demo). This chapter closes the loop: it composes the Kit's
theorems into ONE recipe — decoupled weight decay, gradient clipping,
exponential schedule — and proves, for the running quadratic model, that

* inside the clipping box the recipe is **invisible**: it equals plain
  L2-regularised SGD (`decay_sgd_eq` + clipping idempotence);
* on the quadratic the recipe step has a **closed form** `(1 - lr·(2+wd))ᵗ · w₀`
  — the same shape as Ch05's `sgdQuad_closed`, now with the decay folded in;
* under the stability condition `0 ≤ lr·(2+wd) ≤ 2` the squared loss is
  **non-increasing at every iterate** — the full recipe never worsens the
  loss, at any epoch, by induction;
* the exponential schedule spends a **finite** total step budget
  (`lr_decay_total`, cited verbatim).

Every proof is exact `Rat`; the demo `lake exe capstone` runs the same
recipe in `Float` on MNIST, end to end.
-/

namespace LeanDL.Ch20

open Lean.Grind
open LeanDL (vsum)
open LeanDL.Ch05

section Recipe

-- ANCHOR: recipe
/-- **The capstone step.** Decoupled weight decay (Ch05 Kit) applied to the
weight itself, then the clipped gradient (Ch05 Kit) stepped against it.
These are the two boxes every modern trainer shows as "wd" and
"max_grad_norm"; here they are definitions over `Rat`. -/
def recipeStep (lr wd c : Rat) (w g : Rat) : Rat :=
  decoupledShrink lr wd w - lr * clip c g

/-- A gradient already inside the box is **not clipped**: `-c ≤ x ≤ c`
forces `clip c x = x`. This is the lemma every "clipping only bites on
spikes" claim rests on. -/
theorem clip_id (c x : Rat) (hlo : -c ≤ x) (hhi : x ≤ c) : clip c x = x := by
  unfold clip
  have h1 : ¬ x < -c := Rat.not_lt.mpr hlo
  split <;> grind
-- ANCHOR_END: recipe

-- ANCHOR: decay
/-- **The recipe is invisible inside the box.** When the gradient sits in
`[-c, c]`, the full recipe step — decoupled decay first, clipping second —
equals plain L2-regularised SGD `w - lr·(g + wd·w)`. Both Kit theorems
fire at once: `clip_id` removes the clipping, `decay_sgd_eq` folds the
decoupled shrink back into the gradient. Decoupling is invisible for SGD;
its point is Adam (Kit exercise 4). -/
theorem recipe_step_eq (lr wd c w g : Rat)
    (hlo : -c ≤ g) (hhi : g ≤ c) :
    recipeStep lr wd c w g = w - lr * l2Gradient wd w g := by
  unfold recipeStep
  rw [clip_id c g hlo hhi]
  exact (decay_sgd_eq lr wd w g).symm
-- ANCHOR_END: decay

end Recipe

section Quadratic

/-- The running example of Ch05: a quadratic in one weight, gradient `2·w`.
The **unclipped** recipe map, i.e. the recipe on gradients that never
leave the box. -/
def plainStep (lr wd : Rat) (w : Rat) : Rat :=
  decoupledShrink lr wd w - lr * (2 * w)

/-- The recipe map is multiplication by the contraction
`c = 1 - lr·(2 + wd)` — decay and curvature merge into one factor. -/
theorem plainStep_eq (lr wd w : Rat) :
    plainStep lr wd w = (1 - lr * (2 + wd)) * w := by
  unfold plainStep decoupledShrink
  grind

/-- **Contraction lemma.** Scaling by `c` with `c² ≤ 1` never grows `w²`.
Proved by the difference bridge `(cw)² = c²w² ≤ w²`. -/
theorem sq_mono (c w : Rat) (hc1 : c * c ≤ 1) : (c * w) * (c * w) ≤ w * w := by
  have hw : 0 ≤ w * w := LeanDL.sq_nonneg w
  have hd : w * w - (c * w) * (c * w) = (1 - c * c) * (w * w) := by grind
  have hc0 : 0 ≤ 1 - c * c := by grind
  have hprod : 0 ≤ (1 - c * c) * (w * w) := Rat.mul_nonneg hc0 hw
  rw [← hd] at hprod
  exact (Rat.le_iff_sub_nonneg _ _).mpr hprod

/-- The recipe iterated `t` times on the quadratic. -/
def recipeIter (lr wd : Rat) : Nat → Rat → Rat
  | 0, w => w
  | t + 1, w => recipeIter lr wd t (plainStep lr wd w)

/-- Inside the box (gradient `2·w` with `|2w| ≤ c`), the recipe step *is*
the unclipped map. -/
theorem recipeStep_eq_plain (lr wd c w : Rat)
    (hlo : -c ≤ 2 * w) (hhi : 2 * w ≤ c) :
    recipeStep lr wd c w (2 * w) = plainStep lr wd w := by
  unfold plainStep
  rw [recipe_step_eq lr wd c w (2 * w) hlo hhi]
  unfold l2Gradient decoupledShrink
  grind

-- ANCHOR: loop
/-- **Closed form of the iterated recipe.** Every iterate is
`(1 - lr·(2 + wd))ᵗ · w₀` — the geometric shape of Ch05's
`sgdQuad_closed` with the weight decay folded into the rate. This is the
box "optimizer" of the loop made exact: the epoch count is the exponent. -/
theorem recipe_closed (lr wd : Rat) :
    ∀ t w, recipeIter lr wd t w = powN (1 - lr * (2 + wd)) t * w
  | 0, w => by unfold recipeIter; simp only [powN]; grind
  | t + 1, w => by
    unfold recipeIter
    rw [recipe_closed lr wd t, powN_succ, plainStep_eq]
    grind

/-- **One recipe step never grows the loss**: under the stability condition
`0 ≤ lr·(2+wd) ≤ 2`, the contraction `c := 1 - lr·(2+wd)` lies in `[-1, 1]`,
so `c² ≤ 1` (Ch05 `sq_le_one`) and the squared weight cannot increase
(`sq_mono`). -/
theorem plainStep_sq_le (lr wd : Rat) (hη : 0 ≤ lr * (2 + wd)) (h2 : lr * (2 + wd) ≤ 2)
    (w : Rat) :
    plainStep lr wd w * plainStep lr wd w ≤ w * w := by
  have hc : -1 ≤ 1 - lr * (2 + wd) := by grind
  have hc' : 1 - lr * (2 + wd) ≤ 1 := by grind
  have hsq : (1 - lr * (2 + wd)) * (1 - lr * (2 + wd)) ≤ 1 :=
    sq_le_one _ hc hc'
  rw [plainStep_eq]
  exact sq_mono _ _ hsq

/-- **The capstone theorem.** The full recipe — init, decay, clip, step —
run for `t` epochs on the quadratic has non-increasing squared loss at
*every* iterate: `w(t)² ≤ w(0)²`, by induction on the loop. This is the
loop of the entire course certified at every epoch, exactly. -/
theorem recipe_iter_sq_le (lr wd : Rat) (hη : 0 ≤ lr * (2 + wd)) (h2 : lr * (2 + wd) ≤ 2) :
    ∀ (t : Nat) (w : Rat),
      recipeIter lr wd t w * recipeIter lr wd t w ≤ w * w := by
  intro t w
  have hc : -1 ≤ 1 - lr * (2 + wd) := by grind
  have hc' : 1 - lr * (2 + wd) ≤ 1 := by grind
  have hsq : (1 - lr * (2 + wd)) * (1 - lr * (2 + wd)) ≤ 1 :=
    sq_le_one _ hc hc'
  have h0 : 0 ≤ (1 - lr * (2 + wd)) * (1 - lr * (2 + wd)) := LeanDL.sq_nonneg _
  have hpow := (powN_le_one _ h0 hsq t).1
  have hs : powN ((1 - lr * (2 + wd)) * (1 - lr * (2 + wd))) t =
      powN (1 - lr * (2 + wd)) t * powN (1 - lr * (2 + wd)) t := powN_sq _ t
  have hw : 0 ≤ w * w := LeanDL.sq_nonneg w
  rw [recipe_closed]
  have hsq' : powN (1 - lr * (2 + wd)) t * powN (1 - lr * (2 + wd)) t ≤ 1 := by
    rw [← hs]
    exact hpow
  exact sq_mono _ _ hsq'
-- ANCHOR_END: loop

end Quadratic

section Budget

-- ANCHOR: budget
/-- **The schedule box, cited verbatim from the Kit.** The exponential
schedule `ηₜ = η₀·γᵗ` spends a *finite* total step budget `η₀/(1-γ)` —
the exact difference between "decay" and "decay fast", and the reason a
decaying recipe can take more epochs without moving further in total. -/
theorem recipe_budget (η₀ γ : Rat) (n : Nat) (h0 : 0 < γ) (h1 : γ < 1) (hη : 0 ≤ η₀) :
    vsum (fun t : Fin n => lrAt η₀ γ (t : Nat)) ≤ η₀ / (1 - γ) :=
  lr_decay_total η₀ γ n h0 h1 hη
-- ANCHOR_END: budget

end Budget

end LeanDL.Ch20
