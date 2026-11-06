import LeanDL.Ch20.Capstone

/-! Exercises for Chapter 20. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch20

open Lean.Grind
open LeanDL.Ch05

-- ANCHOR: ex1
/-- Exercise 1: **the clipped step is invisible on small gradients.** For a
gradient inside the box, prove the full capstone step equals plain SGD with
no decay at all: `recipeStep lr wd c w g = w - lr * g` when `-c ≤ g ≤ c`.
(Hint: `clip_id` removes the clipping; `decoupledShrink` unfolds to
`w - lr·wd·w`; collect the `lr·wd·w` terms with `grind`.) -/
theorem exercise_plain_sgd (lr wd c w g : Rat)
    (hlo : -c ≤ g) (hhi : g ≤ c) :
    recipeStep lr wd c w g = w - lr * g - lr * (wd * w) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: **the budget at t = 0.** The schedule spends exactly the
first learning rate in one epoch: `vsum (fun t : Fin 1 => lrAt η₀ γ t) = η₀`
for `0 < γ < 1`. (Hint: `lrAt η₀ γ 0 = η₀ * powN γ 0 = η₀ * 1`; the
`Fin 1` sum collapses to its value at `0` — `omega` settles `Fin 1` cases,
then `grind`.) -/
theorem exercise_budget_one (η₀ γ : Rat) (h0 : 0 < γ) (h1 : γ < 1) :
    LeanDL.vsum (fun t : Fin 1 => lrAt η₀ γ (t : Nat)) = η₀ := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch20
