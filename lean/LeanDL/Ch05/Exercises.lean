import LeanDL.Ch05.Optim

/-! Exercises for Chapter 5. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: two steps of gradient descent on `a w² / 2` multiply `w` by `1 - η a` twice. -/
theorem exercise_sgd_two_steps (η a w : α) :
    sgdQuad η a w 2 = (1 - η * a) * ((1 - η * a) * w) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the first value of the moving average is `(1 - β) g`. -/
theorem exercise_ema_first (β g : α) : ema β g 1 = (1 - β) * g := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch05