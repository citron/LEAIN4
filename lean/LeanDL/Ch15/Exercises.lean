import LeanDL.Ch15.Jepa

/-! Exercises for Chapter 15. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch15

open Lean.Grind

-- ANCHOR: ex1
/-- Exercise 1: a batch with a single embedding has zero spread. -/
theorem exercise_spread_single {α : Type} [CommRing α] (a : α) : spread [a] = 0 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: once the spread reaches `γ`, the variance penalty is switched off. -/
theorem exercise_vreg_zero (γ s : Rat) (h : γ ≤ s) : vreg γ s = 0 := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch15