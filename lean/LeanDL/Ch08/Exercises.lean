import LeanDL.Ch08.CellPath

/-! Exercises for Chapter 8. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch08

-- ANCHOR: ex1
/-- Exercise 1: unfold the product of three forget gates. -/
theorem exercise_prodF_three {α : Type} [Lean.Grind.CommRing α] (f : Nat → α) :
    prodF f 3 = f 0 * f 1 * f 2 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: a product of non-negative gates is non-negative (by induction). -/
theorem exercise_prodF_nonneg (f : Nat → Rat) (h : ∀ t, 0 ≤ f t) : ∀ t, 0 ≤ prodF f t := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch08