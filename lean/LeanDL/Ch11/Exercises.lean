import LeanDL.Ch11.Gan

/-! Exercises for Chapter 11. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch11

open Lean.Grind

-- ANCHOR: ex1
/-- Exercise 1: where the generator puts no mass, the optimal discriminator answers `1`. -/
theorem exercise_dStar_no_generator {α : Type} [Field α] (a : α) (h : a ≠ 0) :
    dStar a (0 : α) = 1 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: a discriminator that answers `1` pays only for the generated data. -/
theorem exercise_lsLoss_at_one {α : Type} [CommRing α] (a b : α) : lsLoss a b (1 : α) = b := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch11