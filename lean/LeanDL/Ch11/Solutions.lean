import LeanDL.Ch11.Gan

/-! Solutions for the Chapter 11 exercises. -/

namespace LeanDL.Ch11

open Lean.Grind

-- ANCHOR: sol1
theorem exercise_dStar_no_generator_solution {α : Type} [Field α] (a : α) (h : a ≠ 0) :
    dStar a (0 : α) = 1 := by
  simp only [dStar]
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_lsLoss_at_one_solution {α : Type} [CommRing α] (a b : α) :
    lsLoss a b (1 : α) = b := by
  simp only [lsLoss]
  grind
-- ANCHOR_END: sol2

end LeanDL.Ch11