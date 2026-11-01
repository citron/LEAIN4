import LeanDL.Ch15.Jepa

/-! Solutions for the Chapter 15 exercises. -/

namespace LeanDL.Ch15

open Lean.Grind

theorem exercise_spread_single_solution {α : Type} [CommRing α] (a : α) : spread [a] = 0 := by
  simp only [spread, List.map, sumL]
  grind

theorem exercise_vreg_zero_solution (γ s : Rat) (h : γ ≤ s) : vreg γ s = 0 := by
  simp only [vreg]
  split
  · exfalso; grind
  · rfl

end LeanDL.Ch15