import LeanDL.Ch12.Diffusion

/-! Exercises for Chapter 12. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch12

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: after one noising step, clean data has variance `s²`. -/
theorem exercise_noiseVar_one_step (a s : α) :
    noiseVar [(a, s)] 0 = s * s := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the signal factor of two steps is the product of the two factors. -/
theorem exercise_cumA_two (a1 s1 a2 s2 : α) : cumA [(a1, s1), (a2, s2)] = a1 * a2 := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch12