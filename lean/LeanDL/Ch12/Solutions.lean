import LeanDL.Ch12.Diffusion

/-! Solutions for the Chapter 12 exercises. -/

namespace LeanDL.Ch12

open Lean.Grind

variable {α : Type} [CommRing α]

theorem exercise_noiseVar_one_step_solution (a s : α) :
    noiseVar [(a, s)] 0 = s * s := by
  simp only [noiseVar]
  grind

theorem exercise_cumA_two_solution (a1 s1 a2 s2 : α) :
    cumA [(a1, s1), (a2, s2)] = a1 * a2 := by
  simp only [cumA]
  grind

end LeanDL.Ch12