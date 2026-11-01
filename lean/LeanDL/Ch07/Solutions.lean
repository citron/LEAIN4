import LeanDL.Ch07.Gradient

/-! Solutions for the Chapter 7 exercises. -/

namespace LeanDL.Ch07

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: sol1
theorem exercise_jacRec_zero_weight_solution (g : Nat → α) (t : Nat) : jacRec 0 g (t + 1) = 0 := by
  simp only [jacRec]
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_jacRec_unit_solution (t : Nat) : jacRec (1 : α) (fun _ => 1) t = 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [jacRec, ih]; grind
-- ANCHOR_END: sol2

end LeanDL.Ch07