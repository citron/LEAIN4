import LeanDL.Ch09.Attention

/-! Solutions for the Chapter 9 exercises. -/

namespace LeanDL.Ch09

open Lean.Grind LeanDL.Ch05

variable {α : Type} [Field α] [HasExp α]

-- ANCHOR: sol1
theorem exercise_weights_single_solution (z0 : α) (h : HasExp.exp z0 ≠ 0) :
    weights (fun _ : Fin 1 => z0) 0 = 1 := by
  simp only [weights, vsum]
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_causal_future_solution {n : Nat} (t : Nat) (j : Fin n) (h : t < j.val) :
    (causal t : Vec α n) j = 0 := by
  simp only [causal]
  split
  · exfalso; omega
  · rfl
-- ANCHOR_END: sol2

end LeanDL.Ch09