import LeanDL.Ch07.Gradient

/-! Exercises for Chapter 7. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch07

variable {α : Type} [Lean.Grind.CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: with a zero recurrent weight the gradient dies after one step. -/
theorem exercise_jacRec_zero_weight (g : Nat → α) (t : Nat) : jacRec 0 g (t + 1) = 0 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: with weight `1` and all factors `1`, the gradient stays exactly `1`. -/
theorem exercise_jacRec_unit (t : Nat) : jacRec (1 : α) (fun _ => 1) t = 1 := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch07