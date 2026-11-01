import LeanDL.Ch13.Rl

/-! Exercises for Chapter 13. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch13

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: when the estimate already equals the target, a TD update changes nothing. -/
theorem exercise_td_fixed (q eta : α) : tdUpdate q q eta = q := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: started at the fixed point of the Bellman equation, value iteration stays there. -/
theorem exercise_valueIter_fixed (r g vs : α) (h : vs = r + g * vs) (k : Nat) :
    valueIter r g vs k = vs := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch13