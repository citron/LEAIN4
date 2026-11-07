import LeanDL.Ch09.Attention

/-! Exercises for Chapter 9. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch09

variable {α : Type} [Lean.Grind.Field α] [HasExp α]

-- ANCHOR: ex1
/-- Exercise 1: attention over a single position puts all the weight on it. -/
theorem exercise_weights_single (z0 : α) (h : HasExp.exp z0 ≠ 0) :
    weights (fun _ : Fin 1 => z0) 0 = 1 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the causal mask is `0` on every future position. -/
theorem exercise_causal_future {n : Nat} (t : Nat) (j : Fin n) (h : t < j.val) :
    (causal t : Vec α n) j = 0 := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: the multi-head layout round-trips — slicing the concatenation
`concatVec h dh o` with `headVec` returns head `k` intact. -/
theorem exercise_head_concat (h dh : Nat) (o : Fin h → Vec α dh) (k : Fin h) :
    headVec h dh (concatVec h dh o) k = o k := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch09