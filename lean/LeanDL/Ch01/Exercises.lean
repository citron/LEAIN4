import LeanDL.Ch01.Neuron

/-! Exercises for Chapter 1. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch01

open Lean.Grind

-- ANCHOR: ex1
/-- Exercise 1: a neuron computing NOR (`1` exactly when both inputs are `0`). -/
def exNor : Neuron Int 2 := sorry

theorem exNor_correct (a b : Bool) :
    exNor.fire step (v2 (b2i a) (b2i b)) = b2i (!(a || b)) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: ReLU is idempotent. -/
theorem exercise_relu_idem (x : Int) : relu (relu x) = relu x := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: tanh is odd, using only the laws of `exp`. -/
theorem exercise_tanh_odd {α : Type} [Field α] [HasExp α] (x : α)
    (h : HasExp.exp x + HasExp.exp (-x) ≠ 0) : tanh (-x) = -tanh x := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch01