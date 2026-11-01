import LeanDL.Ch01.Neuron

/-! Solutions for the Chapter 1 exercises. -/

namespace LeanDL.Ch01

open Lean.Grind

-- ANCHOR: sol1
/-- Exercise 1: NOR is `1` exactly when both inputs are `0`. -/
def norN : Neuron Int 2 := ⟨v2 (-1) (-1), 0⟩

theorem nor_correct (a b : Bool) :
    norN.fire step (v2 (b2i a) (b2i b)) = b2i (!(a || b)) := by
  cases a <;> cases b <;> decide
-- ANCHOR_END: sol1

-- ANCHOR: sol2
/-- Exercise 2: ReLU is idempotent. -/
theorem relu_idem (x : Int) : relu (relu x) = relu x := by
  unfold relu
  by_cases h : 0 ≤ x <;> simp [h]
-- ANCHOR_END: sol2

-- ANCHOR: sol3
/-- Exercise 3: tanh is odd, using only `exp (x + y) = exp x · exp y` and `exp 0 = 1`
(through the non-vanishing of the denominator, which is a hypothesis). -/
theorem tanh_odd {α : Type} [Field α] [HasExp α] (x : α)
    (h : HasExp.exp x + HasExp.exp (-x) ≠ 0) : tanh (-x) = -tanh x := by
  unfold tanh
  rw [show - -x = x by grind]
  have h' : HasExp.exp (-x) + HasExp.exp x ≠ 0 := by grind
  grind
-- ANCHOR_END: sol3

end LeanDL.Ch01
