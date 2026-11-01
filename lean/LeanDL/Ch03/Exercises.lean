import LeanDL.Ch03.Universal

/-! Exercises for Chapter 3. Replace each `sorry`. -/

namespace LeanDL.Ch03

open LeanDL.Ch01

-- ANCHOR: ex1
/-- Exercise 1: a 2-layer network computing XNOR. -/
def xnorNet : MLP Int 2 1 := sorry

theorem xnorNet_correct (a b : Bool) :
    xnorNet.forward step step (v2 (b2i a) (b2i b)) 0 = b2i (a == b) := by
  sorry
-- ANCHOR_END: ex1

end LeanDL.Ch03
