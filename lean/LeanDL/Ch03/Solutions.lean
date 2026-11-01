import LeanDL.Ch03.Exercises

/-! Solutions for the Chapter 3 exercises. -/

namespace LeanDL.Ch03

open LeanDL.Ch01

-- ANCHOR: sol1
/-- XNOR = OR (AND x₁ x₂) (NOR x₁ x₂): the hidden layer computes AND and NOR. -/
def xnorNet_solution : MLP Int 2 1 :=
  .cons (h := 2)
    ⟨Mat.ofLists [[1, 1], [-1, -1]], Vec.ofList [-2, 0]⟩
    (.last ⟨Mat.ofLists [[1, 1]], Vec.ofList [-1]⟩)

theorem xnorNet_solution_correct (a b : Bool) :
    xnorNet_solution.forward step step (v2 (b2i a) (b2i b)) 0 = b2i (a == b) := by
  cases a <;> cases b <;> decide
-- ANCHOR_END: sol1

end LeanDL.Ch03
