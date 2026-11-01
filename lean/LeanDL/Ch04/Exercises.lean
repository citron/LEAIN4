import LeanDL.Ch04.Network

/-! Exercises for Chapter 4. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch04

open Lean.Grind

variable {α : Type} [CommRing α] [HasAct α]

-- ANCHOR: ex1
/-- Exercise 1: the delta rule for the bias, `∂L/∂b = 2 (σ(u) - y) · σ(u)(1 - σ(u))`. -/
theorem exercise_delta_rule_bias (x0 x1 y : α) (w : Vec α 3) :
    let u := w 0 * x0 + w 1 * x1 + w 2
    ((neuronLoss x0 x1 y).backprop w).getD 2 0 =
      2 * (HasAct.sigmoid u - y) * (HasAct.sigmoid u * (1 - HasAct.sigmoid u)) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: backpropagation through a product gives the *other* factor. -/
theorem exercise_product_grad (x : Vec α 2) :
    ((Expr.mul (.var 0) (.var 1) : Expr α 2).backprop x).getD 0 0 = x 1 := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch04