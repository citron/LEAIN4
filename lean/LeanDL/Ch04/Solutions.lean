import LeanDL.Ch04.Network

/-! Solutions for the Chapter 4 exercises. -/

namespace LeanDL.Ch04

open Lean.Grind

variable {α : Type} [CommRing α] [HasAct α]

/-- Exercise 3: the delta rule for the bias,
`∂L/∂b = 2 (σ(u) - y) · σ(u)(1 - σ(u))`. -/
theorem delta_rule_bias (x0 x1 y : α) (w : Vec α 3) :
    let u := w 0 * x0 + w 1 * x1 + w 2
    ((neuronLoss x0 x1 y).backprop w).getD 2 0 =
      2 * (HasAct.sigmoid u - y) * (HasAct.sigmoid u * (1 - HasAct.sigmoid u)) := by
  intro u
  have := backprop_correct w (neuronLoss x0 x1 y) 2
  simp only [Fin.val_two] at this
  rw [this]
  simp [neuronLoss, sqErr, Expr.deriv, Expr.eval, u]
  grind

end LeanDL.Ch04
