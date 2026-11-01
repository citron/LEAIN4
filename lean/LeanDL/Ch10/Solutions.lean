import LeanDL.Ch10.Vae

/-! Solutions for the Chapter 10 exercises. -/

namespace LeanDL.Ch10

open Lean.Grind LeanDL.Ch04

variable {α : Type} [CommRing α] [HasAct α]

theorem exercise_reparam_zero_noise_solution (x : Vec α 2) :
    (reparamE (0 : α)).eval x = x 0 := by
  simp only [reparamE, Expr.eval]
  grind

theorem exercise_kl_zero_mean_solution (half : α) (x : Vec α 2) (hμ : x 0 = 0) :
    (klE half).eval x = half * (HasExp.exp (x 1) - (1 + x 1)) := by
  simp only [klE, Expr.eval, hμ]
  grind

end LeanDL.Ch10