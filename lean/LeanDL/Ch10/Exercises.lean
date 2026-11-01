import LeanDL.Ch10.Vae

/-! Exercises for Chapter 10. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch10

open Lean.Grind LeanDL.Ch04

variable {α : Type} [CommRing α] [HasAct α]

-- ANCHOR: ex1
/-- Exercise 1: with zero noise the reparameterised sample is the mean. -/
theorem exercise_reparam_zero_noise (x : Vec α 2) : (reparamE (0 : α)).eval x = x 0 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the KL penalty when the mean is zero. -/
theorem exercise_kl_zero_mean (half : α) (x : Vec α 2) (hμ : x 0 = 0) :
    (klE half).eval x = half * (HasExp.exp (x 1) - (1 + x 1)) := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch10