import LeanDL.Ch05.Optim

/-! Solutions for the Chapter 5 exercises. -/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type} [CommRing α]

theorem exercise_sgd_two_steps_solution (η a w : α) :
    sgdQuad η a w 2 = (1 - η * a) * ((1 - η * a) * w) := by
  rw [sgdQuad_closed η a 2 w]
  simp only [powN]
  grind

theorem exercise_ema_first_solution (β g : α) : ema β g 1 = (1 - β) * g := by
  simp only [ema]
  grind

end LeanDL.Ch05