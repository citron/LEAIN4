import LeanDL.Ch13.Rl

/-! Solutions for the Chapter 13 exercises. -/

namespace LeanDL.Ch13

open Lean.Grind

variable {α : Type} [CommRing α]

theorem exercise_td_fixed_solution (q eta : α) : tdUpdate q q eta = q := by
  simp only [tdUpdate]
  grind

theorem exercise_valueIter_fixed_solution (r g vs : α) (h : vs = r + g * vs) (k : Nat) :
    valueIter r g vs k = vs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [valueIter, ih]; grind

end LeanDL.Ch13