import LeanDL.Ch08.CellPath

/-! Solutions for the Chapter 8 exercises. -/

namespace LeanDL.Ch08

open LeanDL.Ch05

-- ANCHOR: sol1
theorem exercise_prodF_three_solution {α : Type} [Lean.Grind.CommRing α] (f : Nat → α) :
    prodF f 3 = f 0 * f 1 * f 2 := by
  simp only [prodF]
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_prodF_nonneg_solution (f : Nat → Rat) (h : ∀ t, 0 ≤ f t) :
    ∀ t, 0 ≤ prodF f t
  | 0 => by simp only [prodF]; grind
  | t + 1 => by
    simp only [prodF]
    exact Rat.mul_nonneg (h t) (exercise_prodF_nonneg_solution f h t)
-- ANCHOR_END: sol2

-- ANCHOR: sol3
theorem exercise_prodF_const_solution (w : Rat) : ∀ t, prodF (fun _ => w) t = powN w t := by
  intro t
  induction t with
  | zero => simp only [prodF, powN]
  | succ t ih =>
    simp only [prodF, powN]
    rw [ih]
-- ANCHOR_END: sol3

end LeanDL.Ch08