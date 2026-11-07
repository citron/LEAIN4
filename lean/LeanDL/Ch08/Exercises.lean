import LeanDL.Ch08.CellPath

/-! Exercises for Chapter 8. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch08

open LeanDL.Ch05

-- ANCHOR: ex1
/-- Exercise 1: unfold the product of three forget gates. -/
theorem exercise_prodF_three {α : Type} [Lean.Grind.CommRing α] (f : Nat → α) :
    prodF f 3 = f 0 * f 1 * f 2 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: a product of non-negative gates is non-negative (by induction). -/
theorem exercise_prodF_nonneg (f : Nat → Rat) (h : ∀ t, 0 ≤ f t) : ∀ t, 0 ≤ prodF f t := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3 (GRU): the state gradient of the plain-RNN recurrence
`h_{t+1} = w · h_t + u_t` is the product of the *same* weight at every step. -/
theorem exercise_prodF_const (w : Rat) : ∀ t, prodF (fun _ => w) t = powN w t := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch08