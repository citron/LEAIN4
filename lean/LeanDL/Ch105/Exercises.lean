import LeanDL.Ch105.Boltzmann

/-! Exercises for Chapter 10.5. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch105

open Lean.Grind

-- ANCHOR: ex1
/-- Exercise 1: the conditional on the hidden unit is normalized in the visible-off
row: `qh a b g 0 0 + qh a b g 0 1 = 1`. Use the cross-multiplication helper
`field_eq` and the cancellation `(1 + a) * (1 + a)⁻¹ = 1`. -/
theorem exercise_qh_off_sum (a : Rat) (ha : 0 < a) :
    qh a 1 1 0 0 + qh a 1 1 0 1 = 1 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the visible-off conditional on the visible unit is normalized:
`qv a 1 1 0 0 + qv a 1 1 0 1 = 1` (the row `h = 0` of the visible conditional). -/
theorem exercise_qv_off_sum (a b : Rat) (hb : 0 < b) :
    qv a b 1 0 0 + qv a b 1 0 1 = 1 := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: the partition function of the canonical machine is strictly
positive when every coupling is positive (reprove `Z_pos` from the definition). -/
theorem exercise_Z_pos (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    0 < Z a b g := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch105
