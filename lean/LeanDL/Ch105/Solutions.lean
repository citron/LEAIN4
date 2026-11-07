import LeanDL.Ch105.Boltzmann

/-! Solutions for the Chapter 10.5 exercises. -/

namespace LeanDL.Ch105

open Lean.Grind

-- ANCHOR: sol1
theorem exercise_qh_off_sum_solution (a : Rat) (ha : 0 < a) :
    qh a 1 1 0 0 + qh a 1 1 0 1 = 1 := by
  have hA : (1 + a) * (1 + a)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  unfold qh
  simp only [Rat.div_def]
  push_cast
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_qv_off_sum_solution (a b : Rat) (hb : 0 < b) :
    qv a b 1 0 0 + qv a b 1 0 1 = 1 := by
  have hB : (1 + b) * (1 + b)⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  unfold qv
  simp only [Rat.div_def]
  push_cast
  grind
-- ANCHOR_END: sol2

-- ANCHOR: sol3
theorem exercise_Z_pos_solution (a b g : Rat) (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    0 < Z a b g := by
  unfold Z
  grind
-- ANCHOR_END: sol3

end LeanDL.Ch105
