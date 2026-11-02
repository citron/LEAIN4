import LeanDL.Ch18.Exercises

/-! Solutions for Chapter 18. -/

namespace LeanDL.Ch18

open Lean.Grind LeanDL

-- ANCHOR: sol1
/-- Solution 1: rewrite divisions as multiplications by the inverse, transport the
inequality through the inverse (positive, so order-preserving), apply
`Rat.floor_monotone`, cast, and multiply back by the nonnegative step. -/
theorem exercise_quant_mono_solution (s x y : Rat) (hs : 0 < s) (h : x ≤ y) :
    quant s x ≤ quant s y := by
  show ↑(x / s).floor * s ≤ ↑(y / s).floor * s
  have hinv : 0 < s⁻¹ := (Rat.inv_pos (a := s)).mpr hs
  have hdiv : x / s ≤ y / s := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hinv)
  have hfl : (x / s).floor ≤ (y / s).floor := Rat.floor_monotone hdiv
  have hcast : ((x / s).floor : Rat) ≤ (y / s).floor := by exact_mod_cast hfl
  exact Rat.mul_le_mul_of_nonneg_right hcast (Rat.le_of_lt hs)
-- ANCHOR_END: sol1

-- ANCHOR: sol2
/-- Solution 2: `(x + s) / s = x / s + 1` (multiply out, cancel `s · s⁻¹`), so the floor
gains exactly `1` (`Rat.floor_add_one`), and one extra `s` distributes out of the cast. -/
theorem exercise_quant_translate_solution (s x : Rat) (hs : 0 < s) :
    quant s (x + s) = quant s x + s := by
  show ↑((x + s) / s).floor * s = ↑(x / s).floor * s + s
  have hs' : s ≠ 0 := Rat.ne_of_gt hs
  have hdiv : (x + s) / s = x / s + 1 := by
    show (x + s) * s⁻¹ = x * s⁻¹ + 1
    rw [Rat.add_mul, Rat.mul_inv_cancel s hs']
  have hfl : ((x + s) / s).floor = (x / s).floor + 1 := by
    rw [hdiv, Rat.floor_add_one]
  have hcast : ↑((x / s).floor + 1 : Int) * s = ↑(x / s).floor * s + s := by
    push_cast
    grind [Rat.add_mul]
  rw [hfl]
  exact hcast
-- ANCHOR_END: sol2

-- ANCHOR: sol3
/-- Solution 3: the summand is the constant `(1/E) · (1/E)`, so `vsum_const` gives
`E · ((1/E) · (1/E)) = 1/E` after cancelling one inverse. -/
theorem exercise_uniform_attains_solution {E : Nat} (hE : 0 < E) :
    vsum (fun _ : Fin E => (E : Rat)⁻¹ * (E : Rat)⁻¹) = (E : Rat)⁻¹ := by
  rw [vsum_const]
  rw [← Rat.mul_assoc, Rat.mul_inv_cancel (a := (E : Rat))]
  · grind
  · norm_cast
    omega
-- ANCHOR_END: sol3

end LeanDL.Ch18
