import LeanDL.Ch18.Efficiency

/-! Exercises for Chapter 18. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch18

open Lean.Grind LeanDL

-- ANCHOR: ex1
/-- Exercise 1: **quantization is monotone.** A larger input never quantizes to a smaller
grid point. (Hints: `Rat.div_def` rewrites `x / s` as `x * s⁻¹`; `Rat.floor_monotone`
lifts `a ≤ b` to `a.floor ≤ b.floor`; casting the floor inequality needs a `cast` step.) -/
theorem exercise_quant_mono (s x y : Rat) (hs : 0 < s) (h : x ≤ y) :
    quant s x ≤ quant s y := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: **shifting by one grid step shifts the code by one.** Quantizing `x + s`
gives exactly the code of `x` plus one step — the grid is perfectly translation-invariant,
which is why quantized arithmetic can track its own offset.
(Hints: `(x + s) / s = x / s + 1` via `Rat.add_mul` and `Rat.mul_inv_cancel`;
`Rat.floor_add_one` is `Rat.floor (a + 1) = Rat.floor a + 1`.) -/
theorem exercise_quant_translate (s x : Rat) (hs : 0 < s) :
    quant s (x + s) = quant s x + s := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: **the uniform router attains the load-balance floor exactly.** With `p i = 1 / E`
on all `E ≥ 1` experts, the collision loss `Σᵢ pᵢ²` is exactly `1 / E` — the bound of
`balance_ge` is tight, not just a slack estimate.
(Hint: `vsum_const` computes the sum of a constant vector: `vsum (fun _ => c) = E * c`.) -/
theorem exercise_uniform_attains {E : Nat} (hE : 0 < E) :
    vsum (fun _ : Fin E => (E : Rat)⁻¹ * (E : Rat)⁻¹) = (E : Rat)⁻¹ := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch18
