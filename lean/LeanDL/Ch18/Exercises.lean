import LeanDL.Ch05.Optim
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

-- ANCHOR: ex4
/-- Exercise 4: **the power law multiplies.** `powN b (t + u) = powN b t * powN b u` —
the algebraic shape behind every scaling law: a factor written as a power of a fixed base
turns *sums* of exponents into *products* of factors (so doubling training time multiplies
the remaining-error factor by a constant).
(Hints: induct on `u`; `powN b 0 = 1` is `rfl`-reducible via `powN`; the step is
`Rat.mul_assoc` after rewriting both `powN (· + 1)` unfoldings.) -/
theorem exercise_pow_add (b : Rat) (t u : Nat) :
    Ch05.powN b (t + u) = Ch05.powN b t * Ch05.powN b u := by
  sorry
-- ANCHOR_END: ex4

-- ANCHOR: ex5
variable [LawfulLog]
/-- Exercise 5: **the distillation gap is exactly the KL.** The excess cross-entropy a
student pays over the teacher's entropy is *precisely* `kl t s` — so `distill_ge_entropy`
is one half of a two-sided identity: distillation cannot beat the entropy floor, and the
price of a wrong student is measured in exact nats.
(Hint: `variable [LawfulLog]` is needed; `Dist.crossEntropy_eq_entropy_add_kl` is the
identity, and the rest is `grind`.) -/
theorem exercise_distill_gap {n : Nat} (t s : Dist n) :
    t.crossEntropy s - t.entropy = t.kl s := by
  sorry
-- ANCHOR_END: ex5

end LeanDL.Ch18
