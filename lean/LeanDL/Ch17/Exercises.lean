import LeanDL.Ch17.Contrastive

/-! Exercises for Chapter 17. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch17

open Lean.Grind LeanDL.Ch16

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat] [MonotoneExp (α := Rat)]

-- ANCHOR: ex1
/-- Exercise 1: **adding one more negative raises the collapsed floor by exactly
`log ((n + 2) / (n + 1))`**: with every candidate scoring the same, the loss is the log of
the number of candidates, so the marginal cost of the next negative is the log of the ratio.
(Hint: `log (a * b) = log a + log b` for positive `a, b`, and `(n + 2) = (n + 1) *
((n + 2) / (n + 1))` — read the division as a multiplication by the inverse.) -/
theorem exercise_collapse_step {n : Nat} (c : Rat) (hc : c ≠ 0) (τ : Rat) (hτ : 0 < τ) :
    infoNce τ hτ (collapseSample (n := n + 1) c)
      = infoNce τ hτ (collapseSample (n := n) c)
        + LawfulLog.log (((n + 2 : Nat) : Rat) / ((n + 1 : Nat) : Rat)) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: **zero loss means total confidence on the positive.** If the InfoNCE loss is
`0`, the positive's softmax mass is exactly `1` (hint: `log x ≤ x − 1`, so `0 = −log p`
forces `1 ≤ p`; and no mass of a distribution exceeds `1` — reuse `infoNce_ge_zero`'s
inequality chain: the mass is `≤ 1` because its numerator is `≤ Z`). -/
theorem exercise_zero_loss {n : Nat} (τ : Rat) (hτ : 0 < τ) (s : Samples n)
    (h : infoNce τ hτ s = 0) :
    softmax (Vec.smul τ⁻¹ (score s)) 0 = 1 := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: **temperature `τ = 1` is distribution-preserving on the score vector
itself**: the softmax of any score vector is a distribution (strictly positive, sums
to `1`). State and prove it for `z : Vec Rat (n + 1)` directly from `softmax_dist`. -/
theorem exercise_softmax_total {n : Nat} (z : Vec Rat (n + 1)) :
    Vec.dot (softmax z) (fun _ => (1 : Rat)) = 1 := by
  sorry
-- ANCHOR_END: ex3

end LeanDL.Ch17
