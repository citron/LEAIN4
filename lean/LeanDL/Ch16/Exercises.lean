import LeanDL.Ch16.Tools

/-! Exercises for Chapter 16. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch16

open Lean.Grind

variable [LawfulLog]

-- ANCHOR: ex1
/-- Exercise 1: expectation is **linear over subtraction**:
`E[f - g] = E[f] - E[g]`. The addition half is `expect_add`; this one needs
the dot product distributing over a difference. -/
theorem exercise_expect_sub {n : Nat} (p : Dist n) (f g : Vec Rat n) :
    p.expect (fun i => f i - g i) = p.expect f - p.expect g := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: on a **single-point** distribution there is nothing to
predict: any two distributions over one point have `KL = 0`. (Hint: a
distribution on one point puts all its mass there; then the two logs are
equal.) -/
theorem exercise_kl_single (p q : Dist 1) : p.kl q = 0 := by
  sorry
-- ANCHOR_END: ex2

-- ANCHOR: ex3
/-- Exercise 3: a **constant** has zero variance: a non-random quantity has
no spread. -/
theorem exercise_variance_const {n : Nat} (p : Dist n) (c : Rat) :
    p.variance (fun _ => c) = 0 := by
  sorry
-- ANCHOR_END: ex3

-- ANCHOR: ex4
/-- Exercise 4: a **certain** distribution has zero entropy: `H = 0` on one
point — a certain outcome surprises nobody. -/
theorem exercise_entropy_single (p : Dist 1) : p.entropy = 0 := by
  sorry
-- ANCHOR_END: ex4

-- ANCHOR: ex5
/-- Exercise 5: an **ensemble of one** has no variance. With `p : Dist 1`
(the single hypothesis taken with probability one), the variance term of the
bias–variance decomposition is `0` at every input: a deterministic model
neither averages away variance nor creates any. (Hint: on one point the
weighted sum collapses — `Vec.dot` on `Fin 1` is a single multiplication,
and `p.sum1` says its weight is `1`.) -/
theorem exercise_variance_single {n : Nat} (p : Dist 1) (f : Fin 1 → Vec Rat n)
    (i : Fin n) :
    Vec.dot p.w (fun k => (f k i - p.wavg f i) * (f k i - p.wavg f i)) = 0 := by
  sorry
-- ANCHOR_END: ex5

end LeanDL.Ch16
