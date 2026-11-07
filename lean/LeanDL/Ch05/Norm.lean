import LeanDL.Core.Sum

/-!
# Chapter 5, part 3 — Normalisation

`vsum`/`cnt` live in `Core/Sum`; this chapter adds the mean and proves centring.

Layer normalisation first *centres* its input. We prove that centring works: the entries of
`x - mean x` sum to zero.
-/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type}

open LeanDL (cnt vsum)

section Laws

variable [Field α]

theorem vsum_sub_const : ∀ {n : Nat} (x : Vec α n) (c : α),
    vsum (fun i => x i - c) = vsum x - cnt n * c
  | 0, x, c => by simp only [vsum, cnt]; grind
  | n + 1, x, c => by
    have ih := vsum_sub_const (fun i : Fin n => x i.succ) c
    simp only [vsum, cnt]
    rw [ih]
    grind

-- ANCHOR: centering
/-- The mean of the entries. -/
def mean {n : Nat} (x : Vec α n) : α := vsum x / cnt n

/-- After subtracting the mean, the entries sum to zero (when `n ≠ 0`). -/
theorem centered_sum_zero {n : Nat} (x : Vec α n) (hn : (cnt n : α) ≠ 0) :
    vsum (fun i => x i - mean x) = 0 := by
  rw [vsum_sub_const]
  simp only [mean]
  grind
-- ANCHOR_END: centering

end Laws

end LeanDL.Ch05
