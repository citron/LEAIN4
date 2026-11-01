import LeanDL.Core.Vec

/-!
# Chapter 5, part 3 — Normalisation

Layer normalisation first *centres* its input. We prove that centring works: the entries of
`x - mean x` sum to zero.
-/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type}

/-- The scalar `n`, built by counting (avoids any cast lemma). -/
def cnt [Add α] [OfNat α 0] [OfNat α 1] : Nat → α
  | 0 => 0
  | n + 1 => cnt n + 1

/-- Sum of the entries. -/
def vsum [Add α] [OfNat α 0] : {n : Nat} → Vec α n → α
  | 0, _ => 0
  | _ + 1, x => x 0 + vsum (fun i => x i.succ)

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
