import LeanDL.Ch17.Contrastive

/-! Solutions for Chapter 17. -/

namespace LeanDL.Ch17

open Lean.Grind LeanDL.Ch16

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat] [MonotoneExp (α := Rat)]

-- ANCHOR: sol1
/-- Solution 1: rewrite both losses with `infoNce_collapse` — the goal becomes pure `log`
arithmetic — and `log_div` (from `log_mul` and `log_inv`) is exactly the subtraction rule. -/
theorem exercise_collapse_step_solution {n : Nat} (c : Rat) (hc : c ≠ 0) (τ : Rat) (hτ : 0 < τ) :
    infoNce τ hτ (collapseSample (n := n + 1) c)
      = infoNce τ hτ (collapseSample (n := n) c)
        + LawfulLog.log (((n + 2 : Nat) : Rat) / ((n + 1 : Nat) : Rat)) := by
  rw [infoNce_collapse c hc τ hτ, infoNce_collapse c hc τ hτ]
  have hp1 : (0 : Rat) < (n + 1 : Nat) := by
    norm_cast
    omega
  have hp2 : (0 : Rat) < (n + 2 : Nat) := by
    norm_cast
    omega
  have hstep : LawfulLog.log ((n + 2 : Nat) : Rat) - LawfulLog.log ((n + 1 : Nat) : Rat)
      = LawfulLog.log (((n + 2 : Nat) : Rat) / ((n + 1 : Nat) : Rat)) := log_div hp2 hp1
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
/-- Solution 2: `0 = −log p` gives `log p = 0`; the tangent `log p ≤ p − 1` then forces
`1 ≤ p`, and the numerator-against-`Z` bound from `infoNce_ge_zero` gives `p ≤ 1`. -/
theorem exercise_zero_loss_solution {n : Nat} (τ : Rat) (hτ : 0 < τ) (s : Samples n)
    (h : infoNce τ hτ s = 0) :
    softmax (Vec.smul τ⁻¹ (score s)) 0 = 1 := by
  let z : Vec Rat (n + 1) := Vec.smul τ⁻¹ (score s)
  have hneg : -LawfulLog.log (softmax z 0) = 0 := by
    show infoNce τ hτ s = 0
    exact h
  have hlog : LawfulLog.log (softmax z 0) = 0 := by
    rw [← Rat.neg_neg (LawfulLog.log (softmax z 0)), hneg, Rat.neg_zero]
  have hd := softmax_dist (by simp) z
  have hp : 0 < softmax z 0 := hd.1 0
  have hZ : 0 < vsum z := vsum_pos _ (by simp) z
  have hrec : vsum z = HasExp.exp (z 0) + vsum (fun i => z i.succ) := by
    unfold vsum
    rw [Vec.dot, Rat.one_mul]
  have ht : 0 ≤ vsum (fun i => z i.succ) := by
    unfold vsum
    exact dot_nonneg2 (fun _ => (1 : Rat)) (fun i => HasExp.exp (z i.succ))
      (fun _ => by grind) (fun i => Rat.le_of_lt (exp_pos' _))
  have hnum : HasExp.exp (z 0) ≤ vsum z := by
    rw [hrec]
    grind
  have hle : softmax z 0 ≤ 1 := by
    have hstep : (vsum z)⁻¹ * HasExp.exp (z 0) ≤ (vsum z)⁻¹ * vsum z :=
      Rat.mul_le_mul_of_nonneg_left hnum (Rat.le_of_lt (inv_pos' hZ))
    rw [inv_mul_cancel' (Rat.ne_of_gt hZ)] at hstep
    show HasExp.exp (z 0) * (vsum z)⁻¹ ≤ 1
    rw [Rat.mul_comm]
    exact hstep
  have hge : 1 ≤ softmax z 0 := by
    have htl := LawfulLog.log_le (softmax z 0) hp
    rw [hlog] at htl
    grind
  grind
-- ANCHOR_END: sol2

-- ANCHOR: sol3
/-- Solution 3: `n + 1` is positive by `simp`, and `softmax_dist` does the rest. -/
theorem exercise_softmax_total_solution {n : Nat} (z : Vec Rat (n + 1)) :
    Vec.dot (softmax z) (fun _ => (1 : Rat)) = 1 :=
  (softmax_dist (by simp) z).2
-- ANCHOR_END: sol3

end LeanDL.Ch17
