import LeanDL.Ch16.Tools
import LeanDL.Ch05.Loss

/-!
# Chapter 17 — Contrastive learning: the InfoNCE loss, exactly

Contrastive methods learn an embedding by *contrasting*: one positive sample against `n`
negatives. The standard loss (InfoNCE) is the cross-entropy of classifying "which candidate
is the positive?", so Chapter 5's cross-entropy machinery and Chapter 16's probability tools
apply verbatim. That buys four facts that explain every contrastive training run:

* the softmax is a genuine distribution: strictly positive weights summing to 1 (no division
  by zero, no zero weights, so `log` of every weight is defined);
* the loss is always `≥ 0`, and it is `0` exactly when the positive carries all the mass;
* a **collapsed** embedding — every candidate scoring the same — loses exactly `log (n + 1)`:
  more negatives, higher floor. That is the constant to read off any training curve;
* chance gives the baseline `log (n + 1)`, and the gradient is `p − onehot`: each candidate
  is pushed with exactly the probability mass it should give up.

All statements are over exact `Rat`, no Mathlib: they are theorems, not plots. The companion
executable `lake exe ch17` checks each one numerically over `Float` — and the gap between
the exact theorems and the `Float` run is the rounding, made visible.
-/

namespace LeanDL.Ch17

open Lean.Grind LeanDL.Ch16

section RatLaws

/-- A dot product of nonnegative vectors is nonnegative (the empty dot is 0). -/
theorem dot_nonneg2 {n : Nat} (w f : Vec Rat n) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ Vec.dot w f := by
  induction n with
  | zero => simp only [Vec.dot]; grind
  | succ n ih =>
      have h0 : 0 ≤ w 0 * f 0 := by
        by_cases h1 : w 0 = 0
        · rw [h1]; grind
        · by_cases h2 : f 0 = 0
          · rw [h2]; grind
          · exact Rat.le_of_lt (Rat.mul_pos
              (Rat.lt_of_le_of_ne (hw 0) (Ne.symm h1))
              (Rat.lt_of_le_of_ne (hf 0) (Ne.symm h2)))
      have ht : 0 ≤ Vec.dot (fun i => w i.succ) (fun i => f i.succ) :=
        ih (fun i => w i.succ) (fun i => f i.succ) (fun i => hw i.succ) (fun i => hf i.succ)
      simp only [Vec.dot]
      grind

/-- `Σᵢ 1 · 1 = n`: counting. -/
theorem dot_ones : ∀ (n : Nat),
    Vec.dot (fun _ : Fin n => (1 : Rat)) (fun _ => (1 : Rat)) = n := by
  intro n
  induction n with
  | zero => simp only [Vec.dot]; grind
  | succ n ih =>
      simp only [Vec.dot, ih]
      push_cast
      grind

/-- `Σᵢ c · 1 = c · n`: summing a constant is the constant times the count. -/
theorem dot_const : ∀ (n : Nat) (c : Rat),
    Vec.dot (fun _ : Fin n => c) (fun _ => (1 : Rat)) = c * n := by
  intro n
  induction n with
  | zero => intro c; simp only [Vec.dot]; grind
  | succ n ih =>
      intro c
      simp only [Vec.dot, ih, Rat.mul_one]
      push_cast
      rw [Rat.mul_add]
      grind

/-- `2⁻¹ + 2⁻¹ = 1` over `Rat`, by computation. -/
theorem two_inv_add : (2 : Rat)⁻¹ + (2 : Rat)⁻¹ = 1 := by grind

/-- `x / 2 + x / 2 = x` (over `Rat`, `x / 2` *is* `x * 2⁻¹`, `Rat.div_def`). -/
theorem half_add (x : Rat) : x / 2 + x / 2 = x := by
  show x * 2⁻¹ + x * 2⁻¹ = x
  rw [← Rat.mul_add, two_inv_add, Rat.mul_one]

/-- A nonzero square is *strictly* positive. -/
theorem sq_pos' {a : Rat} (h : a ≠ 0) : 0 < a * a := by
  by_cases hn : a < 0
  · have h2 : 0 < -a := by grind
    have key : (-a) * (-a) = a * a := by
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    have : 0 < (-a) * (-a) := Rat.mul_pos h2 h2
    rw [key] at this
    exact this
  · have h2 : 0 < a := Rat.lt_of_le_of_ne (Rat.not_lt.mp hn) (Ne.symm h)
    exact Rat.mul_pos h2 h2

/-- `exp x · exp (-x) = 1`: the exponential never vanishes. -/
theorem exp_neg_mul [HasExp Rat] [LawfulExp Rat] (x : Rat) :
    HasExp.exp x * HasExp.exp (-x) = 1 := by
  rw [← LawfulExp.exp_add, show x + -x = (0 : Rat) by grind, LawfulExp.exp_zero]

/-- **`exp` is strictly positive** on `Rat`: `exp x = (exp (x/2))²`, a nonzero square. -/
theorem exp_pos' [HasExp Rat] [LawfulExp Rat] (x : Rat) : 0 < HasExp.exp x := by
  have key : HasExp.exp x = HasExp.exp (x / 2) * HasExp.exp (x / 2) := by
    have h : x / 2 + x / 2 = x := half_add x
    have hc := LawfulExp.exp_add (x / 2) (x / 2)
    rw [h] at hc
    exact hc
  rw [key]
  exact sq_pos' (by
    intro heq
    have h1 := exp_neg_mul (x / 2)
    rw [heq, Rat.zero_mul] at h1
    exact absurd h1 (by grind))

/-- `x/y <= 1` when `0 < y` and `x <= y`. -/
theorem div_le_one_of_le {x y : Rat} (hy : 0 < y) (h : x <= y) : x / y <= 1 := by
  rw [Rat.div_def]
  have hinv : 0 <= y⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hy)
  have h2 := Rat.mul_le_mul_of_nonneg_right h hinv
  have hyi : y * y⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  grind

/-- Positive rationals are closed under division. -/
theorem div_pos' {x y : Rat} (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by
  rw [Rat.div_def]
  exact Rat.mul_pos hx (Rat.inv_pos.mpr hy)

end RatLaws

-- ANCHOR: infonce
section InfoNCE

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat]

/-- The partition function `Z = Σᵢ exp (z i)`, as a dot against the constant 1. -/
def vsum {n : Nat} (z : Vec Rat n) : Rat :=
  Vec.dot (fun _ : Fin n => (1 : Rat)) (fun i => HasExp.exp (z i))

/-- The softmax: `exp (z i) / Z`, division read as multiplication by the inverse
(`Rat.div_def`), matching Chapter 16's convention. -/
def softmax {n : Nat} (z : Vec Rat n) : Vec Rat n :=
  fun i => HasExp.exp (z i) * (vsum z)⁻¹

/-- `Z` is strictly positive as soon as there is at least one score. -/
theorem vsum_pos : ∀ (n : Nat), 0 < n → ∀ (z : Vec Rat n), 0 < vsum z := by
  intro n
  induction n with
  | zero => intro hn z; exact absurd hn (Nat.not_lt_zero 0)
  | succ n ih =>
      intro hn z
      have hrec : vsum z = HasExp.exp (z 0) + vsum (fun i => z i.succ) := by
        unfold vsum
        simp only [Vec.dot, Rat.one_mul]
      have h0 : 0 < HasExp.exp (z 0) := exp_pos' _
      rw [hrec]
      cases n with
      | zero =>
          -- empty tail: the sum over zero scores is 0
          have ht : vsum (fun i => z i.succ) = 0 := by
            unfold vsum
            simp only [Vec.dot]
          rw [ht]
          grind
      | succ n =>
          have ht : 0 < vsum (fun i => z i.succ) := ih (Nat.succ_pos n) (fun i => z i.succ)
          grind

/-- **The softmax is a distribution**: strictly positive weights summing to 1. This is exactly
the hypothesis `Dist` needs, so entropy, KL and cross-entropy from Chapter 16 apply to it. -/
theorem softmax_dist {n : Nat} (hn : 0 < n) (z : Vec Rat n) :
    (∀ i, 0 < softmax z i) ∧ Vec.dot (softmax z) (fun _ => (1 : Rat)) = 1 := by
  have hZ : 0 < vsum z := vsum_pos n hn z
  constructor
  · intro i
    show 0 < HasExp.exp (z i) * (vsum z)⁻¹
    exact Rat.mul_pos (exp_pos' _) (Rat.inv_pos.mpr hZ)
  · show Vec.dot (fun i => HasExp.exp (z i) * (vsum z)⁻¹) (fun _ => (1 : Rat)) = 1
    have hsc : Vec.dot (fun i => HasExp.exp (z i) * (vsum z)⁻¹) (fun _ => (1 : Rat))
        = Vec.dot (fun i => (vsum z)⁻¹ * HasExp.exp (z i)) (fun _ => (1 : Rat)) := by
      congr 1
      funext i
      rw [Rat.mul_comm]
    rw [hsc, Vec.dot_smul_left (vsum z)⁻¹, Vec.dot_comm,
      show Vec.dot (fun _ : Fin n => (1 : Rat)) (fun i => HasExp.exp (z i)) = vsum z from rfl,
      inv_mul_cancel' (Rat.ne_of_gt hZ)]

-- ANCHOR: softmax_blend
/-- **An attention blend of bounded values stays bounded.** The softmax
weights are nonnegative and sum to 1 (`softmax_dist`), so blending value
vectors whose every coordinate lies in `[-M, M]` produces a coordinate
again in `[-M, M]` — the attention output of the `lake exe gpt` demo is
carried by this exact bound, not by hope. The same lemma is the
ensemble-average case of Chapter 16's bias-variance story. -/
theorem softmax_blend_bound {n : Nat} (hn : 0 < n) (z v : Vec Rat n) (M : Rat)
    (hb : ∀ i, Rat.abs (v i) ≤ M) : Rat.abs (Vec.dot (softmax z) v) ≤ M := by
  obtain ⟨hpos, hsum⟩ := softmax_dist hn z
  exact Dist.convex_bound (softmax z) v M (fun i => Rat.le_of_lt (hpos i)) hsum hb
-- ANCHOR_END: softmax_blend

/-- **`log` is monotone** on positive rationals: for `x ≤ y`, the ratio `y / x ≥ 1`, its
inverse is `≤ 1`, the tangent bounds `log (y/x)⁻¹` below 0, and `log_inv` flips the sign. -/
theorem log_mono {x y : Rat} (hx : 0 < x) (hy : 0 < y) (h : x ≤ y) :
    LawfulLog.log x ≤ LawfulLog.log y := by
  have hdiff : LawfulLog.log y - LawfulLog.log x = LawfulLog.log (y / x) := log_div hy hx
  have hxy : 0 < y / x := by show 0 < y * x⁻¹; exact Rat.mul_pos hy (inv_pos' hx)
  have hinvp : 0 < (y / x)⁻¹ := inv_pos' hxy
  have htl : LawfulLog.log ((y / x)⁻¹) ≤ (y / x)⁻¹ - 1 := LawfulLog.log_le _ hinvp
  have hinv_eq : (y / x)⁻¹ = x * y⁻¹ := by
    show (y * x⁻¹)⁻¹ = x * y⁻¹
    rw [Field.inv_mul, Field.inv_inv, Rat.mul_comm]
  have hle1 : (y / x)⁻¹ ≤ 1 := by
    rw [hinv_eq]
    have key : y * y⁻¹ = 1 := Field.mul_inv_cancel (Rat.ne_of_gt hy)
    calc x * y⁻¹ ≤ y * y⁻¹ := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (inv_pos' hy))
      _ = 1 := key
  have hf := LawfulLog.log_inv (y / x) (Rat.ne_of_gt hxy)
  have hflip : LawfulLog.log (y / x) = -LawfulLog.log ((y / x)⁻¹) := by
    rw [show LawfulLog.log (y / x) = -(-LawfulLog.log (y / x)) from (Rat.neg_neg _).symm, ← hf]
  have hle0 : LawfulLog.log ((y / x)⁻¹) ≤ 0 := by grind
  have hge : 0 ≤ LawfulLog.log (y / x) := by rw [hflip]; grind
  have hgoal : 0 ≤ LawfulLog.log y - LawfulLog.log x := by rw [hdiff]; exact hge
  exact (Rat.le_iff_sub_nonneg _ _).mpr hgoal

/-- One contrastive sample: a query embedding `q`, a positive `p`, and `n` negatives. -/
structure Samples (n : Nat) where
  q : Rat
  pos : Rat
  neg : Vec Rat n

/-- The score of candidate `i` against the query: the positive at index 0, the negatives
after. (In practice a cosine of embeddings; a plain product keeps the statements exact.) -/
def score {n : Nat} (s : Samples n) : Vec Rat (n + 1) :=
  fun i => if h : i.val = 0 then s.q * s.pos
           else s.q * s.neg ⟨i.val - 1, by omega⟩

/-- **InfoNCE** at temperature `τ > 0`: the negative log-probability that the softmax over
the `n + 1` candidates places on the positive (index 0). -/
def infoNce {n : Nat} (τ : Rat) (_hτ : 0 < τ) (s : Samples n) : Rat :=
  -LawfulLog.log (softmax (Vec.smul τ⁻¹ (score s)) 0)

/-- **The loss is nonnegative**: the positive's mass is at most 1 (its numerator is at most
the whole partition function), and `log` is bounded above by its tangent, which is `≤ 0` at
a mass `≤ 1`. -/
theorem infoNce_ge_zero {n : Nat} (τ : Rat) (hτ : 0 < τ) (s : Samples n) :
    0 ≤ infoNce τ hτ s := by
  let z : Vec Rat (n + 1) := Vec.smul τ⁻¹ (score s)
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
  show 0 ≤ -LawfulLog.log (softmax z 0)
  have hlog : LawfulLog.log (softmax z 0) ≤ softmax z 0 - 1 := LawfulLog.log_le _ hp
  grind

/-- The collapsed sample: every candidate scores `c`, so the query cannot tell the positive
from the negatives. -/
def collapseSample {n : Nat} (c : Rat) : Samples n :=
  { q := 1, pos := c, neg := fun _ => c }

/-- **Collapse costs exactly `log (n + 1)`** (for a nonzero score): the softmax is uniform,
and the loss is the log of the number of candidates. More negatives, higher floor — the
constant to read off any training curve. -/
theorem infoNce_collapse {n : Nat} (c : Rat) (_hc : c ≠ 0) (τ : Rat) (hτ : 0 < τ) :
    infoNce τ hτ (collapseSample (n := n) c) = LawfulLog.log ((n + 1 : Nat) : Rat) := by
  have hsc : score (collapseSample (n := n) c) = (fun _ : Fin (n + 1) => c) := by
    funext i
    cases i with
    | mk i hi =>
        by_cases h : i = 0
        · simp only [score, collapseSample, h, dite_eq_left]
          show (1 : Rat) * c = c
          grind
        · simp only [score, collapseSample, h, dite_eq_right]
          show (1 : Rat) * c = c
          grind
  show -LawfulLog.log (softmax (Vec.smul τ⁻¹ (score (collapseSample (n := n) c))) 0) =
      LawfulLog.log ((n + 1 : Nat) : Rat)
  rw [hsc]
  have hsm : Vec.smul τ⁻¹ ((fun _ => c) : Vec Rat (n + 1)) = (fun _ => τ⁻¹ * c) := by
    funext i
    show τ⁻¹ * (fun _ => c) i = τ⁻¹ * c
    grind
  rw [hsm]
  have hZ : vsum (fun _ : Fin (n + 1) => τ⁻¹ * c) =
      ((n + 1 : Nat) : Rat) * HasExp.exp (τ⁻¹ * c) := by
    show Vec.dot (fun _ : Fin (n + 1) => (1 : Rat)) (fun _ => HasExp.exp (τ⁻¹ * c)) = _
    rw [dot_smul_const, dot_ones, Rat.mul_comm]
  have hmass : softmax (fun _ : Fin (n + 1) => τ⁻¹ * c) 0 = ((n + 1 : Nat) : Rat)⁻¹ := by
    unfold softmax
    show HasExp.exp (τ⁻¹ * c) * (vsum (fun _ : Fin (n + 1) => τ⁻¹ * c))⁻¹ = _
    rw [hZ, Field.inv_mul ((n + 1 : Nat) : Rat) (HasExp.exp (τ⁻¹ * c))]
    calc HasExp.exp (τ⁻¹ * c) * ((↑(n + 1))⁻¹ * (HasExp.exp (τ⁻¹ * c))⁻¹)
        = (↑(n + 1))⁻¹ * ((HasExp.exp (τ⁻¹ * c))⁻¹ * HasExp.exp (τ⁻¹ * c)) := by
          rw [Rat.mul_comm, Rat.mul_assoc]
      _ = (↑(n + 1))⁻¹ * 1 := by
          rw [inv_mul_cancel' (Rat.ne_of_gt (exp_pos' (_ : Rat)))]
      _ = (↑(n + 1))⁻¹ := Rat.mul_one _
  rw [hmass]
  have hn1 : (0 : Rat) < (n + 1 : Nat) := by
    norm_cast
    omega
  rw [LawfulLog.log_inv ((n + 1 : Nat) : Rat) (Rat.ne_of_gt hn1), Rat.neg_neg]

/-- **The gradient is `p − onehot`**: InfoNCE *is* Chapter 5's cross-entropy on the score
vector with the positive (index 0) as the label, so the gradient identity is inherited
verbatim from `ceLoss_grad` — the positive's logit is pushed up with force `1 − p`, and
every negative's logit is pushed down with exactly the probability mass it should give up.
No new calculus: the theorem is a specialization. -/
theorem infonce_grad {α : Type} [Lean.Grind.CommRing α] [Ch04.HasAct α]
    {m : Nat} (hm : 0 < m) (z : Vec α m) (k : Fin m) :
    ((Ch05.ceLoss (⟨0, hm⟩ : Fin m)).deriv k).eval z =
      Ch05.softmax z k - (if (⟨0, hm⟩ : Fin m) = k then 1 else 0) :=
  Ch05.ceLoss_grad z ⟨0, hm⟩ k

-- ANCHOR: matched
/-- **The matched pair**: one query, one positive (score `hi`), one negative (score
`lo`). `Samples n` has `n + 1` candidates, so `matched hi lo : Samples 1` is the
2-candidate problem — the image-text matching toy of CLIP's paper, exactly. -/
def matched (hi lo : Rat) : Samples 1 :=
  { q := 1, pos := hi, neg := fun _ => lo }

/-- **The key algebra**: `(1 + exp(lo - hi)) * exp hi = exp hi + exp lo`. -/
theorem matched_key (hi lo : Rat) :
    (1 + HasExp.exp (lo - hi)) * HasExp.exp hi = HasExp.exp hi + HasExp.exp lo := by
  have h : HasExp.exp (lo - hi) * HasExp.exp hi = HasExp.exp lo := by
    have h2 : lo - hi + hi = lo := by grind
    rw [← LawfulExp.exp_add, h2]
  rw [Rat.add_mul, Rat.one_mul, h]

theorem matched_score0 (hi lo : Rat) : score (matched hi lo) (0 : Fin 2) = hi := by
  simp [score, matched]

theorem matched_score1 (hi lo : Rat) : score (matched hi lo) (1 : Fin 2) = lo := by
  simp [score, matched]

theorem matched_score_succ (hi lo : Rat) :
    score (matched hi lo) (Fin.succ (0 : Fin 1)) = lo := by
  simp [score, matched]

/-- **The positive's softmax mass, closed form**: `1 / (1 + exp(lo - hi))` — the
sigmoid of the similarity gap. This is the exact curve every contrastive training
run plots: mass `1` when the positive dominates, `1/2` when the model collapses
(`hi = lo`), mass tending to `0` when it gets the pair backwards. -/
theorem matched_mass (hi lo : Rat) :
    softmax (score (matched hi lo)) (0 : Fin 2) = (1 + HasExp.exp (lo - hi))⁻¹ := by
  have hpos : 0 < HasExp.exp hi + HasExp.exp lo := by
    have a := exp_pos' hi
    have b := exp_pos' lo
    grind
  have hinv : HasExp.exp hi * (HasExp.exp hi + HasExp.exp lo)⁻¹ =
      (1 + HasExp.exp (lo - hi))⁻¹ := by
    refine (Rat.inv_eq_of_mul_eq_one ?_).symm
    calc (1 + HasExp.exp (lo - hi)) * (HasExp.exp hi * (HasExp.exp hi + HasExp.exp lo)⁻¹)
        = ((1 + HasExp.exp (lo - hi)) * HasExp.exp hi) *
            (HasExp.exp hi + HasExp.exp lo)⁻¹ := by grind [Rat.mul_assoc]
      _ = (HasExp.exp hi + HasExp.exp lo) * (HasExp.exp hi + HasExp.exp lo)⁻¹ := by
            rw [matched_key]
      _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hpos)
  have hZ : vsum (score (matched hi lo)) = HasExp.exp hi + HasExp.exp lo := by
    unfold vsum
    rw [Vec.dot, matched_score0, Vec.dot, Rat.one_mul, Rat.one_mul]
    show HasExp.exp hi + (HasExp.exp (score (matched hi lo) (Fin.succ (0 : Fin 1))) +
        Vec.dot (fun i : Fin 0 => (1 : Rat))
          (fun i => HasExp.exp (score (matched hi lo) i.succ.succ))) = _
    rw [matched_score_succ]
    unfold Vec.dot
    grind
  unfold softmax
  rw [matched_score0, hZ, hinv]

/-- **The matched loss, closed form**: `log (1 + exp(lo - hi))` — the softplus of
the *negated* similarity gap. The loss is a pure function of the gap: shrink the
gap and the loss grows, exponentially in the difference. -/
theorem matched_loss (hi lo : Rat) :
    infoNce 1 (by grind) (matched hi lo) = LawfulLog.log (1 + HasExp.exp (lo - hi)) := by
  have hgt : 0 < 1 + HasExp.exp (lo - hi) := by
    have := exp_pos' (lo - hi)
    grind
  have hinv1 : (1 : Rat)⁻¹ = 1 := by
    rw [Rat.inv_eq_of_mul_eq_one]
    · grind
  have hsm : (Vec.smul (1 : Rat)⁻¹ (score (matched hi lo)) : Vec Rat 2) =
      score (matched hi lo) := by
    funext i
    show (1 : Rat)⁻¹ * score (matched hi lo) i = score (matched hi lo) i
    rw [hinv1, Rat.one_mul]
  show -LawfulLog.log (softmax (Vec.smul (1 : Rat)⁻¹ (score (matched hi lo))) (0 : Fin 2)) = _
  rw [hsm, matched_mass]
  rw [LawfulLog.log_inv (1 + HasExp.exp (lo - hi)) (Rat.ne_of_gt hgt)]
  exact Rat.neg_neg _

/-- The query cannot separate positive from negative (`hi = lo`): the loss is exactly
`log 2`, and the positive's mass is exactly `1/2`. -/
theorem matched_equal (hi : Rat) :
    infoNce 1 (by grind) (matched hi hi) = LawfulLog.log 2 := by
  rw [matched_loss]
  have h : hi - hi = 0 := by grind
  rw [h, LawfulExp.exp_zero, show (1 : Rat) + 1 = 2 from by grind]

/-- **The matched loss decreases as the gap grows — CONDITIONALLY.** Monotonicity of
`exp` is an *analytic* property of the real exponential; it does NOT follow from
`exp_add`/`exp_zero` alone (any group homomorphism `(Rat, +) -> (Rat, *)` satisfies
those). So it is an explicit, named hypothesis — the honest frontier of this
algebraic layer. The real exponential satisfies it; a wild homomorphism does not. -/
theorem matched_mono
    (hmono : ∀ a b : Rat, a <= b -> HasExp.exp a <= HasExp.exp b)
    (hi₁ lo₁ hi₂ lo₂ : Rat) (h : lo₂ - hi₂ <= lo₁ - hi₁) :
    infoNce 1 (by grind) (matched hi₂ lo₂) <= infoNce 1 (by grind) (matched hi₁ lo₁) := by
  rw [matched_loss, matched_loss]
  have e₂ : HasExp.exp (lo₂ - hi₂) <= HasExp.exp (lo₁ - hi₁) := hmono _ _ h
  have hpos₂ : 0 < 1 + HasExp.exp (lo₂ - hi₂) := by
    have := exp_pos' (lo₂ - hi₂)
    grind
  have hpos₁ : 0 < 1 + HasExp.exp (lo₁ - hi₁) := by
    have := exp_pos' (lo₁ - hi₁)
    grind
  exact log_mono hpos₂ hpos₁ (by grind)
-- ANCHOR_END: matched

-- ANCHOR_END: infonce
end InfoNCE

end LeanDL.Ch17
