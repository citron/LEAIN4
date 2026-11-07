import LeanDL.Ch17.Contrastive

/-!
# Chapter 19 — Multimodal learning: two encoders, one shared space

CLIP-style models train **two encoders** — one for images, one for texts — into a
shared embedding space. The training signal is the **symmetric InfoNCE loss**: for a
batch of `B` pairs, every image is a query against `B` texts (its own text is the
positive, the other `B − 1` are negatives), and symmetrically every text is a query
against `B` images. The loss is the **average of the two directions**.

Chapter 17 built the one-directional machine: `Samples`, `score`, `infoNce`, the
`log (n + 1)` collapse floor, and the matched pair `matched hi lo` with its closed
form `log (1 + exp (lo − hi))`. This chapter composes it in both directions and
proves the three facts every CLIP run shows:

* the symmetric loss is `≥ 0` (average of two nonnegative losses);
* a **collapsed** model — every embedding equal — loses exactly `log (n + 1)` in
  each direction, so the averaged floor is the SAME constant: read it off the curve;
* with one negative pair, the symmetric loss is the **sum of two softplus gaps
  divided by 2**, over the same positive score: `S = x₁·y₁`. Both directions see
  the same positive, two different negatives.

The score-symmetry lemma (`col_is_matched`) is the formal core of "two encoders,
one dot product": the text-to-image row of the batch is *the same matched machine*
with the scores transposed — no new loss, one machine, two orientations.
-/

namespace LeanDL.Ch19

open Lean.Grind LeanDL.Ch16 LeanDL.Ch17

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat] [MonotoneExp (α := Rat)]

/-- A (query, positive, negatives) sample built from raw vectors: `x` is one
image embedding (a scalar here — the theorems do not need more), `y` its text,
`negs` the other texts. -/
def pairSample {n : Nat} (x y : Rat) (negs : Vec Rat n) : Samples n :=
  { q := x, pos := y, neg := negs }

/-- Score congruence: equal score vectors give equal InfoNCE. The loss only
sees scores, so any two encoders with the same score matrix are the same model. -/
theorem infoNce_ext {n : Nat} (τ : Rat) (hτ : 0 < τ) {s s' : Samples n}
    (h : score s = score s') : infoNce τ hτ s = infoNce τ hτ s' := by
  show -LawfulLog.log (softmax (Vec.smul τ⁻¹ (score s)) 0)
      = -LawfulLog.log (softmax (Vec.smul τ⁻¹ (score s')) 0)
  rw [h]

-- ANCHOR: symm
/-- **The symmetric (CLIP-style) loss**: the average of image-to-text InfoNCE
and text-to-image InfoNCE. Each direction is Chapter 17's machine; the model
pays for both. -/
def symmInfoNce {n : Nat} (τ : Rat) (hτ : 0 < τ)
    (s s' : Samples n) : Rat :=
  (infoNce τ hτ s + infoNce τ hτ s') / 2

/-- **The symmetric loss is nonnegative**: an average of two nonnegative
losses (`infoNce_ge_zero`, twice). -/
-- ANCHOR_END: symm
theorem symm_ge_zero {n : Nat} (τ : Rat) (hτ : 0 < τ) (s s' : Samples n) :
    0 ≤ symmInfoNce τ hτ s s' := by
  have h1 : 0 ≤ infoNce τ hτ s := infoNce_ge_zero τ hτ s
  have h2 : 0 ≤ infoNce τ hτ s' := infoNce_ge_zero τ hτ s'
  show 0 ≤ (infoNce τ hτ s + infoNce τ hτ s') / 2
  rw [Rat.div_def]
  grind

-- ANCHOR: collapse
/-- **Collapse in both directions**: every embedding equal to `e ≠ 0`, so every
score is `e · e`; each direction hits the Chapter 17 floor `log (n + 1)`, and
the average of two identical floors is the same floor. The CLIP training curve
starts exactly here. -/
theorem symm_collapse {n : Nat} (e : Rat) (he : e ≠ 0) (τ : Rat) (hτ : 0 < τ) :
    symmInfoNce τ hτ
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      = LawfulLog.log ((n + 1 : Nat) : Rat) := by
  have hc : 0 < e * e := sq_pos' he
  have hne : e * e ≠ 0 := Rat.ne_of_gt hc
  have hsc : score (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n))) =
      (fun _ : Fin (n + 1) => e * e) := by
    funext i
    show (if h : i.val = 0 then e * e
          else e * ((fun _ => e) : Vec Rat n) ⟨i.val - 1, by omega⟩) = e * e
    split <;> grind
  have hcollapse_score :
      score (collapseSample (n := n) (c := e * e)) = (fun _ : Fin (n + 1) => e * e) := by
    funext i
    show (if h : i.val = 0 then (1 : Rat) * (e * e)
          else (1 : Rat) * ((fun _ => e * e) : Vec Rat n) ⟨i.val - 1, by omega⟩) = e * e
    split <;> grind
  have h1 : infoNce τ hτ
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      = LawfulLog.log ((n + 1 : Nat) : Rat) := by
    have hlink : score (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
        = score (collapseSample (n := n) (c := e * e)) := by
      rw [hsc, hcollapse_score]
    rw [infoNce_ext τ hτ hlink]
    exact infoNce_collapse (n := n) (c := e * e) hne τ hτ
  show (infoNce τ hτ
        (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      + infoNce τ hτ
        (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))) / 2 = _
  rw [h1]
  show (LawfulLog.log ((n + 1 : Nat) : Rat) + LawfulLog.log ((n + 1 : Nat) : Rat)) / 2
      = LawfulLog.log ((n + 1 : Nat) : Rat)
  rw [Rat.div_def]
  grind

-- ANCHOR_END: collapse
/-- **The row direction is the matched pair.** Query = image `x₁`, positive =
its text `y₁`, negative = the other text `y₂`: the score vector is exactly
`score (matched (x₁·y₁) (x₁·y₂))`. One batch row = one Chapter 17 matched pair. -/
theorem row_is_matched (x1 y1 y2 : Rat) :
    score (pairSample x1 y1 (fun _ => y2)) = score (matched (x1 * y1) (x1 * y2)) := by
  funext i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · simp [score, pairSample, matched]
    · simp [score, pairSample, matched]

/-- **The column direction is the transposed matched pair.** Query = text `y₁`,
positive = its image `x₁`, negative = the other image `x₂`: scores `(x₁·y₁, y₁·x₂)`.
This is the formal content of "two encoders, one dot product": the transposed
batch is the SAME machine with transposed scores. -/
theorem col_is_matched (x1 y1 x2 : Rat) :
    score (pairSample y1 x1 (fun _ => x2)) = score (matched (x1 * y1) (y1 * x2)) := by
  funext i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · simp [score, pairSample, matched, Rat.mul_comm]
    · simp [score, pairSample, matched]

-- ANCHOR: matched
/-- **The symmetric matched loss, closed form.** For the 2×2 batch
`(x₁, y₁) (x₂, y₂)`, the CLIP loss (mean of the two directions, `τ = 1`) is

`[ log (1 + exp (x₁·y₂ − x₁·y₁)) + log (1 + exp (y₁·x₂ − x₁·y₁)) ] / 2`

— the average of two softplus gaps **over the same positive score** `S = x₁·y₁`.
Both directions share one positive and differ only in which modality's
mismatch is the negative. Every gradient step improves `S` against BOTH gaps. -/
theorem symm_matched (x1 y1 x2 y2 : Rat) :
    symmInfoNce (n := 1) 1 (by grind)
      (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))
    = (LawfulLog.log (1 + HasExp.exp (x1 * y2 - x1 * y1))
      + LawfulLog.log (1 + HasExp.exp (y1 * x2 - x1 * y1))) / 2 := by
  have hrw : infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      = infoNce 1 (by grind) (matched (x1 * y1) (x1 * y2)) :=
    infoNce_ext _ _ (row_is_matched x1 y1 y2)
  have hcl : infoNce 1 (by grind) (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))
      = infoNce 1 (by grind) (matched (x1 * y1) (y1 * x2)) :=
    infoNce_ext _ _ (col_is_matched x1 y1 x2)
  show (infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      + infoNce 1 (by grind) (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))) / 2 = _
  rw [hrw, hcl, matched_loss, matched_loss]

-- ANCHOR_END: matched
/-- **Both directions separated ⇒ symmetric loss ≤ log 2.** If the positive
score beats both mismatches (`x₁·y₂ ≤ x₁·y₁` and `y₁·x₂ ≤ x₁·y₁`), each
direction's loss is at most the collapsed matched loss `log 2`
(`matched_mono` + `matched_equal`), so the average is too. The loss of a model
that is *right in both directions* is bounded by the one-negative collapse
floor — the loss cannot tell you the model is perfect, only that it is below
the floor. -/
theorem symm_le_log_two (x1 y1 x2 y2 : Rat)
    (h21 : x1 * y2 ≤ x1 * y1) (h12 : y1 * x2 ≤ x1 * y1) :
    symmInfoNce (n := 1) 1 (by grind)
      (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))
      ≤ LawfulLog.log 2 := by
  have hrowloss : infoNce 1 (by grind) (matched (x1 * y1) (x1 * y2))
      ≤ LawfulLog.log 2 := by
    have hmono := matched_mono (x1 * y1) (x1 * y1) (x1 * y1) (x1 * y2) (by grind)
    rw [matched_equal] at hmono
    exact hmono
  have hcolloss : infoNce 1 (by grind) (matched (x1 * y1) (y1 * x2))
      ≤ LawfulLog.log 2 := by
    have hmono := matched_mono (x1 * y1) (x1 * y1) (x1 * y1) (y1 * x2) (by grind)
    rw [matched_equal] at hmono
    exact hmono
  have hrw : infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      ≤ LawfulLog.log 2 := by
    rw [infoNce_ext _ _ (row_is_matched x1 y1 y2)]; exact hrowloss
  have hcl : infoNce 1 (by grind) (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))
      ≤ LawfulLog.log 2 := by
    rw [infoNce_ext _ _ (col_is_matched x1 y1 x2)]; exact hcolloss
  show (infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      + infoNce 1 (by grind) (pairSample (n := 1) y1 x1 (fun _ : Fin 1 => x2))) / 2 ≤ LawfulLog.log 2
  rw [Rat.div_def]
  grind

end LeanDL.Ch19
