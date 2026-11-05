import LeanDL.Core.Prob
import LeanDL.Core.Sum
import LeanDL.Ch05.Optim

/-!
# Chapter 5, part 4 — The practitioner's kit

Everything standing between the optimiser theorems of part 2 and a training
run that does not explode. Four devices, each with one load-bearing exact fact:

* **Dropout** — the `1/p` rescaling keeps the expectation exact
  (`dropout_expect`); that is why dropout is skipped at test time.
* **Gradient clipping** — clipping never flips a gradient's sign
  (`clip_align`) and never leaves the box (`clip_bounded`): the step is
  shorter, never reversed.
* **Weight decay, decoupled vs L2** — in plain SGD the two rules are the
  same update (`decay_sgd_eq`); under Adam they are not, because L2's
  decay rides inside the moments and gets rescaled by the normaliser,
  while AdamW's shrink acts on the weight directly.
* **Initialisation** — `Var (c·X) = c² · Var X` (`var_smul`) is the
  algebra of the fan-in rule: Xavier (variance `1/n`) and He (variance
  `2/n`) keep pre-activations at O(1) across layers.

Plus schedules: the geometric sum is exact (`geom_sum`), so an exponential
learning-rate decay spends a **finite** total step budget
(`lr_decay_total`) — the exact difference between "decay" and "decay fast".

All proofs are on exact `Rat`. -/

namespace LeanDL.Ch05

open Lean.Grind
open LeanDL (Dist Vec vsum)

section Dropout

-- ANCHOR: dropout
/-- One dropout unit, expectation model: with probability `p` the signal
passes scaled by `1/p`, otherwise it is zeroed (the two-point Bernoulli
mask of Ch16's `expect`). -/
def dropoutUnit (p x : Rat) : Rat :=
  p * (x / p) + (1 - p) * 0

/-- **Inverted dropout is expectation-exact**: the unit equals `x` whenever
`p > 0`. The `1/p` rescaling is not a heuristic — it is the entire content
of this line, and it is why dropout can be skipped at test time: train and
inference expectations already agree. -/
theorem dropout_expect (p x : Rat) (hp : 0 < p) :
    dropoutUnit p x = x := by
  unfold dropoutUnit
  have hinv : p * p⁻¹ = 1 := Rat.mul_inv_cancel p (Rat.ne_of_gt hp)
  calc p * (x / p) + (1 - p) * 0
      = p * (x * p⁻¹) := by rw [Rat.div_def]; grind
    _ = x := by
        calc p * (x * p⁻¹)
            _ = (p * p⁻¹) * x := by
                  rw [Rat.mul_comm x (p⁻¹), ← Rat.mul_assoc]
            _ = x := by rw [hinv, Rat.one_mul]
-- ANCHOR_END: dropout

end Dropout

section Clipping

-- ANCHOR: clip
/-- Clip to the box `[-c, c]`. -/
def clip (c x : Rat) : Rat :=
  if x < -c then -c else if c < x then c else x

/-- **Clipping never flips a sign**: `0 ≤ x · clip c x` for every `c ≥ 0`.
A clipped gradient step therefore still moves downhill — clipping bounds
the step, it does not reverse it. This is the exact content of the
gradient-clipping heuristic. -/
theorem clip_align (c x : Rat) (hc : 0 ≤ c) : 0 ≤ x * clip c x := by
  by_cases h1 : x < -c
  · have heq : clip c x = -c := by
      unfold clip
      split <;> grind
    rw [heq]
    have hcn : -c ≤ 0 := by
      rw [← Rat.neg_zero]
      exact Rat.neg_le_neg hc
    have hx0 : x ≤ 0 := by grind
    have hprod : x * c ≤ 0 := by
      have h := Rat.mul_le_mul_of_nonneg_right hx0 hc
      rw [Rat.zero_mul c] at h
      exact h
    rw [Rat.mul_neg x c]
    rw [← Rat.neg_zero]
    exact Rat.neg_le_neg hprod
  · by_cases h2 : c < x
    · have heq : clip c x = c := by
        unfold clip
        split <;> grind
      rw [heq]
      have hx : 0 ≤ x := by grind
      exact Rat.mul_nonneg hx hc
    · have heq : clip c x = x := by
        unfold clip
        split <;> grind
      rw [heq]
      exact sq_nonneg x

/-- A clipped value stays in the box: `-c ≤ clip c x ≤ c` — the norm
statement every gradient-clipping rulebook states. -/
theorem clip_bounded (c x : Rat) (hc : 0 ≤ c) :
    -c ≤ clip c x ∧ clip c x ≤ c := by
  constructor
  · by_cases h1 : x < -c
    · have heq : clip c x = -c := by
        unfold clip
        split <;> grind
      rw [heq]
      rw [Rat.le_iff_sub_nonneg]
      grind
    · by_cases h2 : c < x
      · have heq : clip c x = c := by
          unfold clip
          split <;> grind
        rw [heq]
        rw [Rat.le_iff_sub_nonneg]
        grind
      · have heq : clip c x = x := by
          unfold clip
          split <;> grind
        rw [heq]
        grind
  · by_cases h1 : x < -c
    · have heq : clip c x = -c := by
        unfold clip
        split <;> grind
      rw [heq]
      rw [Rat.le_iff_sub_nonneg]
      grind
    · by_cases h2 : c < x
      · have heq : clip c x = c := by
          unfold clip
          split <;> grind
        rw [heq]
        rw [Rat.le_iff_sub_nonneg]
        grind
      · have heq : clip c x = x := by
          unfold clip
          split <;> grind
        rw [heq]
        grind
-- ANCHOR_END: clip

end Clipping

section WeightDecay

-- ANCHOR: decay
/-- **Decoupled decay** (AdamW, Loshchilov & Hutter): a *multiplicative*
shrink `w ← w · (1 - lr·wd)` applied to the weight itself, outside the
moment normaliser. -/
def decoupledShrink (lr wd w : Rat) : Rat := w * (1 - lr * wd)

/-- **Classical L2**: the decay term is added to the *gradient*, so under
Adam it rides inside both moments and is rescaled by the normaliser. -/
def l2Gradient (wd w g : Rat) : Rat := g + wd * w

/-- **In plain SGD the two rules coincide**: adding `wd·w` to the gradient
is the same update as shrinking by `(1 - lr·wd)` and stepping on `g`.
Decoupling is invisible for SGD — its whole point is Adam, where the
normaliser rescales L2's decay and the two rules genuinely differ
(exercise 4 makes this exact at step 1). -/
theorem decay_sgd_eq (lr wd w g : Rat) :
    w - lr * l2Gradient wd w g = decoupledShrink lr wd w - lr * g := by
  unfold decoupledShrink l2Gradient
  grind
-- ANCHOR_END: decay

/-- **Adam's first step is unbiased on constants**: with zero-init moments,
the bias-corrected first moment of a constant gradient `g` is exactly `g`
(same for the second moment, on `g²`). The `(1 - β)` warmup is divided
out exactly — so at step 1 AdamW's shrink is the *only* decay acting on
the weight, while L2's decay has been rescaled by the normaliser. -/
theorem adam_first_step_unbiased (β g : Rat) (h : 1 - powN β 1 ≠ 0) :
    (β * 0 + (1 - β) * g) / (1 - powN β 1) = g :=
  bias_correction (α := Rat) β g 1 h

end WeightDecay

section Init

-- ANCHOR: fanin
/-- **Scaling law of the variance**: `Var (c·X) = c² · Var X`.
This one line is Xavier/He initialisation: drawing weights of variance
`1/n` (Xavier; He/ReLU: `2/n`) at a layer of fan-in `n` keeps the
pre-activation variance at O(1) across layers — a deep net neither
explodes nor vanishes *at init*. -/
theorem var_smul (p : Dist n) (f : Vec Rat n) (c : Rat) :
    p.variance (fun i => c * f i) = c * c * p.variance f := by
  unfold Dist.variance Dist.expect
  have hper : (fun i => (c * f i) * (c * f i))
      = (fun i => c * c * (f i * f i)) := by
    funext i; grind
  have h1 : Vec.dot p.w (fun i => (c * f i) * (c * f i))
      = c * c * Vec.dot p.w (fun i => f i * f i) := by
    rw [hper, Vec.dot_smul_right]
  have h2 : Vec.dot p.w (fun i => c * f i) = c * Vec.dot p.w f :=
    Vec.dot_smul_right c p.w f
  have hprod : (c * Vec.dot p.w f) * (c * Vec.dot p.w f)
      = c * c * (Vec.dot p.w f * Vec.dot p.w f) := by
    calc (c * Vec.dot p.w f) * (c * Vec.dot p.w f)
        = c * (Vec.dot p.w f * (c * Vec.dot p.w f)) :=
          Rat.mul_assoc c (Vec.dot p.w f) (c * Vec.dot p.w f)
      _ = c * ((Vec.dot p.w f * c) * Vec.dot p.w f) := by
          rw [← Rat.mul_assoc (Vec.dot p.w f) c (Vec.dot p.w f)]
      _ = c * ((c * Vec.dot p.w f) * Vec.dot p.w f) := by
          rw [Rat.mul_comm (Vec.dot p.w f) c]
      _ = c * (c * (Vec.dot p.w f * Vec.dot p.w f)) := by
          rw [Rat.mul_assoc c (Vec.dot p.w f) (Vec.dot p.w f)]
      _ = (c * c) * (Vec.dot p.w f * Vec.dot p.w f) := by
          rw [Rat.mul_assoc c c (Vec.dot p.w f * Vec.dot p.w f)]
  rw [h1, h2]
  rw [hprod]
  grind
-- ANCHOR_END: fanin

end Init

section Schedules

-- ANCHOR: schedule
/-- Exponential learning-rate schedule: `η_t = η₀ · γ^t`. -/
def lrAt (η₀ γ : Rat) : Nat → Rat := fun t => η₀ * powN γ t

theorem powN_succ (b : Rat) (k : Nat) : powN b (k + 1) = b * powN b k := rfl

/-- Powers of a nonnegative base are nonnegative. -/
theorem powN_nonneg {b : Rat} (hb : 0 ≤ b) : ∀ t, 0 ≤ powN b t
  | 0 => by unfold powN; grind
  | t + 1 => by
      rw [powN_succ]
      exact Rat.mul_nonneg hb (powN_nonneg hb t)

/-- `Σ_{t<n} γ^t = (1 - γⁿ)/(1 - γ)` — the geometric sum, the exact shape
of Adam's bias correction and of every decayed budget. -/
theorem geom_sum (γ : Rat) (h1 : γ < 1) : ∀ n : Nat,
    Vec.dot (fun t : Fin n => powN γ (t : Nat)) (fun _ => (1 : Rat))
      = (1 - powN γ n) / (1 - γ) := by
  intro n
  induction n with
  | zero => unfold Vec.dot powN; grind
  | succ n ih =>
      have hden : 1 - γ ≠ 0 := by grind
      have hinv : (1 - γ) * (1 - γ)⁻¹ = 1 := Rat.mul_inv_cancel (1 - γ) hden
      have hsplit : Vec.dot (fun t : Fin (n + 1) => powN γ (t : Nat))
            (fun _ : Fin (n + 1) => (1 : Rat))
          = powN γ 0 + Vec.dot (fun t : Fin n => powN γ (t.succ : Nat))
              (fun _ : Fin n => (1 : Rat)) := by
        simp only [Vec.dot]
        grind
      have htail : (fun t : Fin n => powN γ (t.succ : Nat))
          = (fun (t : Fin n) => γ * powN γ (t : Nat)) := by
        funext t
        show powN γ (t.val + 1) = γ * powN γ (t : Nat)
        exact powN_succ γ t.val
      rw [hsplit, powN, htail, Vec.dot_smul_left, ih]
      rw [powN_succ]
      grind

/-- `vsum z = Σ zᵢ · 1`: the plain sum is the dot with ones. -/
theorem vsum_eq_dot_ones : ∀ {n : Nat} (z : Vec Rat n),
    vsum z = Vec.dot z (fun _ => (1 : Rat)) := by
  intro n
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      show z 0 + vsum (fun i => z i.succ)
        = z 0 * 1 + Vec.dot (fun i => z i.succ) (fun _ => (1 : Rat))
      rw [ih (fun i => z i.succ)]
      grind

/-- **Finite geometric budget**: for `0 < γ < 1` and `η₀ ≥ 0`, the total
displacement `Σ_{t<n} η₀ γ^t` is bounded by `η₀ / (1 - γ)` — for every `n`.
Exponential decay spends a *finite* total step budget; the `1/t` rate of
part 2 spends an unbounded one. This is the exact difference between
"decay" and "decay fast", and why long-tail schedules keep exploring late
in training. -/
theorem lr_decay_total (η₀ γ : Rat) (n : Nat) (h0 : 0 < γ) (h1 : γ < 1)
    (hη : 0 ≤ η₀) :
    vsum (fun t : Fin n => lrAt η₀ γ (t : Nat)) ≤ η₀ / (1 - γ) := by
  unfold lrAt
  have h0b : 0 ≤ γ := by grind
  have hpow : 0 ≤ powN γ n := powN_nonneg h0b n
  rw [vsum_eq_dot_ones, Vec.dot_smul_left, geom_sum γ h1 n]
  have hden : 0 < 1 - γ := by grind
  have hin : 0 ≤ (1 - γ)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hden)
  have hle : (1 : Rat) - powN γ n ≤ 1 := by grind
  have hstep : (1 - powN γ n) * (1 - γ)⁻¹ ≤ 1 * (1 - γ)⁻¹ :=
    Rat.mul_le_mul_of_nonneg_right hle hin
  have hmul := Rat.mul_le_mul_of_nonneg_left hstep hη
  grind
-- ANCHOR_END: schedule

end Schedules

end LeanDL.Ch05