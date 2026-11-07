import LeanDL.Core.Vec
import LeanDL.Core.Algebra

/-!
# Probability on finite sets — a Layer-1 foundation

Distributions, expectations, variance, entropy and KL divergence over
**finite** outcome sets, with exact `Rat` arithmetic. This is the shared
probability layer: Chapter 16 teaches it, Chapter 17 (InfoNCE) builds on
it, and the generalization/bias–variance theory lives here too.

Everything here is *exact*: the scalars are `Rat`. No limits, no integrals,
no `Float` rounding. Distributions are finite, on `n` points — enough for
every loss used in the course: cross-entropy, KL, VAE, RL rewards.

The logarithm is an **abstract operation with named laws** (`LawfulLog`
below), the same style as `LawfulExp` in `Core/Algebra.lean`. Every theorem
holds for *any* structure obeying those laws; the real logarithm on ℝ obeys
them (a fact of analysis, outside this course's scope), and `Float` rounds,
so it obeys them only approximately — we never prove anything about `Float`.
-/

namespace LeanDL

open Lean.Grind

-- ANCHOR: haslog
/-- An abstract logarithm on `Rat`, with the four laws this course uses:
multiplication becomes addition, inverses become negation, and the
fundamental tangent inequality `log x ≤ x - 1`. The real logarithm satisfies
all four; `Float` satisfies them only up to rounding, which is exactly why
the statements are over exact `Rat` and not over `Float`. -/
class LawfulLog where
  log : Rat → Rat
  log_mul : ∀ x y, 0 < x → 0 < y → log (x * y) = log x + log y
  log_inv : ∀ x, x ≠ 0 → log x⁻¹ = -log x
  log_le : ∀ x, 0 < x → log x ≤ x - 1

/-- `log 1 = 0`, from `log_mul`: `log 1 = log (1·1) = log 1 + log 1`. -/
theorem log_one [LawfulLog] : LawfulLog.log (1 : Rat) = 0 := by
  have := LawfulLog.log_mul (1 : Rat) 1 (by grind) (by grind)
  grind

/-- `log x - log y = log (x / y)` for positive `x, y`: bookkeeping from
`log_mul` and `log_inv` (over `Rat`, `x / y` *is* `x * y⁻¹`). -/
theorem log_div [LawfulLog] {x y : Rat} (hx : 0 < x) (hy : 0 < y) :
    LawfulLog.log x - LawfulLog.log y = LawfulLog.log (x / y) := by
  have hyi : 0 < y⁻¹ := Rat.inv_pos.mpr hy
  show LawfulLog.log x - LawfulLog.log y = LawfulLog.log (x * y⁻¹)
  rw [LawfulLog.log_mul x y⁻¹ hx hyi, LawfulLog.log_inv y (by grind)]
  grind
-- ANCHOR_END: haslog
/-- Positive rationals are closed under inversion, and `x · x⁻¹ = 1`
exactly. These two facts do the cancellations in the chapter, so we state
them once, over `Rat`, where they are true (over `Float` they are not). -/
theorem inv_pos' {x : Rat} (h : 0 < x) : 0 < x⁻¹ := Rat.inv_pos.mpr h

theorem inv_mul_cancel' {x : Rat} (h : x ≠ 0) : x⁻¹ * x = 1 := Rat.inv_mul_cancel x h

-- ANCHOR: dist
/-- A probability distribution on `n` points: weights that are all strictly
positive and sum to `1`. Strict positivity keeps `log` of every weight
defined; the cases with zero weights are measure-theoretic bookkeeping, not
ideas, and we say so rather than hand-wave them. -/
structure Dist (n : Nat) where
  w : Vec Rat n
  pos : ∀ i, 0 < w i
  sum1 : Vec.dot w (fun _ => 1) = 1
-- ANCHOR_END: dist

section DotOrder

/-- **Monotonicity of the dot product**: nonnegative weights preserve order.
Every bound on the integrand becomes a bound on the expectation — the
workhorse of the whole chapter. -/
theorem dot_mono : ∀ {n : Nat} (w f g : Vec Rat n), (∀ i, 0 ≤ w i) →
    (∀ i, f i ≤ g i) → Vec.dot w f ≤ Vec.dot w g := by
  intro n
  induction n with
  | zero =>
      intro w f g hw h
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w f g hw h
      have h0 := Rat.mul_le_mul_of_nonneg_left (h 0) (hw 0)
      have ht := ih (fun i => w i.succ) (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hw i.succ) (fun i => h i.succ)
      simp only [Vec.dot]
      grind

/-- The dot product distributes over subtraction (as over addition). -/
theorem dot_sub : ∀ {n : Nat} (w f g : Vec Rat n),
    Vec.dot w (fun i => f i - g i) = Vec.dot w f - Vec.dot w g := by
  intro n
  induction n with
  | zero =>
      intro w f g
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w f g
      have h := ih (fun i => w i.succ) (fun i => f i.succ) (fun i => g i.succ)
      simp only [Vec.dot]
      grind

/-- The dot product commutes with negation: `Σ (-fᵢ) = -Σ fᵢ`. -/
theorem dot_neg : ∀ {n : Nat} (w f : Vec Rat n),
    Vec.dot w (fun i => -f i) = -Vec.dot w f := by
  intro n
  induction n with
  | zero =>
      intro w f
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w f
      have h := ih (fun i => w i.succ) (fun i => f i.succ)
      simp only [Vec.dot]
      grind

/-- A positive-weighted sum of squares is nonnegative. -/
theorem weighted_sq_nonneg : ∀ {n : Nat} (w f : Vec Rat n), (∀ i, 0 < w i) →
    0 ≤ Vec.dot w (fun i => f i * f i) := by
  intro n
  induction n with
  | zero =>
      intro w f hw
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w f hw
      have ih' := ih (fun i => w i.succ) (fun i => f i.succ) (fun i => hw i.succ)
      have h0 : 0 ≤ w 0 * (f 0 * f 0) :=
        Rat.mul_nonneg (Rat.le_of_lt (hw 0)) (LeanDL.sq_nonneg (f 0))
      simp only [Vec.dot]
      grind

/-- The dot product against the constant zero is zero. -/
theorem dot_zero_right : ∀ {n : Nat} (w : Vec Rat n),
    Vec.dot w (fun _ => (0 : Rat)) = 0 := by
  intro n
  induction n with
  | zero =>
      intro w
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w
      have := ih (fun i => w i.succ)
      simp only [Vec.dot]
      grind

/-- Summing a constant is the constant times the total weight. -/
theorem dot_smul_const : ∀ {n : Nat} (w : Vec Rat n) (c : Rat),
    Vec.dot w (fun _ => c) = c * Vec.dot w (fun _ => (1 : Rat)) := by
  intro n
  induction n with
  | zero =>
      intro w c
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro w c
      have := ih (fun i => w i.succ) c
      simp only [Vec.dot]
      grind

/-- **Telescoping**: weighting `(qᵢ − pᵢ) · pᵢ⁻¹` by `pᵢ` cancels the
inverse inside the dot, so the sum is `Σqᵢ − Σpᵢ`. This is where "the
partition functions cancel" becomes a calculation. -/
theorem dot_inv_telescope : ∀ {n : Nat} (pw qw : Vec Rat n),
    (∀ i, pw i * (pw i)⁻¹ = 1) →
    Vec.dot pw (fun i => (qw i - pw i) * (pw i)⁻¹)
      = Vec.dot qw (fun _ => (1 : Rat)) - Vec.dot pw (fun _ => (1 : Rat)) := by
  intro n
  induction n with
  | zero =>
      intro pw qw h
      simp only [Vec.dot]
      try grind
  | succ n ih =>
      intro pw qw h
      have h0 : pw 0 * ((qw 0 - pw 0) * (pw 0)⁻¹) = qw 0 - pw 0 := by
        have hc := h 0
        grind
      have := ih (fun i => pw i.succ) (fun i => qw i.succ) (fun i => h i.succ)
      simp only [Vec.dot]
      grind

end DotOrder

namespace Dist

variable {n : Nat}

-- ANCHOR: expect
/-- The **expectation** of `f` under `p`: the weighted average `Σᵢ pᵢ fᵢ`. -/
def expect (p : Dist n) (f : Vec Rat n) : Rat :=
  Vec.dot p.w f

/-- The **variance** of `f`: the expectation of the squared deviation from
the mean. It measures the spread of `f` under `p`. -/
def variance (p : Dist n) (f : Vec Rat n) : Rat :=
  p.expect (fun i => f i * f i) - p.expect f * p.expect f
-- ANCHOR_END: expect

section ExpectLaws

-- ANCHOR: expect_laws
/-- The mean of the constant `1` is `1`: total probability is conserved. -/
theorem expect_one (p : Dist n) : p.expect (fun _ => 1) = 1 := p.sum1

/-- Expectation is **additive**: `E[f + g] = E[f] + E[g]`. -/
theorem expect_add (p : Dist n) (f g : Vec Rat n) :
    p.expect (fun i => f i + g i) = p.expect f + p.expect g := by
  simp only [expect]
  exact Vec.dot_add_right _ _ _

/-- Expectation is **monotone**: `f ≤ g` pointwise implies `E[f] ≤ E[g]`. -/
theorem expect_le (p : Dist n) {f g : Vec Rat n} (h : ∀ i, f i ≤ g i) :
    p.expect f ≤ p.expect g := by
  simp only [expect]
  exact dot_mono p.w f g (fun i => Rat.le_of_lt (p.pos i)) h

/-- The mean of a constant is that constant. -/
theorem expect_const (p : Dist n) (c : Rat) : p.expect (fun _ => c) = c := by
  show Vec.dot p.w (fun _ => c) = c
  rw [dot_smul_const, p.sum1]
  grind
-- ANCHOR_END: expect_laws

-- ANCHOR: convex_bound
/-- **Convex combination of bounded values stays bounded.** If the
weights are nonnegative and sum to 1 — a gate, a softmax, an ensemble
vote — and every value satisfies `|f i| ≤ M`, then the blend satisfies
`|Σ wᵢ fᵢ| ≤ M`. This is the kernel of every bridge between exact
theorems and the recurrent/attention layers: `tanh` outputs (bounded by
1), GRU gated updates (convex combinations of bounded states), attention
blends (softmax-weighted averages of bounded value vectors). -/
theorem convex_bound {n : Nat} (w f : Vec Rat n) (M : Rat)
    (hw : ∀ i, 0 ≤ w i) (hsum : Vec.dot w (fun _ => (1 : Rat)) = 1)
    (hb : ∀ i, Rat.abs (f i) ≤ M) :
    Rat.abs (Vec.dot w f) ≤ M := by
  have hup : Vec.dot w f ≤ Vec.dot w (fun _ => M) := dot_mono w f (fun _ => M) hw (fun i => by
    have := hb i
    grind [Rat.abs.eq_1])
  have hneg : Vec.dot w (fun _ => -M) ≤ Vec.dot w f := dot_mono w (fun _ => -M) f hw (fun i => by
    have := hb i
    grind [Rat.abs.eq_1])
  have hsm : Vec.dot w (fun _ => M) = M * Vec.dot w (fun _ => (1 : Rat)) :=
    dot_smul_const w M
  have hsm2 : Vec.dot w (fun _ => -M) = -M * Vec.dot w (fun _ => (1 : Rat)) :=
    dot_smul_const w (-M)
  rw [hsm, hsum] at hup
  rw [hsm2, hsum] at hneg
  have h2 : -M * 1 = -M := by grind
  rw [h2] at hneg
  grind [Rat.abs.eq_1]

/-- The expectation version: under a distribution, a bounded random
variable has bounded mean. Softmax attention over values in `[-M, M]`
blends to a vector of mean-coordinate in `[-M, M]`; an ensemble of
models each within `M` of the target is itself within `M`. -/
theorem expect_abs_bound (p : Dist n) (f : Vec Rat n) (M : Rat)
    (hb : ∀ i, Rat.abs (f i) ≤ M) : Rat.abs (p.expect f) ≤ M :=
  convex_bound p.w f M (fun i => Rat.le_of_lt (p.pos i)) p.sum1 hb
-- ANCHOR_END: convex_bound

end ExpectLaws

-- ANCHOR: variance
/-- The **centered** form of the variance: `E[(f - Ef)²] = E[f²] - (Ef)²`.
The two definitions agree; the left side explains the name, the right side
is what the computer computes. -/
theorem variance_eq_centered (p : Dist n) (f : Vec Rat n) :
    p.variance f =
      p.expect (fun i => (f i - p.expect f) * (f i - p.expect f)) := by
  have hrew : Vec.dot p.w
        (fun i => (f i - Vec.dot p.w f) * (f i - Vec.dot p.w f))
      = Vec.dot p.w (fun i => f i * f i) - Vec.dot p.w f * Vec.dot p.w f := by
    rw [show (fun i => (f i - Vec.dot p.w f) * (f i - Vec.dot p.w f))
          = (fun i => f i * f i + (-(2 : Rat) * (Vec.dot p.w f * f i))
              + (Vec.dot p.w f * Vec.dot p.w f)) from by
          funext i; grind,
        Vec.dot_add_right, Vec.dot_add_right,
        Vec.dot_smul_right (-(2 : Rat)), Vec.dot_smul_right (Vec.dot p.w f),
        dot_smul_const p.w (Vec.dot p.w f * Vec.dot p.w f), p.sum1]
    generalize Vec.dot p.w (fun i => f i * f i) = Q, Vec.dot p.w f * Vec.dot p.w f = S
    grind
  simp only [variance, expect]
  exact hrew.symm
-- ANCHOR_END: variance

-- ANCHOR: generalization
/-- The **ensemble average** of a family of models `f : Fin m → Vec Rat n` (one
prediction per input) under the ensemble distribution `p` over hypotheses:
`f̄ i = Σₖ pₖ · fₖ i`. -/
def wavg {m n : Nat} (p : Dist m) (f : Fin m → Vec Rat n) : Vec Rat n :=
  fun i => Vec.dot p.w (fun k => f k i)

/-- **The average of the family is the ensemble mean**: `Σₖ pₖ fₖ i = f̄ i`. -/
theorem expect_f_eq_wavg {m n : Nat} (p : Dist m) (f : Fin m → Vec Rat n) (i : Fin n) :
    p.expect (fun k => f k i) = wavg p f i := by
  simp only [wavg, expect]

/-- A weighted sum of zeros is zero. -/
theorem dot_zero_fun {m : Nat} (w : Vec Rat m) :
    Vec.dot w (fun _ => (0 : Rat)) = 0 := by
  induction m with
  | zero => simp only [Vec.dot]; try grind
  | succ m ih =>
      have h := ih (fun i => w i.succ)
      simp only [Vec.dot]
      grind

/-- **The cross term vanishes**: the average deviation of the family from its own
mean is zero. -/
theorem wavg_dev_zero {m n : Nat} (p : Dist m) (f : Fin m → Vec Rat n) (i : Fin n) :
    p.expect (fun k => f k i - wavg p f i) = 0 := by
  simp only [expect]
  rw [dot_sub]
  have h1 : Vec.dot p.w (fun k => f k i) = wavg p f i := by
    have t := expect_f_eq_wavg p f i
    simp only [expect] at t
    exact t
  have h2 : Vec.dot p.w (fun _ => wavg p f i) = wavg p f i := by
    rw [dot_smul_const, p.sum1]
    grind
  rw [h1, h2]
  grind

/-- **Pointwise decomposition of the ensemble risk** at one input `x = i`, with
target `t i`: the mean squared error of the individual models equals the squared
bias of the average plus the (ensemble) variance:
`Σₖ pₖ (fₖ i − t i)² = (f̄ i − t i)² + Σₖ pₖ (fₖ i − f̄ i)²`. -/
theorem wavg_pointwise {m n : Nat} (p : Dist m) (f : Fin m → Vec Rat n) (t : Vec Rat n)
    (i : Fin n) :
    Vec.dot p.w (fun k => (f k i - t i) * (f k i - t i))
      = (wavg p f i - t i) * (wavg p f i - t i)
        + Vec.dot p.w (fun k => (f k i - wavg p f i) * (f k i - wavg p f i)) := by
  have hsq : (fun k => (f k i - t i) * (f k i - t i))
      = (fun k => (wavg p f i - t i) * (wavg p f i - t i)
          + (f k i - wavg p f i) * (f k i - wavg p f i)
          + (2 : Rat) * ((wavg p f i - t i) * (f k i - wavg p f i))) := by
    funext k
    grind
  have hcross : Vec.dot p.w (fun k => (wavg p f i - t i) * (f k i - wavg p f i)) = 0 := by
    rw [Vec.dot_smul_right (wavg p f i - t i)]
    have h : Vec.dot p.w (fun k => f k i - wavg p f i) = 0 := by
      have t := wavg_dev_zero p f i
      simp only [expect] at t
      exact t
    rw [h]
    grind
  have hconst : Vec.dot p.w (fun k => (wavg p f i - t i) * (wavg p f i - t i))
      = (wavg p f i - t i) * (wavg p f i - t i) := by
    rw [dot_smul_const, p.sum1]
    grind
  rw [hsq, Vec.dot_add_right, Vec.dot_add_right, Vec.dot_smul_right (2 : Rat), hcross, hconst]
  generalize (wavg p f i - t i) * (wavg p f i - t i) = X,
    Vec.dot p.w (fun k => (f k i - wavg p f i) * (f k i - wavg p f i)) = V
  rw [Rat.mul_zero, Rat.add_zero]

/-- Two functions that agree at every point have equal weighted sums. -/
theorem dot_congruent {n : Nat} (w : Vec Rat n) {f g : Vec Rat n} (h : ∀ i, f i = g i) :
    Vec.dot w f = Vec.dot w g := by
  congr 1
  funext i
  exact h i

/-- **The bias–variance decomposition of the ensemble risk.** Averaging the
pointwise identity over the input distribution `q` (inputs `i`, target `t i`,
hypotheses drawn from `p`):

`risk = (bias)² + variance`, where
`risk = Σᵢ qᵢ Σₖ pₖ (fₖ i − t i)²`, `(bias)² = Σᵢ qᵢ (f̄ i − t i)²`,
`variance = Σᵢ qᵢ Σₖ pₖ (fₖ i − f̄ i)²`.

This is exact algebra on `Rat`: no probability theory beyond the two weighted
sums, no analysis, no limits. What it buys: **the risk of a single draw is the
risk of the average plus the variance of the family** — averaging hypotheses
fights variance, and only the average can fight bias. -/
theorem ensemble_risk_decomp {m n : Nat} (p : Dist m) (q : Dist n)
    (f : Fin m → Vec Rat n) (t : Vec Rat n) :
    Vec.dot q.w (fun i => Vec.dot p.w (fun k => (f k i - t i) * (f k i - t i)))
      = Vec.dot q.w (fun i => (wavg p f i - t i) * (wavg p f i - t i))
        + Vec.dot q.w (fun i =>
            Vec.dot p.w (fun k => (f k i - wavg p f i) * (f k i - wavg p f i))) := by
  have hpoint : (fun i => Vec.dot p.w (fun k => (f k i - t i) * (f k i - t i)))
      = (fun i => (wavg p f i - t i) * (wavg p f i - t i)
          + Vec.dot p.w (fun k => (f k i - wavg p f i) * (f k i - wavg p f i))) := by
    funext i
    exact wavg_pointwise p f t i
  rw [hpoint, Vec.dot_add_right]
-- ANCHOR_END: generalization

section Entropy
variable [LawfulLog]

/-- The **entropy** `H(p) = Σᵢ -pᵢ log pᵢ`: the average surprise of a draw
from `p`. It is `0` when `p` is certain (one point has weight `1`) and grows
as the mass spreads out. -/
def entropy (p : Dist n) : Rat :=
  Vec.dot p.w (fun i => -LawfulLog.log (p.w i))

/-- The **KL divergence** `KL(p ∥ q) = Σᵢ pᵢ log (pᵢ / qᵢ)` (the division is
rewritten as a difference of logs by `log_div`): the extra surprise of
coding a draw from `p` with the code designed for `q`. -/
def kl (p q : Dist n) : Rat :=
  Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i))

/-- The **cross-entropy** `CE(p, q) = Σᵢ -pᵢ log qᵢ`: what training actually
minimises — the average surprise of the true distribution `p` under the
model `q`. -/
def crossEntropy (p q : Dist n) : Rat :=
  Vec.dot p.w (fun i => -LawfulLog.log (q.w i))

/-- `KL(p ∥ p) = 0`: a distribution is perfectly predictable to itself. -/
theorem kl_self (p : Dist n) : p.kl p = 0 := by
  show Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (p.w i)) = 0
  rw [show (fun i => LawfulLog.log (p.w i) - LawfulLog.log (p.w i))
        = (fun _ => (0 : Rat)) from by
        funext i
        grind]
  exact dot_zero_right _

-- ANCHOR: gibbs
/-- **Gibbs' inequality: `0 ≤ KL(p ∥ q)`.** Two distributions can never have
negative divergence; coding with the wrong code always costs extra surprise.
This single fact is why minimising cross-entropy pushes a model toward the
data distribution, and why the loss has a floor.

*Proof, in words.* With the tangent inequality at `qᵢ · pᵢ⁻¹`:
`log qᵢ − log pᵢ = log(qᵢ · pᵢ⁻¹) ≤ qᵢ · pᵢ⁻¹ − 1 = (qᵢ − pᵢ) · pᵢ⁻¹`.
Weighting by `pᵢ` cancels the inverse (`pᵢ · pᵢ⁻¹ = 1`, exactly, over
`Rat`) and the sum telescopes: `Σ(qᵢ − pᵢ) = Σqᵢ − Σpᵢ = 1 − 1 = 0`.
`KL` is the negation of the weighted sum of the left-hand sides, so
`KL ≥ 0`. The tangent inequality is the whole content of the theorem;
everything else is finite bookkeeping.
-/
theorem kl_nonneg (p q : Dist n) : 0 ≤ p.kl q := by
  -- Exact cancellation pᵢ·pᵢ⁻¹ = 1 over Rat.
  have hc : ∀ i, p.w i * (p.w i)⁻¹ = 1 := fun i =>
    Rat.mul_inv_cancel _ (Rat.ne_of_gt (p.pos i))
  -- Step 1: pointwise bound  log qᵢ − log pᵢ ≤ (qᵢ − pᵢ) · pᵢ⁻¹.
  have hpoint : ∀ i, LawfulLog.log (q.w i) - LawfulLog.log (p.w i)
      ≤ (q.w i - p.w i) * (p.w i)⁻¹ := by
    intro i
    have hp : 0 < p.w i := p.pos i
    have hq : 0 < q.w i := q.pos i
    have hlog : LawfulLog.log (q.w i) - LawfulLog.log (p.w i)
        = LawfulLog.log (q.w i * (p.w i)⁻¹) := log_div hq hp
    have hpos : 0 < q.w i * (p.w i)⁻¹ := Rat.mul_pos hq (inv_pos' hp)
    have ht := LawfulLog.log_le (q.w i * (p.w i)⁻¹) hpos
    rw [hlog]
    refine Rat.le_trans ht ?_
    have hc0 := hc i
    grind
  -- Step 2: sum the bounds with weights pᵢ ≥ 0.
  have hS : Vec.dot p.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (p.w i))
      ≤ Vec.dot p.w (fun i => (q.w i - p.w i) * (p.w i)⁻¹) :=
    dot_mono p.w _ _ (fun i => Rat.le_of_lt (p.pos i)) hpoint
  -- Step 3: the right side telescopes to Σqᵢ − Σpᵢ = 1 − 1 = 0.
  have hzero : Vec.dot p.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (p.w i))
      ≤ 0 := by
    rw [dot_inv_telescope p.w q.w hc, q.sum1, p.sum1] at hS
    grind
  -- Step 4: KL is the negation of that sum; flip the bound.
  show 0 ≤ Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i))
  have hflip : Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i))
      = -(Vec.dot p.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (p.w i))) := by
    rw [show (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i))
          = (fun i => -(LawfulLog.log (q.w i) - LawfulLog.log (p.w i)))
            from by funext i; grind]
    exact dot_neg _ _
  rw [hflip]
  exact Rat.neg_le_neg hzero

-- ANCHOR_END: gibbs

-- ANCHOR: ce_decomp
/-- **Cross-entropy = entropy + KL.** Minimising `CE(p, q)` over `q` is
minimising `KL(p ∥ q)` — the entropy of the data is a constant the model
cannot change — and the gap can never go below zero. This is the theorem
behind every classifier in the course. -/
theorem crossEntropy_eq_entropy_add_kl (p q : Dist n) :
    p.crossEntropy q = p.entropy + p.kl q := by
  show Vec.dot p.w (fun i => -LawfulLog.log (q.w i))
      = Vec.dot p.w (fun i => -LawfulLog.log (p.w i))
        + Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i))
  rw [← Vec.dot_add_right]
  congr 1; funext i; grind
-- ANCHOR_END: ce_decomp

/-- **The mean-square dominates the squared mean** (finite Jensen):
`(Ef)² ≤ E[f²]`, so the variance is nonnegative, and the mean-square error
of any predictor is at least its squared bias. -/
theorem expect_sq_le_expect_sq (p : Dist n) (f : Vec Rat n) :
    p.expect f * p.expect f ≤ p.expect (fun i => f i * f i) := by
  have hsq := weighted_sq_nonneg p.w (fun i => f i - Vec.dot p.w f) p.pos
  show Vec.dot p.w f * Vec.dot p.w f ≤ Vec.dot p.w (fun i => f i * f i)
  have hrew : Vec.dot p.w
        (fun i => (f i - Vec.dot p.w f) * (f i - Vec.dot p.w f))
      = Vec.dot p.w (fun i => f i * f i) - Vec.dot p.w f * Vec.dot p.w f := by
    rw [show (fun i => (f i - Vec.dot p.w f) * (f i - Vec.dot p.w f))
          = (fun i => f i * f i + (-(2 : Rat) * (Vec.dot p.w f * f i))
              + (Vec.dot p.w f * Vec.dot p.w f)) from by
          funext i; grind,
        Vec.dot_add_right, Vec.dot_add_right,
        Vec.dot_smul_right (-(2 : Rat)), Vec.dot_smul_right (Vec.dot p.w f),
        dot_smul_const p.w (Vec.dot p.w f * Vec.dot p.w f), p.sum1]
    generalize Vec.dot p.w (fun i => f i * f i) = Q, Vec.dot p.w f * Vec.dot p.w f = S
    grind
  rw [hrew] at hsq
  exact (Rat.le_iff_sub_nonneg _ _).mpr hsq

/-- The **variance is nonnegative**. -/
theorem variance_nonneg (p : Dist n) (f : Vec Rat n) : 0 ≤ p.variance f := by
  have := expect_sq_le_expect_sq p f
  simp only [variance, expect] at this ⊢
  grind

end Entropy

end Dist




end LeanDL
