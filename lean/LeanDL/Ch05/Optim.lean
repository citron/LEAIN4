import LeanDL.Ch04.Autodiff

/-!
# Chapter 5, part 2 — Optimizers

Each optimizer is a pure function from (parameters, gradient, state) to new parameters and
state. The scalar recurrences below are the ones we prove things about; the array versions are
what the demos run.
-/

namespace LeanDL.Ch05

open Lean.Grind LeanDL.Ch04

variable {α : Type}

/-- `b ^ t` by repeated multiplication. -/
def powN [Mul α] [OfNat α 1] (b : α) : Nat → α
  | 0 => 1
  | t + 1 => b * powN b t

-- ANCHOR: ema
/-- Exponential moving average of a constant gradient `g`, started at `0`:
`m₀ = 0`, `m_{t+1} = β m_t + (1 - β) g`. Momentum and both Adam moments are of this form. -/
def ema [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] (β g : α) : Nat → α
  | 0 => 0
  | t + 1 => β * ema β g t + (1 - β) * g
-- ANCHOR_END: ema

section Laws

variable [CommRing α]

-- ANCHOR: ema_laws
/-- Closed form: `m_t = (1 - βᵗ) g`. The average starts at `0`, so it is *biased* towards `0`. -/
theorem ema_const (β g : α) : ∀ t, ema β g t = (1 - powN β t) * g
  | 0 => by simp only [ema, powN]; grind
  | t + 1 => by
    have ih := ema_const β g t
    simp only [ema, powN, ih]
    grind

-- ANCHOR_END: ema_laws

-- ANCHOR: sgd_quadratic
/-- Gradient descent on `f(w) = a w² / 2` has gradient `a w`. -/
def sgdQuad (η a : α) : α → Nat → α
  | w, 0 => w
  | w, t + 1 => sgdQuad η a (w - η * (a * w)) t

/-- `w_t = (1 - η a)ᵗ w₀`: convergence iff `|1 - η a| < 1`, divergence if the step is too big. -/
theorem sgdQuad_closed (η a : α) : ∀ (t : Nat) (w : α), sgdQuad η a w t = powN (1 - η * a) t * w
  | 0, w => by simp only [sgdQuad, powN]; grind
  | t + 1, w => by
    rw [sgdQuad, sgdQuad_closed η a t]
    simp only [powN]
    grind
-- ANCHOR_END: sgd_quadratic

-- ANCHOR: sgd_spec
/-- `b² ≤ 1` when `-1 ≤ b ≤ 1`. The one algebraic fact behind every
convergence proof below: a factor in `[-1, 1]` never amplifies. -/
theorem sq_le_one (c : Rat) (lo : -1 ≤ c) (hi : c ≤ 1) : c * c ≤ 1 := by
  rcases Rat.le_total (a := 0) (b := c) with hpos | hneg
  · have h := Rat.mul_le_mul_of_nonneg_left hi hpos
    grind
  · have hneg1 : -c ≤ 1 := by
      have := Rat.neg_le_neg lo
      grind
    have h0 : 0 ≤ -c := by grind
    have h := Rat.mul_le_mul_of_nonneg_left hneg1 h0
    have : c * c = (-c) * (-c) := by grind
    grind

/-- Powers of a number in `[0, 1]` stay in `[0, 1]`. -/
theorem powN_le_one (b : Rat) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ t, powN b t ≤ 1 ∧ 0 ≤ powN b t
  | 0 => by simp only [powN]; grind
  | t + 1 => by
      obtain ⟨ih, ih0⟩ := powN_le_one b hb0 hb1 t
      have hb : powN b (t + 1) = b * powN b t := rfl
      have h1 : b * powN b t ≤ 1 * powN b t := Rat.mul_le_mul_of_nonneg_right hb1 ih0
      have h2 : 0 ≤ b * powN b t := Rat.mul_nonneg hb0 ih0
      grind

/-- `powN (b·b) t = powN b t · powN b t`. -/
theorem powN_sq (b : Rat) : ∀ t, powN (b * b) t = powN b t * powN b t
  | 0 => by simp only [powN]; grind
  | t + 1 => by
      have hb1 : powN b (t + 1) = b * powN b t := rfl
      have hbb : powN (b * b) (t + 1) = (b * b) * powN (b * b) t := rfl
      rw [hbb, hb1, powN_sq b t]
      show (b * b) * (powN b t * powN b t) = (b * powN b t) * (b * powN b t)
      rw [← Rat.mul_assoc, Rat.mul_comm b (powN b t), Rat.mul_assoc, Rat.mul_assoc]
      grind

/-- **One SGD step never increases the loss.** On `f(w) = a w²/2` the loss
is `w²` up to the constant `a/2`; whenever the step size obeys
`0 < η a < 2` — the stability condition every practitioner learns — the
squared iterate cannot grow. The proof is one factorisation:
`w' = (1 − ηa)·w` with `1 − ηa ∈ [-1, 1]`. -/
theorem sgd_step_contract (η a w : Rat) (ha : 0 < a) (hη : 0 < η) (hb : η * a < 2) :
    (w - η * (a * w)) * (w - η * (a * w)) ≤ w * w := by
  have hpos : 0 ≤ η * a := Rat.mul_nonneg (Rat.le_of_lt hη) (Rat.le_of_lt ha)
  have hc : -1 ≤ 1 - η * a := by grind
  have hc' : 1 - η * a ≤ 1 := (Rat.sub_right_le_iff_le_add (a := (1 : Rat))).mpr (by grind)
  have hstep : w - η * (a * w) = (1 - η * a) * w := by
    have hqa : η * a * w = η * (a * w) := by grind
    grind
  rw [hstep, Rat.mul_assoc]
  have hc2 := sq_le_one (1 - η * a) hc hc'
  have hw : 0 ≤ w * w := sq_nonneg w
  have h := Rat.mul_le_mul_of_nonneg_right hc2 hw
  have : 1 * (w * w) = w * w := by grind
  grind

/-- **SGD's stability specification**: under the same condition, *every*
iterate of the run has loss at most the loss at the start. Training never
diverges while the step is in the stable range. -/
theorem sgd_loss_decreases (η a w : Rat) (ha : 0 < a) (hη : 0 < η) (hb : η * a < 2) :
    ∀ t, sgdQuad η a w t * sgdQuad η a w t ≤ w * w := by
  intro t
  have hpos : 0 ≤ η * a := Rat.mul_nonneg (Rat.le_of_lt hη) (Rat.le_of_lt ha)
  have hc : -1 ≤ 1 - η * a := by grind
  have hc' : 1 - η * a ≤ 1 := (Rat.sub_right_le_iff_le_add (a := (1 : Rat))).mpr (by grind)
  have key : ∀ (t : Nat) (v : Rat), sgdQuad η a v t = powN (1 - η * a) t * v := by
    intro t
    induction t with
    | zero => intro v; simp only [sgdQuad, powN]; grind
    | succ t ih =>
      intro v
      have hstepv : v - η * (a * v) = (1 - η * a) * v := by
        have hqa : η * a * v = η * (a * v) := by grind
        grind
      rw [sgdQuad, ih (v - η * (a * v)), hstepv, powN, Rat.mul_assoc]
      grind
  rw [key t w, Rat.mul_assoc]
  have hc2 : 0 ≤ (1 - η * a) * (1 - η * a) := sq_nonneg _
  have hc2b : (1 - η * a) * (1 - η * a) ≤ 1 := sq_le_one _ hc hc'
  obtain ⟨hp, _⟩ := powN_le_one ((1 - η * a) * (1 - η * a)) hc2 hc2b t
  have hw : 0 ≤ w * w := sq_nonneg w
  have h1 : powN ((1 - η * a) * (1 - η * a)) t * (w * w) ≤ 1 * (w * w) :=
    Rat.mul_le_mul_of_nonneg_right hp hw
  rw [powN_sq (1 - η * a)] at h1
  have : 1 * (w * w) = w * w := by grind
  grind

/-- **The critical step converges in one move.** At `η = 1/a` — the step
the curvature suggests — `1 − ηa = 0` and the iterate lands on the
minimiser `w = 0` exactly, on the first step. Too big a step (`ηa > 2`)
diverges; this is the theorem that makes the demo's divergence curve a
proven fact and not a curiosity. -/
theorem sgd_critical_step (a w : Rat) (ha : a ≠ 0) :
    sgdQuad a⁻¹ a w 1 = 0 := by
  show w - a⁻¹ * (a * w) = 0
  have h : a⁻¹ * a = 1 := Rat.inv_mul_cancel a ha
  grind
-- ANCHOR_END: sgd_spec

end Laws

section Fields

variable [Field α]

-- ANCHOR: bias_correction
/-- Adam's bias correction `m̂ = m / (1 - βᵗ)` removes the bias exactly. -/
theorem bias_correction (β g : α) (t : Nat) (h : 1 - powN β t ≠ 0) :
    ema β g t / (1 - powN β t) = g := by
  rw [ema_const]
  grind
-- ANCHOR_END: bias_correction

end Fields

/-! ## Executable optimizers on arrays -/

section Exec

variable [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] [HasAct α]

-- ANCHOR: exec
def sgdStep (lr : α) (p g : Array α) : Array α :=
  (p.zip g).map fun (w, d) => w - lr * d

/-- Heavy-ball momentum: `v ← μ v + g`, `p ← p - lr v`. -/
def momentumStep (lr μ : α) (v p g : Array α) : Array α × Array α :=
  let v' := (v.zip g).map fun (u, d) => μ * u + d
  ((p.zip v').map fun (w, u) => w - lr * u, v')

structure AdamState (α : Type) where
  m : Array α
  v : Array α
  t : Nat

def AdamState.init (n : Nat) : AdamState α := ⟨Array.replicate n 0, Array.replicate n 0, 0⟩

/-- Adam (Kingma & Ba): moving averages of `g` and `g²`, bias-corrected, then a normalised step. -/
def adamStep (lr β1 β2 eps : α) (st : AdamState α) (p g : Array α) : Array α × AdamState α :=
  let t := st.t + 1
  let m := (st.m.zip g).map fun (u, d) => β1 * u + (1 - β1) * d
  let v := (st.v.zip g).map fun (u, d) => β2 * u + (1 - β2) * (d * d)
  let c1 := HasAct.inv (1 - powN β1 t)
  let c2 := HasAct.inv (1 - powN β2 t)
  let p' := ((p.zip m).zip v).map fun ((w, a), b) =>
    w - lr * (a * c1) * HasAct.inv (HasAct.sqrt (b * c2) + eps)
  (p', ⟨m, v, t⟩)
-- ANCHOR_END: exec

end Exec

end LeanDL.Ch05
