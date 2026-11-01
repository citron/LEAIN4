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
