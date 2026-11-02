import LeanDL.Ch07.Gradient

/-!
# Chapter 8 — LSTM: an additive path for the gradient

The LSTM keeps a *cell state* `c` that is updated additively: `c_{t+1} = f_t · c_t + u_t`, where
the forget gate `f_t ∈ (0, 1)` and the update `u_t = i_t · g_t` are computed from the inputs.
Along this path the gradient is a product of forget gates only — no weight matrix, no
`1 - tanh²` — and the network can learn to keep it close to `1`.
-/

namespace LeanDL.Ch08

open Lean.Grind LeanDL.Ch04 LeanDL.Ch05

variable {α : Type}

-- ANCHOR: cell
/-- The cell-state recurrence `c_{t+1} = f_t · c_t + u_t`, unrolled as an `Expr` in `c₀`. -/
def cE [Add α] [Mul α] (f u : Nat → α) : Nat → Expr α 1
  | 0 => .var 0
  | t + 1 => .add (.mul (.const (f t)) (cE f u t)) (.const (u t))

/-- The product of the first `t` forget gates. -/
def prodF [Mul α] [OfNat α 1] (f : Nat → α) : Nat → α
  | 0 => 1
  | t + 1 => f t * prodF f t
-- ANCHOR_END: cell

section Exact

variable [CommRing α] [HasAct α]

-- ANCHOR: path
/-- **The gradient along the cell path is the product of the forget gates.** -/
theorem deriv_cE (f u : Nat → α) (x : Vec α 1) :
    ∀ t, ((cE f u t).deriv 0).eval x = prodF f t
  | 0 => by simp [cE, prodF, Expr.deriv, Expr.eval]
  | t + 1 => by
    have ih := deriv_cE f u x t
    simp only [cE, prodF, Expr.deriv, Expr.eval]
    rw [ih]
    grind

/-- With the forget gate fully open the gradient is exactly `1`, however long the sequence:
the "constant error carousel". -/
theorem carousel (f : Nat → α) (hf : ∀ t, f t = 1) : ∀ t, prodF f t = 1
  | 0 => rfl
  | t + 1 => by
    have ih := carousel f hf t
    simp only [prodF, hf t, ih]
    grind
-- ANCHOR_END: path

end Exact

section Bounds

open LeanDL.Ch02

theorem powN_nonneg (a : Rat) (ha : 0 ≤ a) : ∀ t, 0 ≤ powN a t
  | 0 => by simp only [powN]; grind
  | t + 1 => by
    have := powN_nonneg a ha t
    simp only [powN]
    exact Rat.mul_nonneg ha this

-- ANCHOR: bounds
/-- If every forget gate is at least `a ≥ 0`, the gradient is at least `aᵗ`: with `a = 0.99`
it takes hundreds of steps to lose half, whereas `|w| ≤ 1/2` loses half *every* step. -/
theorem prodF_ge (a : Rat) (ha : 0 ≤ a) (f : Nat → Rat) (hf : ∀ t, a ≤ f t) :
    ∀ t, powN a t ≤ prodF f t
  | 0 => by simp only [powN, prodF]; grind
  | t + 1 => by
    have ih := prodF_ge a ha f hf t
    have hP := powN_nonneg a ha t
    have hft := hf t
    have h0 : 0 ≤ f t := by grind
    have s1 : a * powN a t ≤ f t * powN a t := Rat.mul_le_mul_of_nonneg_right hft hP
    have s2 : f t * powN a t ≤ f t * prodF f t := Rat.mul_le_mul_of_nonneg_left ih h0
    simp only [powN, prodF]
    grind

/-- Gates in `[0, 1]` also keep the gradient from exploding: it never exceeds `1`. -/
theorem prodF_le_one (f : Nat → Rat) (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) :
    ∀ t, 0 ≤ prodF f t ∧ prodF f t ≤ 1
  | 0 => by simp only [prodF]; grind
  | t + 1 => by
    obtain ⟨hp0, hp1⟩ := prodF_le_one f h0 h1 t
    have a0 := h0 t
    have a1 := h1 t
    have s1 : f t * prodF f t ≤ f t * 1 := Rat.mul_le_mul_of_nonneg_left hp1 a0
    simp only [prodF]
    exact ⟨Rat.mul_nonneg a0 hp0, by grind⟩
-- ANCHOR_END: bounds

end Bounds

-- ANCHOR: gru
section Gru

variable {α : Type} [CommRing α] [HasAct α]

/-- **The GRU obeys the same recurrence as the cell state.** Its update
`h_{t+1} = z_t · h_t + (1 − z_t) · n_t` is the additive path `cE` with forget factor
`f_t = z_t` (the update gate *keeps* the old state) and update `u_t = (1 − z_t) · n_t`.
So every theorem above applies verbatim to the hidden state itself: the GRU buys the
LSTM's constant-error carousel with two gates instead of four. -/
def gruStep (z n : Nat → α) : Nat → Expr α 1 := cE z (fun t => (1 - z t) * n t)

/-- The gradient of the GRU state path is the product of update gates. -/
theorem deriv_gru (z n : Nat → α) (x : Vec α 1) :
    ∀ t, ((gruStep z n t).deriv 0).eval x = prodF z t := deriv_cE z _ x

end Gru
-- ANCHOR_END: gru

end LeanDL.Ch08
