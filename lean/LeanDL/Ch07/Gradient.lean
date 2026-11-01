import LeanDL.Ch05.Optim
import LeanDL.Ch04.Correct
import LeanDL.Ch02.Perceptron

/-!
# Chapter 7 — Recurrent networks: how gradients flow through time

A scalar recurrent network `h_{t+1} = tanh (w · h_t + c_t)`, unrolled for `T` steps as an `Expr`
in the single variable `h₀`. Its gradient `∂h_T/∂h₀` is a product of `T` factors; we prove that
product exactly, then bound it (vanishing) and compute it in the linear case (exploding).
-/

namespace LeanDL.Ch07

open Lean.Grind LeanDL.Ch04 LeanDL.Ch05

variable {α : Type}

-- ANCHOR: unroll
/-- The network unrolled for `t` steps; the only variable is the initial state `h₀`. -/
def hE [Add α] [Mul α] (w : α) (c : Nat → α) : Nat → Expr α 1
  | 0 => .var 0
  | t + 1 => .tanh (.add (.mul (.const w) (hE w c t)) (.const (c t)))

/-- The product of per-step factors `g₁ · w · g₂ · w ⋯`, for factors `gₛ` given as a function. -/
def jacRec [Mul α] [OfNat α 1] (w : α) (g : Nat → α) : Nat → α
  | 0 => 1
  | t + 1 => g (t + 1) * (w * jacRec w g t)
-- ANCHOR_END: unroll

section Exact

variable [CommRing α] [HasAct α]

-- ANCHOR: bptt
/-- **Backpropagation through time computes a product.** The formal derivative of the unrolled
network with respect to `h₀` is `∏ₛ (1 - hₛ²) · w`, where `hₛ` is the state at step `s`. -/
theorem deriv_hE (w : α) (c : Nat → α) (x : Vec α 1) :
    ∀ t, ((hE w c t).deriv 0).eval x =
      jacRec w (fun s => 1 - (hE w c s).eval x * (hE w c s).eval x) t
  | 0 => by simp [hE, jacRec, Expr.deriv, Expr.eval]
  | t + 1 => by
    have ih := deriv_hE w c x t
    simp only [hE, jacRec, Expr.deriv, Expr.eval]
    rw [ih]
    grind

/-- The gradient that `backprop` returns for the unrolled network is that product. -/
theorem bptt_gradient (w : α) (c : Nat → α) (x : Vec α 1) (t : Nat) :
    ((hE w c t).backprop x).getD 0 0 =
      jacRec w (fun s => 1 - (hE w c s).eval x * (hE w c s).eval x) t := by
  have := backprop_correct x (hE w c t) 0
  simp only [Fin.val_zero] at this
  rw [this, deriv_hE]
-- ANCHOR_END: bptt

end Exact

section Vanishing

open LeanDL.Ch02

-- ANCHOR: vanishing
/-- **Vanishing gradients.** If every factor `gₛ` lies in `[0, 1]` (as `1 - tanh²` does), then
`(∂h_T/∂h₀)² ≤ (w²)ᵀ`: with `|w| < 1` the gradient decays exponentially with the length of the
sequence. Over `Rat`, exact arithmetic. -/
theorem jacRec_sq_le (w : Rat) (g : Nat → Rat) (h0 : ∀ t, 0 ≤ g (t + 1)) (h1 : ∀ t, g (t + 1) ≤ 1) :
    ∀ t, jacRec w g t * jacRec w g t ≤ powN (w * w) t
  | 0 => by simp only [jacRec, powN]; grind
  | t + 1 => by
    have ih := jacRec_sq_le w g h0 h1 t
    have hg := h0 t
    have hg1 := h1 t
    have hww : 0 ≤ w * w := sq_nonneg w
    have hJ : 0 ≤ jacRec w g t * jacRec w g t := sq_nonneg _
    have hgg : g (t + 1) * g (t + 1) ≤ 1 := by
      have := Rat.mul_le_mul_of_nonneg_left hg1 hg
      grind
    have hB : 0 ≤ (w * w) * (jacRec w g t * jacRec w g t) := Rat.mul_nonneg hww hJ
    have s1 : (g (t + 1) * g (t + 1)) * ((w * w) * (jacRec w g t * jacRec w g t)) ≤
        1 * ((w * w) * (jacRec w g t * jacRec w g t)) :=
      Rat.mul_le_mul_of_nonneg_right hgg hB
    have s2 : (w * w) * (jacRec w g t * jacRec w g t) ≤ (w * w) * powN (w * w) t :=
      Rat.mul_le_mul_of_nonneg_left ih hww
    simp only [jacRec, powN]
    grind

/-- The tanh case: `gₛ = 1 - tanh(·)²` lies in `[0, 1]` as soon as `tanh² ≤ 1`. -/
theorem tanh_jacobian_sq_le [HasAct Rat] (hb : ∀ y : Rat, HasAct.tanh y * HasAct.tanh y ≤ 1)
    (w : Rat) (c : Nat → Rat) (x : Vec Rat 1) (t : Nat) :
    jacRec w (fun s => 1 - (hE w c s).eval x * (hE w c s).eval x) t *
      jacRec w (fun s => 1 - (hE w c s).eval x * (hE w c s).eval x) t ≤ powN (w * w) t := by
  have hs : ∀ s, (hE w c (s + 1)).eval x =
      HasAct.tanh (w * (hE w c s).eval x + c s) := fun s => rfl
  apply jacRec_sq_le
  · intro s
    rw [hs]
    have := hb (w * (hE w c s).eval x + c s)
    grind
  · intro s
    rw [hs]
    have := sq_nonneg (HasAct.tanh (w * (hE w c s).eval x + c s))
    grind
-- ANCHOR_END: vanishing

end Vanishing

section Exploding

variable [CommRing α] [HasAct α]

-- ANCHOR: exploding
/-- The same recurrence without the non-linearity. -/
def hL [Add α] [Mul α] (w : α) (c : Nat → α) : Nat → Expr α 1
  | 0 => .var 0
  | t + 1 => .add (.mul (.const w) (hL w c t)) (.const (c t))

/-- **Exploding gradients.** Without a saturating activation the gradient is exactly `wᵗ`. -/
theorem deriv_hL (w : α) (c : Nat → α) (x : Vec α 1) :
    ∀ t, ((hL w c t).deriv 0).eval x = powN w t
  | 0 => by simp [hL, powN, Expr.deriv, Expr.eval]
  | t + 1 => by
    have ih := deriv_hL w c x t
    simp only [hL, powN, Expr.deriv, Expr.eval]
    rw [ih]
    grind

/-- Numbers: a factor `2` per step is already a million after 20 steps; a factor `1/2` per step
has square `1/4`, and `4¹⁰ = 1048576`, so the squared gradient is below one millionth after 10. -/
example : powN (2 : Int) 20 = 1048576 := by decide
example : powN (4 : Int) 10 = 1048576 := by decide
-- ANCHOR_END: exploding

end Exploding
end LeanDL.Ch07
