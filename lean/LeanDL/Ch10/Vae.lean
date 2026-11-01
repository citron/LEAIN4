import LeanDL.Ch05.Optim
import LeanDL.Ch04.Correct
import LeanDL.Ch02.Perceptron

/-!
# Chapter 10 — Autoencoders and the VAE: what can be proved

A variational autoencoder samples `z = μ + σ · ε` and pays a KL penalty
`½ (μ² + e^ℓ - 1 - ℓ)` with `ℓ = log σ²`. Here we prove the facts that make it trainable and
meaningful, using the verified autodiff of Chapter 4.
-/

namespace LeanDL.Ch10

open Lean.Grind LeanDL.Ch04

variable {α : Type}

-- ANCHOR: reparam
/-- The reparameterised sample `z = μ + σ ε` as an expression in `(μ, σ)`; the noise `ε` is
a constant that was drawn independently of the parameters. -/
def reparamE [Add α] [Mul α] (eps : α) : Expr α 2 :=
  .add (.var 0) (.mul (.var 1) (.const eps))

section Reparam

variable [CommRing α] [HasAct α]

/-- **The reparameterisation trick.** Because the randomness was moved into `ε`, the sample is a
differentiable function of the parameters: `∂z/∂μ = 1` and `∂z/∂σ = ε`. Backpropagation can
therefore flow through the sampling step. -/
theorem reparam_grad (eps : α) (x : Vec α 2) :
    ((reparamE eps).backprop x).getD 0 0 = 1 ∧ ((reparamE eps).backprop x).getD 1 0 = eps := by
  constructor
  · have := backprop_correct x (reparamE eps) 0
    simp only [Fin.val_zero] at this
    rw [this]; simp [reparamE, Expr.deriv, Expr.eval]; grind
  · have := backprop_correct x (reparamE eps) 1
    simp only [Fin.val_one] at this
    rw [this]; simp [reparamE, Expr.deriv, Expr.eval]; grind
-- ANCHOR_END: reparam

-- ANCHOR: kl
/-- `KL( N(μ, e^ℓ) ‖ N(0, 1) ) = ½ (μ² + e^ℓ - 1 - ℓ)`, as an expression in `(μ, ℓ)`.
`half` stands for the constant `1/2`. -/
def klE (half : α) : Expr α 2 :=
  .mul (.const half)
    (.sub (.add (.mul (.var 0) (.var 0)) (.exp (.var 1))) (.add (.const 1) (.var 1)))

/-- The gradient of the KL penalty: `∂/∂μ = ½ (μ + μ)` and `∂/∂ℓ = ½ (e^ℓ - 1)`. -/
theorem kl_grad (half : α) (x : Vec α 2) :
    ((klE half).backprop x).getD 0 0 = half * (x 0 + x 0) ∧
      ((klE half).backprop x).getD 1 0 = half * (HasExp.exp (x 1) - 1) := by
  constructor
  · have := backprop_correct x (klE half) 0
    simp only [Fin.val_zero] at this
    rw [this]; simp [klE, Expr.deriv, Expr.eval]; grind
  · have := backprop_correct x (klE half) 1
    simp only [Fin.val_one] at this
    rw [this]; simp [klE, Expr.deriv, Expr.eval]; grind

/-- **The prior is the unique stationary point.** At `μ = 0`, `ℓ = 0` (the standard normal) the
penalty vanishes and so does its gradient: the KL term pulls every posterior towards `N(0, 1)`. -/
theorem kl_at_prior [LawfulExp α] (half : α) (_h2 : half * 2 = 1) (x : Vec α 2)
    (hμ : x 0 = 0) (hℓ : x 1 = 0) :
    (klE half).eval x = 0 ∧ ((klE half).backprop x).getD 0 0 = 0 ∧
      ((klE half).backprop x).getD 1 0 = 0 := by
  have h0 : HasExp.exp (x 1) = 1 := by rw [hℓ]; exact LawfulExp.exp_zero
  refine ⟨?_, ?_, ?_⟩
  · simp only [klE, Expr.eval, hμ]; rw [h0]; grind
  · rw [(kl_grad half x).1, hμ]; grind
  · rw [(kl_grad half x).2, h0]; grind
end Reparam
-- ANCHOR_END: kl

section Nonneg

open LeanDL.Ch02

-- ANCHOR: kl_nonneg
/-- **The KL penalty is non-negative.** It uses one fact about the exponential, the tangent-line
bound `1 + ℓ ≤ e^ℓ` (a hypothesis here, true for the real exponential): then
`½ (μ² + e^ℓ - 1 - ℓ) ≥ ½ μ² ≥ 0`. -/
theorem kl_nonneg [HasAct Rat] (hexp : ∀ l : Rat, 1 + l ≤ HasExp.exp l) (half : Rat)
    (hh : 0 ≤ half) (x : Vec Rat 2) : 0 ≤ (klE half).eval x := by
  have h1 := hexp (x 1)
  have h2 := sq_nonneg (x 0)
  have h3 : 0 ≤ (x 0 * x 0 + HasExp.exp (x 1)) - (1 + x 1) := by grind
  simp only [klE, Expr.eval]
  exact Rat.mul_nonneg hh h3
-- ANCHOR_END: kl_nonneg

end Nonneg

end LeanDL.Ch10
