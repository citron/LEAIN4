import LeanDL.Ch04.Correct

/-!
# Chapter 13 — Reinforcement learning: three exact facts

* Value iteration converges geometrically (checked on the one-state case, exactly).
* A TD / Q-learning update shrinks the error by the factor `1 - α`.
* The policy gradient of a two-armed softmax bandit equals the REINFORCE estimator, and a
  baseline does not change it.
-/

namespace LeanDL.Ch13

open Lean.Grind LeanDL.Ch04

variable {α : Type}

section Value

variable [CommRing α]

-- ANCHOR: value
/-- A power function, so we stay inside the abstract ring. -/
def pw (g : α) : Nat → α
  | 0 => 1
  | k + 1 => g * pw g k

/-- Value iteration for a state with reward `r` that returns to itself: `v ← r + γ v`. -/
def valueIter (r g v0 : α) : Nat → α
  | 0 => v0
  | k + 1 => r + g * valueIter r g v0 k

/-- **Geometric convergence.** If `v*` satisfies the Bellman equation `v* = r + γ v*`, then after `k`
sweeps the error is exactly `γᵏ` times the initial error. With `0 ≤ γ < 1` this tends to `0`. -/
theorem valueIter_error (r g v0 vs : α) (hfix : vs = r + g * vs) (k : Nat) :
    valueIter r g v0 k - vs = pw g k * (v0 - vs) := by
  induction k with
  | zero => simp only [valueIter, pw]; grind
  | succ k ih => simp only [valueIter, pw]; grind

/-- The temporal-difference update `Q ← Q + η (target - Q)`. -/
def tdUpdate (q target eta : α) : α := q + eta * (target - q)

/-- **A TD update multiplies the error by `1 - η`.** With a learning rate in `(0, 1]` the estimate
moves towards the target and never overshoots it. -/
theorem tdUpdate_error (q target eta : α) :
    tdUpdate q target eta - target = (1 - eta) * (q - target) := by
  simp only [tdUpdate]
  grind
end Value

section Fixed

variable [Field α]

/-- The Bellman fixed point of a self-loop is `r / (1 - γ)`. -/
theorem bellman_fixed (r g : α) (h : 1 - g ≠ 0) : r / (1 - g) = r + g * (r / (1 - g)) := by
  grind
-- ANCHOR_END: value

end Fixed

section Bandit

variable [CommRing α] [HasAct α]

-- ANCHOR: bandit
/-- Expected reward of a two-armed bandit whose policy plays arm 0 with probability `π = σ(θ)`:
`J(θ) = π r₀ + (1 - π) r₁`. -/
def banditJ (r0 r1 : α) : Expr α 1 :=
  .add (.const r1) (.mul (.const (r0 - r1)) (.sigmoid (.var 0)))

/-- **The policy-gradient theorem for the bandit.** The gradient of `J`, computed by verified
backpropagation, equals the REINFORCE form `E[R · ∇θ log π(a)]`:
`π · r₀ · (1 - π) + (1 - π) · r₁ · (-π)`, since `∂ log π(0)/∂θ = 1 - π` and
`∂ log π(1)/∂θ = -π`. -/
theorem reinforce_bandit (r0 r1 : α) (x : Vec α 1) :
    let p := HasAct.sigmoid (x 0)
    ((banditJ r0 r1).backprop x).getD 0 0 = p * (r0 * (1 - p)) + (1 - p) * (r1 * (0 - p)) := by
  intro p
  have := backprop_correct x (banditJ r0 r1) 0
  simp only [Fin.val_zero] at this
  rw [this]
  simp [banditJ, Expr.deriv, Expr.eval, p]
  grind

/-- **Baselines do not bias the policy gradient.** Subtracting any constant `b` from both rewards
leaves the expected gradient unchanged. -/
theorem baseline_invariant (r0 r1 b p : α) :
    p * ((r0 - b) * (1 - p)) + (1 - p) * ((r1 - b) * (0 - p)) =
      p * (r0 * (1 - p)) + (1 - p) * (r1 * (0 - p)) := by
  grind
-- ANCHOR_END: bandit

end Bandit

end LeanDL.Ch13
