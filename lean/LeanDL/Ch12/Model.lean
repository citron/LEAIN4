import LeanDL.Ch12.Diffusion
import LeanDL.Ch04.Network
import LeanDL.Core.Rng

/-!
# Chapter 12, part 2 — A diffusion model on a one-dimensional mixture

The network `ε_θ(x_t, t)` predicts the noise that was added to `x_t`. Its loss is an `Expr`, so
its gradient comes from the verified `backprop`.
-/

namespace LeanDL.Ch12

open LeanDL.Ch04

abbrev HD : Nat := 16
abbrev PD : Nat := mlpParams [2, HD, 1]

-- ANCHOR: diff_model
/-- `ε_θ(x, t)`: a `2 → 16 → 1` tanh network; `t` is passed as `step / T`. -/
def epsNet (x t : Float) : Expr Float PD :=
  (mlpE .tanh (fun e => e) [2, HD, 1] 0 [.const x, .const t]).headD (.const 0)

/-- The training loss: mean squared error between the predicted and the true noise, for a batch of
`(x_t, t, ε)`. -/
def denoiseLoss (batch : List (Float × Float × Float)) : Expr Float PD :=
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun (xt, t, e) => sqErr (epsNet xt t) (.const e)))
-- ANCHOR_END: diff_model

def vecOf (p : Array Float) : Vec Float PD := fun i => p[i.val]!

/-- Number of noising steps. -/
def T : Nat := 20

/-- Linear `β` schedule from `0.02` to `0.35`; entry `t - 1` is `β_t`. -/
def betas : Array Float := (Array.range T).map fun i => 0.02 + (0.35 - 0.02) * i.toFloat / (T - 1).toFloat

/-- `ā_t = ∏_{k ≤ t} (1 - β_k)`, with `ā_0 = 1`; the array has `T + 1` entries. -/
def abars : Array Float :=
  betas.foldl (fun acc b => acc.push (acc.back! * (1.0 - b))) #[1.0]

end LeanDL.Ch12
