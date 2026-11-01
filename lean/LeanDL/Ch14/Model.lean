import LeanDL.Ch14.WorldModel
import LeanDL.Ch04.Network
import LeanDL.Core.Rng

/-!
# Chapter 14, part 2 — A learned world model, and a controller trained inside it

The environment is a point on a slope: position `x`, velocity `v`, action `u ∈ [-1, 1]`. Gravity
pushes the point *away* from `x = 0`, so doing nothing fails and a controller is needed.
-/

namespace LeanDL.Ch14

open LeanDL.Ch04

abbrev HW : Nat := 16
abbrev PW : Nat := mlpParams [3, HW, 2]

-- ANCHOR: env
/-- The real environment (the world model never sees this formula, only samples from it). -/
def envStep (x v u : Float) : Float × Float :=
  let u := max (-1.0) (min 1.0 u)
  (x + 0.1 * v, 0.97 * v + 0.15 * u + 0.1 * Float.sin x)

/-- Cost of being at `(x, v)` having applied `u`. -/
def stepCost (x v u : Float) : Float := x * x + 0.1 * v * v + 0.01 * u * u
-- ANCHOR_END: env

-- ANCHOR: world_model
/-- The world model: `(x, v, u) ↦ 10·(Δx, Δv)`, a `3 → 16 → 2` tanh network. The factor 10 only
rescales the small per-step changes to a convenient size. -/
def dynNet (x v u : Float) : List (Expr Float PW) :=
  mlpE .tanh (fun e => e) [3, HW, 2] 0 [.const x, .const v, .const u]

/-- Training loss on a batch of observed transitions `(x, v, u, 10Δx, 10Δv)`. -/
def dynLoss (batch : List (Float × Float × Float × Float × Float)) : Expr Float PW :=
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun (x, v, u, dx, dv) =>
      let out := dynNet x v u
      .add (sqErr (out.getD 0 (.const 0)) (.const dx)) (sqErr (out.getD 1 (.const 0)) (.const dv))))
-- ANCHOR_END: world_model

def vecOf (p : Array Float) : Vec Float PW := fun i => p[i.val]!

/-- One imagined step. -/
def dream (p : Array Float) (x v u : Float) : Float × Float :=
  let u := max (-1.0) (min 1.0 u)
  let out := dynNet x v u
  let dx := (out.getD 0 (.const 0)).eval (vecOf p)
  let dv := (out.getD 1 (.const 0)).eval (vecOf p)
  (x + dx / 10.0, v + dv / 10.0)

/-- The controller `u = tanh(w₀ x + w₁ v + w₂)`. -/
def policy (w : Array Float) (x v : Float) : Float := Float.tanh (w[0]! * x + w[1]! * v + w[2]!)

end LeanDL.Ch14
