import LeanDL.Ch15.Jepa
import LeanDL.Ch04.Network
import LeanDL.Core.Rng

/-!
# Chapter 15, part 2 — A JEPA with an action-conditioned predictor

A hidden angle `θ` generates *views* `(cos θ, sin θ, noise, noise)`, the last two coordinates being
large, unpredictable distractors. The target view is the view of `θ + δ`, where `δ` is an action.
The encoder, the predictor and (optionally) the EMA target encoder all live in one parameter
vector, so that `backprop` gives every gradient and a *mask* implements stop-gradient.
-/

namespace LeanDL.Ch15

open LeanDL.Ch04

abbrev PE : Nat := mlpParams [4, 8, 2]    -- encoder: 58
abbrev PP : Nat := mlpParams [3, 8, 2]    -- predictor: 50
abbrev PJ : Nat := PE + PP + PE           -- context encoder, predictor, target encoder: 166

-- ANCHOR: jepa_model
/-- Encoder whose parameters start at `base`; it returns a 2-dimensional embedding. -/
def encE (base : Nat) (view : List Float) : List (Expr Float PJ) :=
  mlpE .tanh (fun e => e) [4, 8, 2] base (view.map .const)

/-- The predictor maps the context embedding and the action `δ` to a predicted target embedding. -/
def predE (z : List (Expr Float PJ)) (δ : Float) : List (Expr Float PJ) :=
  mlpE .tanh (fun e => e) [3, 8, 2] PE (z ++ [.const δ])

/-- Prediction loss over a batch of `(context view, target view, action)`. With `ema = true` the
target is computed by the *separate* target encoder (parameters `PE + PP …`); otherwise by the
context encoder itself, and gradients flow through both paths. -/
def predLoss (ema : Bool) (batch : List (List Float × List Float × Float)) : Expr Float PJ :=
  let tbase := if ema then PE + PP else 0
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun (c, y, δ) =>
      let pz := predE (encE 0 c) δ
      let tz := encE tbase y
      Expr.sum ((pz.zip tz).map fun (a, b) => sqErr a b)))
-- ANCHOR_END: jepa_model

-- ANCHOR: vicreg
/-- Mean of the `d`-th embedding coordinate over a batch of context views. -/
def meanE (d : Nat) (batch : List (List Float)) : Expr Float PJ :=
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun c => (encE 0 c).getD d (.const 0)))

/-- Variance of coordinate `d`. -/
def varE (d : Nat) (batch : List (List Float)) : Expr Float PJ :=
  let m := meanE d batch
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun c => sqErr ((encE 0 c).getD d (.const 0)) m))

/-- Covariance between the two coordinates. -/
def covE (batch : List (List Float)) : Expr Float PJ :=
  let m0 := meanE 0 batch
  let m1 := meanE 1 batch
  .mul (.const (1.0 / batch.length.toFloat))
    (Expr.sum (batch.map fun c =>
      .mul (.sub ((encE 0 c).getD 0 (.const 0)) m0) (.sub ((encE 0 c).getD 1 (.const 0)) m1)))

/-- The anti-collapse regulariser: a hinge keeping each coordinate's variance above `γ`
(the `vreg` of `Ch15/Jepa.lean`) plus a penalty on the covariance between coordinates. -/
def regLoss (γ wv wc : Float) (batch : List (List Float)) : Expr Float PJ :=
  .add
    (.mul (.const wv) (Expr.sum ([0, 1].map fun d => .relu (.sub (.const γ) (varE d batch)))))
    (.mul (.const wc) (.mul (covE batch) (covE batch)))
-- ANCHOR_END: vicreg

def vecOf (p : Array Float) : Vec Float PJ := fun i => p[i.val]!

/-- Embedding of a view by the context encoder. -/
def embed (p : Array Float) (view : List Float) : Array Float :=
  ((encE 0 view).map fun e => e.eval (vecOf p)).toArray

/-- A view of the hidden angle: two informative coordinates, two large distractors. -/
def mkView (θ : Float) (r : Rng) : List Float × Rng :=
  let (a, r) := r.normal
  let (b, r) := r.normal
  let (c, r) := r.normal
  let (d, r) := r.normal
  ([Float.cos θ + 0.1 * a, Float.sin θ + 0.1 * b, 3.0 * c, 3.0 * d], r)

end LeanDL.Ch15
