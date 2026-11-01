import LeanDL.Ch13.Rl
import LeanDL.Ch04.Network
import LeanDL.Core.Rng

/-!
# Chapter 13, part 2 — REINFORCE and Q-learning on a corridor

States `0 … 5`. Start in `1`; reaching `5` gives reward `+1`, reaching `0` gives `-1`; both end
the episode. Actions: `1` = right, `0` = left. A random walk reaches the goal with probability 1/5.
-/

namespace LeanDL.Ch13

open LeanDL.Ch04

abbrev PR : Nat := mlpParams [6, 8, 1]

def goal : Nat := 5
def gamma : Float := 0.95
def maxLen : Nat := 30

-- ANCHOR: pg_model
/-- Policy logit `z(s)`: a `6 → 8 → 1` network on a one-hot state; `P(right) = σ(z)`. -/
def logit (s : Nat) : Expr Float PR :=
  (mlpE .tanh (fun e => e) [6, 8, 1] 0
    ((List.range 6).map fun i => .const (if i == s then 1.0 else 0.0))).headD (.const 0)

/-- `log π(a | s)` as an expression, so that `backprop` gives `∇θ log π`. -/
def logPi (s a : Nat) : Expr Float PR :=
  if a == 1 then .log (.sigmoid (logit s))
  else .log (.sub (.const 1) (.sigmoid (logit s)))

/-- The REINFORCE surrogate loss: minus the sum of `(G - b) · log π(a|s)` over all steps. Its
gradient is the policy-gradient estimator. -/
def pgLoss (steps : List (Nat × Nat × Float)) (baseline : Float) (nEpisodes : Nat) : Expr Float PR :=
  .mul (.const (-1.0 / nEpisodes.toFloat))
    (Expr.sum (steps.map fun (s, a, g) => .mul (.const (g - baseline)) (logPi s a)))
-- ANCHOR_END: pg_model

def vecOf (p : Array Float) : Vec Float PR := fun i => p[i.val]!

def probRight (p : Array Float) (s : Nat) : Float :=
  1.0 / (1.0 + Float.exp (-(logit s).eval (vecOf p)))

/-- Environment step: `(next state, reward, done)`. -/
def envStep (s a : Nat) : Nat × Float × Bool :=
  let s' := if a == 1 then s + 1 else s - 1
  if s' == goal then (s', 1.0, true) else if s' == 0 then (s', -1.0, true) else (s', 0.0, false)

end LeanDL.Ch13
