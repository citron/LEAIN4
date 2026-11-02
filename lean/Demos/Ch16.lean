import LeanDL.Ch16.Tools

open LeanDL LeanDL.Ch16

/-!
Chapter 16 demo: the *numeric* face of the exact theorems. The library
proves `kl_nonneg` and `crossEntropy_eq_entropy_add_kl` over exact `Rat`;
here we evaluate entropy, KL and cross-entropy with `Float` on concrete
distributions and watch the identity `CE = H + KL` and the inequality
`KL ≥ 0` hold up to rounding. The gap between the exact world (theorems)
and the floating world (experiments) is the gap this chapter keeps honest.
-/

/-- Cross-entropy `Σ -pᵢ log qᵢ` on Float arrays. -/
def ceF (p q : Array Float) : Float :=
  (Array.range p.size).foldl (fun s i => s - p[i]! * Float.log q[i]!) 0.0

/-- Entropy `Σ -pᵢ log pᵢ`. -/
def hF (p : Array Float) : Float := ceF p p

/-- KL `Σ pᵢ (log pᵢ − log qᵢ)`. -/
def klF (p q : Array Float) : Float :=
  (Array.range p.size).foldl
    (fun s i => s + p[i]! * (Float.log p[i]! - Float.log q[i]!)) 0.0

/-- The expectation of `v` under `p`. -/
def expF (p v : Array Float) : Float :=
  (Array.range p.size).foldl (fun s i => s + p[i]! * v[i]!) 0.0

/-- The variance of `v` under `p`. -/
def varF (p v : Array Float) : Float :=
  expF p (v.map fun x => x * x) - expF p v * expF p v

def showDist (name : String) (p : Array Float) : IO Unit :=
  IO.println (name ++ ": [" ++
    String.intercalate ", " (p.toList.map fun x => toString x) ++ "]")

def main : IO Unit := do
  -- A true distribution and three candidate models.
  let p : Array Float := #[0.7, 0.2, 0.08, 0.02]          -- the data
  let q1 : Array Float := #[0.6, 0.25, 0.1, 0.05]         -- a good model
  let q2 : Array Float := #[0.25, 0.25, 0.25, 0.25]       -- uniform: knows nothing
  let q3 : Array Float := #[0.05, 0.1, 0.25, 0.6]         -- confidently wrong
  showDist "p  (data)   " p
  showDist "q1 (good)   " q1
  showDist "q2 (uniform)" q2
  showDist "q3 (wrong)  " q3
  IO.println ""
  let h := hF p
  IO.println s!"H(p)          = {h}"
  for (name, q) in [("q1", q1), ("q2", q2), ("q3", q3)] do
    let ce := ceF p q
    let kl := klF p q
    IO.println s!"CE(p,{name})   = {ce}   KL = {kl}   H+KL = {h + kl}   gap = {ce - (h + kl)}"
  IO.println ""
  -- Expectation and variance of a reward vector under each model.
  let reward : Array Float := #[1.0, 0.5, -0.5, -1.0]
  for (name, q) in [("p ", p), ("q1", q1), ("q2", q2), ("q3", q3)] do
    IO.println s!"E[{name}]·r = {expF q reward}   Var[{name}]·r = {varF q reward}"
  IO.println ""
  -- Bias–variance: an ensemble of noisy models around the truth.
  -- risk(i) = bias(i)^2 + variance(i), summed over inputs with weights q.
  let q : Array Float := #[0.25, 0.25, 0.25, 0.25]        -- input distribution
  let target : Array Float := #[1.0, 2.0, 3.0, 4.0]       -- the true function
  -- three hypotheses: the truth shifted by noise at each input
  let f1 : Array Float := #[1.1, 1.8, 3.2, 3.9]
  let f2 : Array Float := #[0.9, 2.2, 2.8, 4.1]
  let f3 : Array Float := #[1.0, 2.0, 3.0, 3.9]
  let pw : Array Float := #[1/3, 1/3, 1/3]                -- uniform over hypotheses
  let mean : Array Float := (Array.range 4).map fun i =>
    expF pw #[f1[i]!, f2[i]!, f3[i]!]
  let risk : Array Float := (Array.range 4).map fun i =>
    expF pw #[(f1[i]! - target[i]!) * (f1[i]! - target[i]!),
              (f2[i]! - target[i]!) * (f2[i]! - target[i]!),
              (f3[i]! - target[i]!) * (f3[i]! - target[i]!)]
  let bias : Array Float := (Array.range 4).map fun i =>
    (mean[i]! - target[i]!) * (mean[i]! - target[i]!)
  let varc : Array Float := (Array.range 4).map fun i =>
    expF pw #[(f1[i]! - mean[i]!) * (f1[i]! - mean[i]!),
              (f2[i]! - mean[i]!) * (f2[i]! - mean[i]!),
              (f3[i]! - mean[i]!) * (f3[i]! - mean[i]!)]
  let r := expF q risk
  let b := expF q bias
  let v := expF q varc
  IO.println "Ensemble of 3 models, uniform hypothesis weights:"
  IO.println s!"  total risk        = {r}"
  IO.println s!"  (bias of mean)^2  = {b}"
  IO.println s!"  variance          = {v}"
  IO.println s!"  bias^2 + variance = {b + v}   gap = {r - (b + v)}"
  IO.println ""
  IO.println "KL ≥ 0 (Gibbs), CE = H + KL and risk = bias² + variance hold over Rat by proof;"
  IO.println "here they hold over Float up to rounding, as the gaps show."
