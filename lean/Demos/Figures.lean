import LeanDL.Core.Plot
import LeanDL.Core.Rng
import LeanDL.Ch12.Model
import LeanDL.Ch14.Model

/-!
# Figures of the book

`lake exe figures` writes the concept figures (curves computed by Lean itself) to
`../website/static/img/`. The training demos write their own figures.
-/

open LeanDL LeanDL.Plot

def blue := "#2e5aa8"
def orange := "#c4561a"
def green := "#2a9d5c"
def purple := "#8a4fb3"
def grey := "#888888"

def grid (lo hi : Float) (n : Nat) : Array Float :=
  (Array.range (n + 1)).map fun i => lo + (hi - lo) * i.toFloat / n.toFloat

def curve (xs : Array Float) (f : Float → Float) : Array (Float × Float) := xs.map fun x => (x, f x)

def sigmoid (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

def save (name : String) (svg : String) : IO Unit :=
  IO.FS.writeFile s!"../website/static/img/{name}.svg" svg

def normalPdf (m s x : Float) : Float :=
  Float.exp (-(x - m) * (x - m) / (2.0 * s * s)) / (s * Float.sqrt (2.0 * 3.141592653589793))

def main : IO Unit := do
  -- Chapter 1: the four activation functions
  let xs := grid (-4.0) 4.0 160
  save "activations" <| lineSvg 480 280 (-4.0) 4.0 (-2.0) 2.0 "Activation functions" "input u" "output"
    [("step", grey, curve xs fun x => if x > 0.0 then 1.0 else 0.0),
     ("sigmoid", blue, curve xs sigmoid),
     ("tanh", orange, curve xs Float.tanh),
     ("ReLU", green, curve xs fun x => if x > 0.0 then x else 0.0)]
  -- Chapter 2: mistakes per epoch (the numbers printed by `lake exe ch02`)
  let pts (l : List Nat) : Array (Float × Float) :=
    (l.toArray.mapIdx fun i m => (i.toFloat, m.toFloat))
  save "perceptron_mistakes" <| lineSvg 480 260 0.0 8.0 0.0 8.0 "Perceptron mistakes per epoch" "epoch" "mistakes"
    [("AND", blue, pts [2, 3, 3, 2, 2, 3, 2, 1, 0]),
     ("OR", green, pts [3, 1, 2, 2, 1, 0]),
     ("XOR", orange, pts [4, 4, 4, 4, 4, 4, 4, 4, 4])]
  -- Chapter 3: gradient descent on L(w) = w^2 for four learning rates
  let gd (eta : Float) : Array (Float × Float) := Id.run do
    let mut w := 1.0
    let mut out := #[(0.0, w)]
    for k in [1:21] do
      w := w - eta * 2.0 * w
      out := out.push (k.toFloat, w)
    return out
  save "gradient_descent" <| lineSvg 480 280 0.0 20.0 (-1.5) 1.5 "Gradient descent on L(w) = w^2, start w = 1" "step" "w"
    [("rate 0.05", blue, gd 0.05), ("rate 0.4", green, gd 0.4), ("rate 0.9", purple, gd 0.9), ("rate 1.05", orange, gd 1.05)]
  -- Chapter 7: gradient of a one-unit RNN with |tanh'| <= 1 and recurrent weight w: size at most |w|^T
  let steps := grid 0.0 30.0 30
  let logPow (w : Float) : Array (Float × Float) := curve steps fun t => t * Float.log10 w
  save "vanishing" <| lineSvg 480 280 0.0 32.0 (-12.0) 4.0 "Size of the RNN gradient after T steps" "T (steps back in time)" "log10 of |w|^T"
    [("w = 0.5", blue, logPow 0.5), ("w = 0.9", green, logPow 0.9), ("w = 1.0", grey, logPow 1.0), ("w = 1.1", orange, logPow 1.1)]
  -- Chapter 8: the LSTM highway multiplies forget gates instead
  let steps100 := grid 0.0 100.0 100
  let logPow100 (w : Float) : Array (Float × Float) := curve steps100 fun t => t * Float.log10 w
  save "highway" <| lineSvg 480 280 0.0 100.0 (-30.0) 10.0 "Gradient along the memory path" "T (steps back in time)" "log10 of the product"
    [("RNN factor 0.5", orange, logPow100 0.5), ("forget gate 0.9", purple, logPow100 0.9),
     ("forget gate 0.99", blue, logPow100 0.99), ("forget gate 1.0", green, logPow100 1.0)]
  -- Chapter 9: a causal mask with uniform scores: position t averages positions 0..t
  save "causal_mask" <| heatSvg 44 "Causal attention (equal scores)" "query position t" "key position j"
    ((Array.range 6).map fun t => (Array.range 6).map fun j => if j ≤ t then 1.0 / (t + 1).toFloat else 0.0)
  -- Chapter 11: the optimal discriminator between a real and a generated density
  let gx := grid (-4.0) 6.0 200
  save "optimal_discriminator" <| lineSvg 480 280 (-4.0) 6.0 0.0 1.2 "Optimal discriminator D*(x) = a / (a + b)" "x" "density / probability"
    [("real data a(x)", blue, curve gx (normalPdf 2.0 1.0)),
     ("generated b(x)", orange, curve gx (normalPdf 0.0 1.2)),
     ("D*(x)", green, curve gx fun x => normalPdf 2.0 1.0 x / (normalPdf 2.0 1.0 x + normalPdf 0.0 1.2 x))]
  -- Chapter 12: signal and noise levels along the schedule, and the data being destroyed
  let tt := (Array.range (LeanDL.Ch12.T + 1))
  save "noise_schedule" <| lineSvg 480 280 0.0 20.0 0.0 1.2 "The forward process" "noising step t" "level"
    [("signal factor", blue, tt.map fun t => (t.toFloat, Float.sqrt LeanDL.Ch12.abars[t]!)),
     ("noise level", orange, tt.map fun t => (t.toFloat, Float.sqrt (1.0 - LeanDL.Ch12.abars[t]!)))]
  let sample (t : Nat) : Array Float := Id.run do
    let mut r := Rng.seed (100 + t.toUInt64)
    let mut out := #[]
    let ab := LeanDL.Ch12.abars[t]!
    for _ in [0:4000] do
      let (g, r1) := r.normal
      let (u, r2) := r1.uniform
      let (e, r3) := r2.normal
      r := r3
      let x0 := (if u < 0.5 then -2.0 else 2.0) + 0.4 * g
      out := out.push (Float.sqrt ab * x0 + Float.sqrt (1.0 - ab) * e)
    return out
  save "forward_diffusion" <| histSvg 480 200 (-5.0) 5.0 40 "Data at noising steps 0, 4, 10 and 20"
    [("t = 0", blue, sample 0), ("t = 4", green, sample 4), ("t = 10", purple, sample 10), ("t = 20", orange, sample 20)]
  -- Chapter 13: value iteration error shrinks like gamma^k
  let ks := grid 0.0 100.0 100
  let geo (g : Float) : Array (Float × Float) := curve ks fun k => Float.exp (k * Float.log g)
  save "value_iteration" <| lineSvg 480 280 0.0 100.0 0.0 1.2 "Value iteration: remaining error" "sweep k" "error / initial error"
    [("gamma 0.9", blue, geo 0.9), ("gamma 0.95", green, geo 0.95), ("gamma 0.99", orange, geo 0.99)]
  -- Chapter 14: the bound of `compounding_error` for a one-step error of 1
  let kk := grid 0.0 30.0 30
  let bound (l : Float) : Array (Float × Float) :=
    curve kk fun k => if l == 1.0 then k else (Float.exp (k * Float.log l) - 1.0) / (l - 1.0)
  save "compounding" <| lineSvg 480 280 0.0 32.0 0.0 40.0 "Imagined-rollout error bound (one-step error = 1)" "imagined steps k" "bound on the error"
    [("L = 0.8", green, bound 0.8), ("L = 1.0", blue, bound 1.0), ("L = 1.1", orange, bound 1.1)]
  -- Chapter 14: real rollout against a rollout of a model whose gravity term is 10 % too strong
  let rollout (gravity : Float) : Array (Float × Float) := Id.run do
    let mut x := 0.5
    let mut v := 0.0
    let mut out := #[(0.0, x)]
    for k in [1:41] do
      let u := 0.3 * Float.sin (0.3 * k.toFloat)
      let u := max (-1.0) (min 1.0 u)
      let x' := x + 0.1 * v
      let v' := 0.97 * v + 0.15 * u + gravity * Float.sin x
      x := x'
      v := v'
      out := out.push (k.toFloat, x)
    return out
  let real := rollout 0.1
  let model := rollout 0.11
  save "rollout_drift" <| lineSvg 480 280 0.0 40.0 0.0 8.0 "Open-loop rollout with the same actions" "step" "position x"
    [("real world", blue, real), ("imagined (gravity 10 % off)", orange, model),
     ("difference x 10", grey, (Array.range 41).map fun k => (k.toFloat, 10.0 * Float.abs (real[k]!.2 - model[k]!.2)))]
  -- Chapter 15: the EMA target closes a fraction (1 - m) of the gap at each step
  let ks2 := grid 0.0 200.0 200
  let emaGap (m : Float) : Array (Float × Float) := curve ks2 fun k => Float.exp (k * Float.log m)
  save "ema_distance" <| lineSvg 480 280 0.0 200.0 0.0 1.2 "Distance between target and context parameters" "update k" "distance / initial distance"
    [("m = 0.9", orange, emaGap 0.9), ("m = 0.99", blue, emaGap 0.99), ("m = 0.999", green, emaGap 0.999)]
  -- Chapter 15: with the variance penalty, collapse scores w * gamma, an informative solution scores 0
  let ws := grid 0.0 2.0 20
  save "collapse_penalty" <| lineSvg 480 280 0.0 2.0 0.0 2.0 "Objective of a perfect predictor (gamma = 1)" "penalty weight w" "total objective"
    [("collapsed (spread 0)", orange, curve ws fun w => w), ("informative (spread >= gamma)", green, curve ws fun _ => 0.0)]
  -- Chapter 18: quantization error of the two grids, floor (error in [0, s)) and
  -- round-to-nearest (error in (-s/2, s/2]) — the bounds of quant_bound / roundq_err_le.
  save "quantization" <| lineSvg 480 260 (-4.0) 4.0 (-0.8) 1.2 "Quantization error, step s = 1" "value x" "x - Q(x)"
    [("floor grid", orange, curve (grid (-4.0) 4.0 160) fun x => x - Float.floor x),
     ("round grid", blue, curve (grid (-4.0) 4.0 160) fun x => x - Float.round x)]
  -- Chapter 18: MoE load balance. The collision probability sum p^2 of a router
  -- p_i proportional to (i+1)^alpha over E = 9 experts, times E (so the floor of
  -- balance_ge sits at 1.0): uniform (alpha = 0) attains it; skew raises it.
  let collide (alpha : Float) : Float :=
    let e := (9 : Nat)
    let Z := (Array.range e).foldl (fun acc j => acc + Float.pow (j.toFloat + 1.0) alpha) 0.0
    (Array.range e).foldl (fun acc j =>
      let p := Float.pow (j.toFloat + 1.0) alpha / Z
      acc + p * p) 0.0
  save "moe_balance" <| lineSvg 480 260 0.0 4.0 0.8 6.0 "MoE collision probability E * sum p^2 (floor = 1)" "router skew alpha" "E * sum p^2"
    [("collision probability", blue, curve (grid 0.0 4.0 40) collide)]

  -- Chapter 4: the chain rule through a deep stack. A sigmoid unit has |f'| <= 1/4,
  -- so a stack of sigmoid layers multiplies the end-to-end gradient by at most (1/4)^L:
  -- it vanishes exponentially. This is why ReLU (local slope 1) took over deep nets.
  let stackL := grid 0.0 14.0 28
  save "chain_stack" <| lineSvg 480 260 0.0 14.0 (-9.0) 1.0 "End-to-end gradient through a stack of sigmoid layers" "layers L" "log10 of the gradient"
    [("worst case (1/4)^L", orange, curve stackL fun l => l * Float.log10 0.25),
     ("typical (0.5)^L", blue, curve stackL fun l => l * Float.log10 0.5)]
  -- Chapter 5: one-dimensional SGD on a smooth loss with curvature 2 around the
  -- minimizer w = 0: iterates stay bounded while eta < 1, and explode past it.
  let etas := grid 0.05 1.6 63
  let gdEnd (eta : Float) : Float := Id.run do
    let mut w := 1.0
    for _ in [1:600] do w := w - eta * 2.0 * w
    return if Float.abs w < 300.0 then Float.abs w else 300.0
  save "lr_stability" <| lineSvg 480 260 0.0 1.6 0.0 64.0 "SGD |w| after 600 steps: the learning-rate cliff" "learning rate eta" "|w| (capped at 64)"
    [("start w = 1", blue, curve etas gdEnd)]
  -- Chapters 16-17: the InfoNCE floor. One positive, n negatives, blind embedding:
  -- the loss is exactly log(n+1) (infoNce_collapse), and a matched pair costs
  -- log(1 + exp(lo - hi)) (matched_loss), = log 2 when the model is blind.
  let ns := grid 0.0 32.0 64
  save "infonce_floor" <| lineSvg 480 260 0.0 32.0 0.0 4.0 "InfoNCE: the floor theorems predict" "negatives n" "loss"
    [("blind: log(n+1)", orange, curve ns fun n => Float.log (n + 1.0)),
     ("matched pair, gap 0: log 2", grey, curve ns fun _ => Float.log 2.0),
     ("matched pair, gap 2", green, curve ns fun _ => Float.log (1.0 + Float.exp (-2.0)))]
  -- Chapter 16: the entropy of a binary source peaks, flat, at the fair coin.
  let ps := grid 0.001 0.999 99
  save "entropy_coin" <| lineSvg 480 260 0.0 1.0 0.0 1.1 "Entropy of a biased coin" "p (probability of heads)" "entropy H(p)"
    [("binary entropy H(p)", blue,
      curve ps fun p => -(p * Float.log p / Float.log 2.0 + (1.0 - p) * Float.log (1.0 - p) / Float.log 2.0))]
  -- Chapter 16: KL is not a distance (asymmetric): coding p = 0.5 with a code
  -- built for q, in both orders (Core/Prob).
  let qs := grid 0.02 0.98 96
  let binKL (p q : Float) : Float := p * (Float.log p - Float.log q) / Float.log 2.0
    + (1.0 - p) * (Float.log (1.0 - p) - Float.log (1.0 - q)) / Float.log 2.0
  save "kl_asymmetry" <| lineSvg 480 260 0.0 1.0 0.0 1.1 "KL divergence is not a distance" "q (code built for p = 0.5)" "bits of waste"
    [("KL(p, q)  from p = 0.5", blue, curve qs fun q => binKL 0.5 q),
     ("KL(q, p)  the other order", orange, curve qs fun q => binKL q 0.5)]
  -- Chapter 17: temperature sharpens the softmax. One positive at score 1, one
  -- negative at 0: the mass on the positive is exp(1/t) / (exp(1/t) + 1).
  let ts := grid 0.1 2.0 95
  save "softmax_sharp" <| lineSvg 480 260 0.0 2.0 0.0 1.05 "Temperature sharpens the softmax (scores 1 and 0)" "temperature tau" "mass on the positive"
    [("exp(1/t) / (exp(1/t) + 1)", blue,
      curve ts fun t => let e := Float.exp (1.0 / t); e / (e + 1.0))]
  -- Chapter 5: the price of Float. Adding 0.1 ten thousand times: the exact
  -- answer is the integer 1000 (a Rat certificate), the Float loop is not -
  -- 0.1 is not a binary fraction, and every addition rounds.
  let sum10k : Array (Float × Float) := Id.run do
    let mut acc := 0.0
    let mut out := #[]
    for k in [1:10001] do
      acc := acc + 0.1
      out := out.push (k.toFloat, acc - k.toFloat / 10.0)
    return out
  let dmax := (sum10k.foldl (fun m p => max m (Float.abs p.2)) 0.0) * 1.5e12
  save "float_drift" <| lineSvg 480 260 0.0 10000.0 (0.0 - dmax) dmax
    "Float: 10 000 additions of 0.1, drift vs the exact answer (units 1e-12)" "additions" "drift x 1e12"
    [("accumulated rounding", orange, sum10k.map (fun q => (q.1, q.2 * 1e12)))]
  -- Chapter 17: the closed form of the matched pair, loss = log(1 + exp(lo - hi)).
  let gaps := grid (-6.0) 10.0 80
  save "matched_gap" <| lineSvg 480 260 (-6.0) 10.0 (-0.2) 3.0 "Matched pair: loss = log(1 + exp(lo - hi))" "similarity gap  hi - lo" "InfoNCE loss"
    [("matched_loss", blue, curve gaps fun g => Float.log (1.0 + Float.exp (-g))),
     ("blind model: log 2", grey, curve gaps fun _ => Float.log 2.0)]
  -- Chapter 5 (Core/Interval.lean): the number-line dictionary of the layer.
  IO.println "figures written to ../website/static/img/"
