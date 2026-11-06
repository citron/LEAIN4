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
  -- Salve 2: one more figure for each chapter that has only one
  -- Ch02: XOR is not linearly separable
  let xsX := grid (0.0 - 0.3) 1.3 40
  save "xor_points" <| lineSvg 480 260 (0.0 - 0.3) 1.3 (0.0 - 0.3) 1.3
    "XOR: +1 on the diagonal, -1 on the anti-diagonal - no line separates them" "x1" "x2"
    [("+1 class (0,0) (1,1)", blue, curve xsX fun x => x),
     ("-1 class (0,1) (1,0)", orange, curve xsX fun x => 1.0 - x)]
  -- Ch04: the dead ReLU
  let xsA := grid (0.0 - 4.0) 4.0 80
  save "relu_dead" <| lineSvg 480 240 (0.0 - 4.0) 4.0 (0.0 - 1.0) 2.0
    "ReLU alive vs ReLU dead: y = max(0, x) and y = 0" "input x" "output"
    [("alive y = max(0, x)", blue, curve xsA fun x => max 0.0 x),
     ("dead unit: stuck at 0", orange, curve xsA fun _ => 0.0)]
  -- Ch06: the convolution window reads a patch of the input
  let img6 := (Array.range 8).map (fun i =>
    (Array.range 8).map (fun j =>
      if i >= 2 && i <= 5 && j >= 2 && j <= 5 then 1.0 - (i.toFloat * 8.0 + j.toFloat) / 200.0 else (i.toFloat + j.toFloat) / 30.0))
  save "conv_window" <| heatSvg 30 "Conv3x3: the window is a 3x3 dot product over a sliding patch" "row i" "col j" img6
  -- Ch07: gradient through the unrolled chain
  let xsD := grid 1.0 14.0 13
  save "rnn_chain" <| lineSvg 480 240 1.0 14.0 (0.0 - 12.0) 1.0
    "RNN: gradient magnitude through T unrolled steps (log10)" "time steps T" "log10 |grad|"
    [("typical  0.5^T", blue, curve xsD fun t => Float.log (Float.pow 0.5 t) / Float.log 10.0),
     ("worst    0.25^T", orange, curve xsD fun t => Float.log (Float.pow 0.25 t) / Float.log 10.0)]
  -- Ch08: what the LSTM gates compute
  let xsG := grid (0.0 - 6.0) 6.0 120
  save "lstm_gates" <| lineSvg 480 240 (0.0 - 6.0) 6.0 (0.0 - 1.5) 1.5
    "LSTM parts: f = sigmoid, i = sigmoid, c~ = tanh, f * c~" "gate input" "value"
    [("f = sigmoid", blue, curve xsG sigmoid),
     ("i = sigmoid", green, curve xsG sigmoid),
     ("c~ = tanh", orange, curve xsG fun x => Float.tanh x),
     ("f * c~  (with c~ = 1)", purple, curve xsG sigmoid)]
  -- Ch09: causal self-attention, uniform scores
  let attn9 := (Array.range 6).map (fun i =>
    (Array.range 6).map (fun j =>
      if j > i then 0.0 else 1.0 / (i.toFloat + 1.0)))
  save "attention_causal" <| heatSvg 44 "Causal self-attention (uniform scores): each row spreads over its own past" "query t" "key j" attn9
  -- Ch10: -log p(x) and the KL, the two halves of the ELBO
  let p10 (x : Float) : Float :=
    0.5 * normalPdf (0.0 - 1.0) 1.0 x + 0.5 * normalPdf 4.0 1.0 x
  let xsE := grid (0.0 - 5.0) 8.0 130
  let nll10 := xsE.map fun x => (x, 0.0 - Float.log (max 1e-9 (p10 x)))
  let kl10 := xsE.map fun x => (x, 0.5 * (x - 1.0) * (x - 1.0) - 0.5 - Float.log (max 1e-9 (p10 x)) - 0.5 * Float.log (2.0 * 3.141592653589793))
  save "elbo_parts" <| lineSvg 480 260 (0.0 - 5.0) 8.0 (0.0 - 1.0) 6.0
    "Ch10: -log p(x) and KL(q||p) - the ELBO is their sum" "x" "value"
    [("-log p(x)", blue, nll10),
     ("KL (q = N(1,1) to p)", green, kl10)]
  -- Ch13: TD(0) bootstrap error decays geometrically
  let xsT := grid 1.0 12.0 11
  save "td_bootstrap" <| lineSvg 480 240 1.0 12.0 0.0 1.1
    "TD(0) on a chain: V(s_i) = 0.5^i approaches the true value 1" "state i (steps to end)" "value"
    [("TD(0) V(s_i)", blue, curve xsT fun i => Float.pow 0.5 i),
     ("true value (10 steps away)", orange, curve xsT fun _ => 1.0)]
  -- Ch03: gradient signal through depth
  let xsS := grid 1.0 14.0 13
  save "depth_signal" <| lineSvg 480 240 1.0 14.0 (0.0 - 12.0) 1.0
    "MLP: first-layer gradient shrinks with depth (log10)" "depth L" "log10 |dL/dW0|"
    [("typical  0.5^L", blue, curve xsS fun l => Float.log (Float.pow 0.5 l) / Float.log 10.0),
     ("worst    0.25^L", orange, curve xsS fun l => Float.log (Float.pow 0.25 l) / Float.log 10.0)]
  -- Salve 3
  -- Ch01: the sigmoid derivative is a bell with peak 1/4
  let xs1 := grid (0.0 - 5.0) 5.0 160
  save "sigmoid_deriv" <| lineSvg 480 250 (0.0 - 5.0) 5.0 (0.0 - 0.1) 1.1
    "Sigmoid and derivative: sigma' = sigma(1 - sigma), peak 1/4" "input u" "value"
    [("sigma(u)", blue, curve xs1 sigmoid),
     ("sigma'(u) = sigma(1-sigma)", orange, curve xs1 fun u =>
        let g := sigmoid u
        g * (1.0 - g))]
  -- Ch05: L2 weight decay shrinks the fixed point
  let decay (lr lam : Float) : Array (Float × Float) := Id.run do
    let mut out := #[(0.0, 0.0)]
    let mut w := 0.0
    for t in List.range 80 do
      w := w - lr * (2.0 * (w - 1.0) + 2.0 * lam * w)
      out := out.push (t.toFloat + 1.0, w)
    return out
  save "weight_decay" <| lineSvg 480 250 1.0 80.0 (0.0 - 0.2) 1.2
    "SGD on (w-1)^2: decay lam = 1 settles at 0.5, not 1" "steps" "weight w"
    [("lam = 0  ->  w -> 1", blue, decay 0.1 0.0),
     ("lam = 1  ->  w -> 0.5", orange, decay 0.1 1.0)]
  -- Ch11: covering both modes beats collapsing on one (mode_collapse_reward)
  let xs11 := grid 0.1 4.0 60
  save "mode_collapse" <| lineSvg 480 250 0.1 4.0 0.0 1.2
    "Generator reward a*b/(a+b): covering modes beats collapsing" "generator mass a (b = 1)" "reward"
    [("collapse: a/(a+1)", orange, curve xs11 fun a => a / (a + 1.0)),
     ("covers both: a/(a+0.5)", blue, curve xs11 fun a => a / (a + 0.5))]
  -- Ch14: imagined rollouts drift by the compounding bound
  let xs14 := grid 0.0 10.0 20
  save "dream_drift" <| lineSvg 480 250 0.0 10.0 0.0 6.5
    "World model: per-step error compounds geometrically over k steps" "imagined steps k" "total drift"
    [("Lipschitz L = 1.2 (drift explodes)", orange, curve xs14 fun k => 0.1 * (Float.pow 1.2 k - 1.0) / 0.2),
     ("Lipschitz L = 0.5 (drift bounded)", blue, curve xs14 fun k => 0.2 * (1.0 - Float.pow 0.5 k))]
  -- Ch15: the spread penalty is exactly zero at collapse
  let xs15 := grid 0.0 3.0 60
  save "spread_collapse" <| lineSvg 480 250 0.0 3.0 0.0 18.0
    "JEPA spread of a 2-point batch is 2 d^2 - zero at collapse" "embedding distance d" "spread penalty"
    [("spread = 2 d^2", blue, curve xs15 fun d => 2.0 * d * d),
     ("collapsed batch (d = 0)", orange, curve xs15 fun _ => 0.0)]
  -- Ch16: ensembles kill variance, never bias
  let xs16 := grid 1.0 20.0 38
  save "bias_var" <| lineSvg 480 250 1.0 20.0 0.0 1.4
    "Ensemble risk = bias^2 + variance/n (bias^2 = 0.09, variance = 1)" "models n" "risk"
    [("variance 1/n", blue, curve xs16 fun n => 1.0 / n),
     ("ensemble risk 0.09 + 1/n", orange, curve xs16 fun n => 0.09 + 1.0 / n),
     ("bias^2 floor (unremovable)", grey, curve xs16 fun _ => 0.09)]
  -- Ch17: the mass on the positive decays as 1/(n+1) when blind
  let xs17 := grid 1.0 32.0 31
  save "infonce_mass" <| lineSvg 480 250 1.0 32.0 0.0 1.05
    "InfoNCE mass on the positive: blind 1/(n+1) vs gap 2" "negatives n" "probability"
    [("blind: 1/(n+1)", orange, curve xs17 fun n => 1.0 / (n + 1.0)),
     ("matched gap 2", blue, curve xs17 fun n =>
        7.389056 / (7.389056 + n))]
  -- Ch18: round quantization never errs by more than s/2 (roundq_err_le)
  let xs18 := grid (0.0 - 3.0) 3.0 200
  save "quant_grid" <| lineSvg 480 250 (0.0 - 3.0) 3.0 (0.0 - 0.8) 0.8
    "Round-to-nearest, grid s = 1: sawtooth error in [-1/2, 1/2]" "value x (grid s = 1)" "x - roundq x"
    [("rounding error", blue, curve xs18 fun x =>
        x - (Float.floor (x + 0.5))),
     ("bound +s/2", orange, curve xs18 fun _ => 0.5),
     ("bound -s/2", green, curve xs18 fun _ => 0.0 - 0.5)]
  -- Ch18: the training-loss decay theorem, drawn
  let xs19 := grid 1.0 40.0 39
  save "scaling_shape" <| lineSvg 480 250 1.0 40.0 1.0 4.5
    "train_decay: L(N) = Linf + c^N (L0 - Linf) falls geometrically to the floor Linf" "data/parameters N" "loss L(N)"
    [("L0 = 4, Linf = 1.5, c = 0.9", blue, curve xs19 fun n =>
        1.5 + Float.pow 0.9 n * 2.5),
     ("irreducible floor Linf", orange, curve xs19 fun _ => 1.5)]
  -- Salve 4
  -- Ch01: a neuron is a half-plane
  let xsA := grid (0.0 - 3.0) 3.0 40
  save "neuron_halfplane" <| lineSvg 480 260 (0.0 - 3.0) 3.0 (0.0 - 3.0) 3.0
    "A neuron is a half-plane: w.x = b is the boundary line" "x1" "x2"
    [("boundary 2 x1 - x2 = 0.5", blue, curve xsA fun x => 2.0 * x - 0.5),
     ("fires: w.x > b (shifted)", orange, curve xsA fun x => 2.0 * x + 0.5)]
  -- Ch03: 4 ReLU units bend a piecewise-linear sin
  save "mlp_stairs" <| lineSvg 480 250 0.0 6.3 (0.0 - 1.2) 1.2
    "A 4-unit ReLU MLP fits sin by straight segments" "x" "value"
    [("sin(x)", blue, curve (grid 0.0 6.3 80) Float.sin),
     ("ReLU fit, 4 units", orange,
      curve (grid 0.0 6.3 80) fun x =>
        2.0 / 3.141593 * x
        - 4.0 / 3.141593 * (if x > 1.570796 then x - 1.570796 else 0.0)
        + 4.0 / 3.141593 * (if x > 4.712389 then x - 4.712389 else 0.0))]
  -- Ch04: finite differences in Float hit the roundoff wall
  save "fd_drift" <| lineSvg 480 250 1.0 50.0 (0.0 - 52.0) 3.0
    "Central difference of sin at x = 1, h = 2^-k (log2 error): U-curve in Float" "k (h = 2^-k)" "log2 error"
    [("log2 |approx - cos 1|", blue,
      (Id.run do
        let mut out := #[(0.0, 0.0)]
        for k in List.range 50 do
          let h := Float.pow 0.5 (k.toFloat + 1.0)
          let app := (Float.sin (1.0 + h) - Float.sin (1.0 - h)) / (2.0 * h)
          let e := Float.abs (app - Float.cos 1.0)
          out := out.push (k.toFloat + 1.0, Float.log e / Float.log 2.0)
        return out))]
  -- Ch06: receptive field of stacked 3x3 convolutions
  save "rf_growth" <| lineSvg 480 250 1.0 8.0 0.0 18.0
    "Stacked 3x3 convs: receptive field 2L + 1 grows linearly with depth" "layers L" "field (pixels)"
    [("stacked 3x3: 2L + 1", blue, curve (grid 1.0 8.0 15) fun l => 2.0 * l + 1.0),
     ("one wide 5x5", orange, curve (grid 1.0 8.0 15) fun _ => 5.0)]
  -- Ch07: delayed copy, the RNN memory task
  save "lag_copy" <| lineSvg 480 240 0.0 10.0 (0.0 - 0.15) 1.2
    "Memory task y_t = x_(t-3): the pulse must arrive 3 steps late" "time t" "signal"
    [("input pulse x_t", blue, #[(0.0, 0.0), (2.5, 0.0), (3.0, 1.0), (3.5, 0.0), (10.0, 0.0)]),
     ("target y_t = x_(t-3)", orange, #[(0.0, 0.0), (5.5, 0.0), (6.0, 1.0), (6.5, 0.0), (10.0, 0.0)])]
  -- Ch08: the cell state carries a value with factor f
  save "cell_hold" <| lineSvg 480 250 0.0 40.0 0.0 1.05
    "Cell state written 1 at t = 0: f = 1 carries it forever, f < 1 fades" "steps t" "cell state c_t"
    [("f = 1", blue, curve (grid 0.0 40.0 41) fun _ => 1.0),
     ("f = 0.95", orange, curve (grid 0.0 40.0 41) fun t => Float.pow 0.95 t),
     ("f = 0.5 (plain RNN)", grey, curve (grid 0.0 40.0 41) fun t => Float.pow 0.5 t)]
  -- Ch09: the attention temperature
  save "attn_sharp" <| lineSvg 480 250 0.0 6.0 0.0 1.05
    "Attention: a logit gap beta puts e^beta / (e^beta + 3) on the top key" "logit gap beta" "weight, 4 keys"
    [("top key weight", blue, curve (grid 0.0 6.0 40) fun b =>
        Float.exp b / (Float.exp b + 3.0)),
     ("uniform 1/4", orange, curve (grid 0.0 6.0 40) fun _ => 0.25)]
  -- Ch10: the beta-VAE rate-distortion tradeoff
  save "beta_vae" <| lineSvg 480 250 0.1 10.0 0.0 1.05
    "beta-VAE model: distortion 1/(1+beta) vs rate beta/(1+beta)" "beta" "value"
    [("distortion 1/(1+beta)", blue, curve (grid 0.1 10.0 50) fun b => 1.0 / (1.0 + b)),
     ("rate beta/(1+beta)", orange, curve (grid 0.1 10.0 50) fun b => b / (1.0 + b))]
  -- Ch13: value iteration contracts toward the fixed point
  save "vi_contractions" <| lineSvg 480 250 0.0 12.0 0.0 1.05
    "Value iteration: the error to V* shrinks as gamma^k per sweep" "sweeps k" "error / initial"
    [("gamma = 0.9", blue, curve (grid 0.0 12.0 25) fun k => Float.pow 0.9 k),
     ("gamma = 0.5", orange, curve (grid 0.0 12.0 25) fun k => Float.pow 0.5 k)]
  -- Ch02: the perceptron mistake bound
  save "perceptron_bound" <| lineSvg 480 250 0.14 1.0 0.0 60.0
    "Perceptron bound 1/gamma^2: a thin margin costs samples" "margin gamma" "bound 1/gamma^2"
    [("1 / gamma^2", blue, curve (grid 0.14 1.0 40) fun g => 1.0 / (g * g)),
     ("cap 50", orange, curve (grid 0.14 1.0 40) fun _ => 50.0)]
  -- Ch05: heavy ball momentum damps the zigzag
  save "momentum_path" <| lineSvg 480 250 0.0 30.0 (0.0 - 1.0) 1.0
    "On a steep valley: plain SGD zigzags, momentum mu = 0.9 damps it" "steps k" "position"
    [("SGD mu = 0", blue, curve (grid 0.0 30.0 61) fun k =>
        Float.sin (1.5 * k) * Float.pow 0.98 k),
     ("momentum mu = 0.9", orange, curve (grid 0.0 30.0 61) fun k =>
        Float.sin (1.5 * k) * Float.pow 0.85 k)]
  -- Ch11: the optimal discriminator is the posterior
  save "disc_posterior" <| lineSvg 480 250 (0.0 - 3.0) 3.0 0.0 1.0
    "Optimal D*(x) = p / (p + q) for two Gaussians p = N(-1,1), q = N(1,1)" "x" "D*(x)"
    [("D*(x)", blue, curve (grid (0.0 - 3.0) 3.0 61) fun x =>
        let pp := Float.exp (-(x + 1.0) * (x + 1.0) / 2.0)
        let qq := Float.exp (-(x - 1.0) * (x - 1.0) / 2.0)
        pp / (pp + qq))]
  -- Ch12: the signal-to-noise ratio of the forward process
  save "snr_decay" <| lineSvg 480 250 1.0 20.0 0.0 12.0
    "Forward diffusion: SNR = alpha_bar / (1 - alpha_bar) collapses" "step t" "value"
    [("alpha_bar_t", blue, curve (grid 1.0 20.0 20) fun t => Float.pow 0.92 t),
     ("SNR", orange, curve (grid 1.0 20.0 20) fun t =>
        let a := Float.pow 0.92 t
        a / (1.0 - a))]
  -- Ch14: model-based error compounds, model-free accumulates
  save "planning_horizon" <| lineSvg 480 250 1.0 20.0 0.0 12.0
    "Plan error: model-based 0.1 L^k (L = 1.25) vs model-free 0.25 k" "horizon k" "error"
    [("model-based 0.1 x 1.25^k", blue, curve (grid 1.0 20.0 20) fun k => 0.1 * Float.pow 1.25 k),
     ("model-free 0.25 k", orange, curve (grid 1.0 20.0 20) fun k => 0.25 * k)]
  -- Ch15: the variance regularizer is a hinge on the batch spread
  save "var_hinge" <| lineSvg 480 240 0.0 2.0 0.0 1.1
    "Variance penalty max(0, delta - spread): zero once the batch is spread" "spread of embeddings" "penalty (delta = 1)"
    [("max(0, 1 - spread)", blue, curve (grid 0.0 2.0 41) fun x =>
        if x < 1.0 then 1.0 - x else 0.0)]
  -- Ch16: test risk is U-shaped in capacity
  save "capacity_u" <| lineSvg 480 250 1.0 40.0 0.0 1.2
    "Test risk = bias^2 + variance: the U bottoms where the two balance" "capacity n" "risk"
    [("bias^2 = 1/n", blue, curve (grid 1.0 40.0 40) fun n => 1.0 / n),
     ("variance = n / 400", orange, curve (grid 1.0 40.0 40) fun n => n / 400.0),
     ("sum", grey, curve (grid 1.0 40.0 40) fun n => 1.0 / n + n / 400.0)]
  -- Ch17: InfoNCE as a function of the positive similarity gap
  save "nce_temp" <| lineSvg 480 250 0.0 6.0 0.0 1.5
    "InfoNCE loss -log(e^s / (e^s + 3)) vs positive gap s: 1.39 blind, 0 aligned" "similarity gap s" "loss"
    [("loss (3 negatives)", blue, curve (grid 0.0 6.0 40) fun s =>
        -(Float.log (Float.exp s / (Float.exp s + 3.0))))]

  -- Ch19: the symmetric (CLIP) matched loss vs the shared positive gap
  save "clip_symm" <| lineSvg 480 250 0.0 10.0 0.0 0.75
    "CLIP loss [softplus(-g1) + softplus(-g2)] / 2 vs gaps" "gap (both directions)" "loss"
    [("both gaps = g", blue, curve (grid 0.0 10.0 50) fun g =>
        (Float.log (1.0 + Float.exp (-g)) + Float.log (1.0 + Float.exp (-g))) / 2.0),
     ("row gap 2, col gap g", orange, curve (grid 0.0 10.0 50) fun g =>
        (Float.log (1.0 + Float.exp (-2.0)) + Float.log (1.0 + Float.exp (-g))) / 2.0)]
  -- Ch19: the collapse floor of the symmetric loss grows with the batch
  save "clip_floor" <| lineSvg 480 240 1 16 0.0 4.0
    "Collapsed CLIP model pays log (n + 1): batch size raises the floor" "batch B = n + 1" "loss"
    [("log (B)", blue, curve (grid 1.0 16.0 16) fun b => Float.log b)]

  IO.println "figures written to ../website/static/img/"
