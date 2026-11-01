import LeanDL.Core.Rng

/-!
# Chapter 7, part 2 — An Elman RNN with backpropagation through time

Parameters live in one flat array: `Wh` (nh×nh), `Wx` (nh), `b` (nh), `wo` (nh), `bo`.
The network reads a sequence of numbers and outputs one probability from its last state.
(The `Expr` of Chapter 4 is a tree, so unrolling a network whose units all read all previous
units would copy the history exponentially often; arrays avoid that.)
-/

namespace LeanDL.Rnn

def nParams (nh : Nat) : Nat := nh * nh + 3 * nh + 1

-- ANCHOR: forward
/-- All hidden states `h₀ … h_T` (row `t` holds `h_t`, with `h₀ = 0`) and the output
probability `σ(wo · h_T + bo)`. -/
def forward (nh : Nat) (p : Array Float) (xs : Array Float) : Array Float × Float := Id.run do
  let T := xs.size
  let oWx := nh * nh
  let ob := oWx + nh
  let owo := ob + nh
  let obo := owo + nh
  let mut hs := Array.replicate ((T + 1) * nh) 0.0
  for t in [0:T] do
    for j in [0:nh] do
      let mut a := p[ob + j]! + p[oWx + j]! * xs[t]!
      for i in [0:nh] do
        a := a + p[j * nh + i]! * hs[t * nh + i]!
      hs := hs.set! ((t + 1) * nh + j) (Float.tanh a)
  let mut z := p[obo]!
  for j in [0:nh] do
    z := z + p[owo + j]! * hs[T * nh + j]!
  return (hs, 1.0 / (1.0 + Float.exp (-z)))
-- ANCHOR_END: forward

-- ANCHOR: bptt
/-- Binary cross-entropy loss, its gradient with respect to all parameters, and `‖∂L/∂h_t‖`
for `t = T, …, 1` (in that order), which shows how the gradient fades as it travels back. -/
def lossGrad (nh : Nat) (p : Array Float) (xs : Array Float) (y : Float) :
    Float × Array Float × Array Float := Id.run do
  let T := xs.size
  let oWx := nh * nh
  let ob := oWx + nh
  let owo := ob + nh
  let obo := owo + nh
  let (hs, prob) := forward nh p xs
  let loss := -(y * Float.log prob + (1.0 - y) * Float.log (1.0 - prob))
  let mut g := Array.replicate (nParams nh) 0.0
  -- Output: gradient of cross-entropy through a sigmoid is `prob - y`.
  let dz := prob - y
  g := g.set! obo dz
  let mut dh := Array.replicate nh 0.0
  for j in [0:nh] do
    g := g.set! (owo + j) (dz * hs[T * nh + j]!)
    dh := dh.set! j (dz * p[owo + j]!)
  let mut norms := Array.mkEmpty T
  -- Backpropagation through time: walk the unrolled network from the last step to the first.
  for k in [0:T] do
    let t := T - k
    norms := norms.push (Float.sqrt (dh.foldl (fun s v => s + v * v) 0.0))
    let mut dprev := Array.replicate nh 0.0
    for j in [0:nh] do
      let hj := hs[t * nh + j]!
      let da := dh[j]! * (1.0 - hj * hj)
      g := g.set! (ob + j) (g[ob + j]! + da)
      g := g.set! (oWx + j) (g[oWx + j]! + da * xs[t - 1]!)
      for i in [0:nh] do
        g := g.set! (j * nh + i) (g[j * nh + i]! + da * hs[(t - 1) * nh + i]!)
        dprev := dprev.set! i (dprev[i]! + p[j * nh + i]! * da)
    dh := dprev
  return (loss, g, norms)
-- ANCHOR_END: bptt

/-- Mean loss and mean gradient over a dataset. -/
def batchLossGrad (nh : Nat) (p : Array Float) (data : Array (Array Float × Float)) :
    Float × Array Float := Id.run do
  let mut g := Array.replicate (nParams nh) 0.0
  let mut loss := 0.0
  for (xs, y) in data do
    let (l, gi, _) := lossGrad nh p xs y
    loss := loss + l
    g := (g.zip gi).map fun (a, b) => a + b
  let n := data.size.toFloat
  return (loss / n, g.map (· / n))

def accuracy (nh : Nat) (p : Array Float) (data : Array (Array Float × Float)) : Float := Id.run do
  let mut ok := 0
  for (xs, y) in data do
    let (_, prob) := forward nh p xs
    if (prob > 0.5) == (y > 0.5) then ok := ok + 1
  return ok.toFloat / data.size.toFloat

/-- A random bit sequence of length `T`. -/
def randomBits (r : Rng) (T : Nat) : Array Float × Rng := Id.run do
  let mut r := r
  let mut out := Array.mkEmpty T
  for _ in [0:T] do
    let (u, r') := r.uniform
    out := out.push (if u > 0.5 then 1.0 else 0.0)
    r := r'
  return (out, r)

/-- The memory task: the label is the *first* bit, so it must survive `T - 1` further steps. -/
def memoryTask (r : Rng) (T n : Nat) : Array (Array Float × Float) × Rng := Id.run do
  let mut r := r
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let (xs, r') := randomBits r T
    r := r'
    out := out.push (xs, xs[0]!)
  return (out, r)

end LeanDL.Rnn
