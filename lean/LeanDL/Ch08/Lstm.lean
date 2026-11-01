import LeanDL.Ch07.Rnn

/-!
# Chapter 8, part 2 — An LSTM with backpropagation through time

Four gates per unit: forget `f`, input `i`, candidate `g`, output `o`.

    c_t = f ⊙ c_{t-1} + i ⊙ g          h_t = o ⊙ tanh c_t

Parameters, flat: for gate `k ∈ {f, i, g, o}` and unit `j` a block of `nh + 2` numbers
(`nh` recurrent weights, one input weight, one bias) at offset `(k·nh + j)(nh + 2)`;
then the readout `wo` (nh numbers) and `bo`.
-/

namespace LeanDL.Lstm

open LeanDL.Rnn

def nParams (nh : Nat) : Nat := 4 * nh * (nh + 2) + nh + 1

def sig (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

/-- Pre-activation of gate `k`, unit `j`, at step `t`. -/
def preact (nh : Nat) (p hs : Array Float) (t : Nat) (x : Float) (k j : Nat) : Float := Id.run do
  let o := (k * nh + j) * (nh + 2)
  let mut a := p[o + nh + 1]! + p[o + nh]! * x
  for i in [0:nh] do
    a := a + p[o + i]! * hs[t * nh + i]!
  return a

structure Fwd where
  hs : Array Float   -- (T+1) × nh
  cs : Array Float   -- (T+1) × nh
  fs : Array Float   -- T × nh, gate values
  is : Array Float
  gs : Array Float
  os : Array Float
  prob : Float

-- ANCHOR: forward
def forward (nh : Nat) (p : Array Float) (xs : Array Float) : Fwd := Id.run do
  let T := xs.size
  let mut hs := Array.replicate ((T + 1) * nh) 0.0
  let mut cs := Array.replicate ((T + 1) * nh) 0.0
  let mut fs := Array.replicate (T * nh) 0.0
  let mut is := Array.replicate (T * nh) 0.0
  let mut gs := Array.replicate (T * nh) 0.0
  let mut os := Array.replicate (T * nh) 0.0
  for t in [0:T] do
    for j in [0:nh] do
      let f := sig (preact nh p hs t xs[t]! 0 j)
      let i := sig (preact nh p hs t xs[t]! 1 j)
      let g := Float.tanh (preact nh p hs t xs[t]! 2 j)
      let o := sig (preact nh p hs t xs[t]! 3 j)
      -- The cell state is updated *additively*: this is the path the gradient can follow.
      let c := f * cs[t * nh + j]! + i * g
      fs := fs.set! (t * nh + j) f
      is := is.set! (t * nh + j) i
      gs := gs.set! (t * nh + j) g
      os := os.set! (t * nh + j) o
      cs := cs.set! ((t + 1) * nh + j) c
      hs := hs.set! ((t + 1) * nh + j) (o * Float.tanh c)
  let owo := 4 * nh * (nh + 2)
  let mut z := p[owo + nh]!
  for j in [0:nh] do
    z := z + p[owo + j]! * hs[T * nh + j]!
  return ⟨hs, cs, fs, is, gs, os, sig z⟩
-- ANCHOR_END: forward

def norm (v : Array Float) : Float := Float.sqrt (v.foldl (fun s x => s + x * x) 0.0)

-- ANCHOR: bptt
/-- Loss, gradient, and the sizes `‖∂L/∂h_t‖` and `‖∂L/∂c_t‖` for `t = T, …, 1`. -/
def lossGrad (nh : Nat) (p : Array Float) (xs : Array Float) (y : Float) :
    Float × Array Float × Array Float × Array Float := Id.run do
  let T := xs.size
  let fw := forward nh p xs
  let prob := fw.prob
  let loss := -(y * Float.log prob + (1.0 - y) * Float.log (1.0 - prob))
  let owo := 4 * nh * (nh + 2)
  let mut g := Array.replicate (nParams nh) 0.0
  let dz := prob - y
  g := g.set! (owo + nh) dz
  let mut dh := Array.replicate nh 0.0
  let mut dc := Array.replicate nh 0.0
  for j in [0:nh] do
    g := g.set! (owo + j) (dz * fw.hs[T * nh + j]!)
    dh := dh.set! j (dz * p[owo + j]!)
  let mut dhNorms := Array.mkEmpty T
  let mut dcNorms := Array.mkEmpty T
  for k in [0:T] do
    let t := T - k
    let mut dhPrev := Array.replicate nh 0.0
    let mut dcPrev := Array.replicate nh 0.0
    -- First pass: gradient arriving at c_t, then the four gate pre-activations.
    let mut da := Array.replicate (4 * nh) 0.0
    for j in [0:nh] do
      let c := fw.cs[t * nh + j]!
      let tc := Float.tanh c
      let o := fw.os[(t - 1) * nh + j]!
      let f := fw.fs[(t - 1) * nh + j]!
      let i := fw.is[(t - 1) * nh + j]!
      let gg := fw.gs[(t - 1) * nh + j]!
      let dcj := dc[j]! + dh[j]! * o * (1.0 - tc * tc)
      dc := dc.set! j dcj
      -- `dcj * f` is the cell path of the theorem: gradient times the forget gate.
      dcPrev := dcPrev.set! j (dcj * f)
      da := da.set! (0 * nh + j) (dcj * fw.cs[(t - 1) * nh + j]! * f * (1.0 - f))
      da := da.set! (1 * nh + j) (dcj * gg * i * (1.0 - i))
      da := da.set! (2 * nh + j) (dcj * i * (1.0 - gg * gg))
      da := da.set! (3 * nh + j) (dh[j]! * tc * o * (1.0 - o))
    dhNorms := dhNorms.push (norm dh)
    dcNorms := dcNorms.push (norm dc)
    -- Second pass: parameter gradients and the gradient sent to h_{t-1}.
    for gate in [0:4] do
      for j in [0:nh] do
        let d := da[gate * nh + j]!
        let o := (gate * nh + j) * (nh + 2)
        g := g.set! (o + nh) (g[o + nh]! + d * xs[t - 1]!)
        g := g.set! (o + nh + 1) (g[o + nh + 1]! + d)
        for i in [0:nh] do
          g := g.set! (o + i) (g[o + i]! + d * fw.hs[(t - 1) * nh + i]!)
          dhPrev := dhPrev.set! i (dhPrev[i]! + p[o + i]! * d)
    dh := dhPrev
    dc := dcPrev
  return (loss, g, dhNorms, dcNorms)
-- ANCHOR_END: bptt

def batchLossGrad (nh : Nat) (p : Array Float) (data : Array (Array Float × Float)) :
    Float × Array Float := Id.run do
  let mut g := Array.replicate (nParams nh) 0.0
  let mut loss := 0.0
  for (xs, y) in data do
    let (l, gi, _, _) := lossGrad nh p xs y
    loss := loss + l
    g := (g.zip gi).map fun (a, b) => a + b
  let n := data.size.toFloat
  return (loss / n, g.map (· / n))

def accuracy (nh : Nat) (p : Array Float) (data : Array (Array Float × Float)) : Float := Id.run do
  let mut ok := 0
  for (xs, y) in data do
    if ((forward nh p xs).prob > 0.5) == (y > 0.5) then ok := ok + 1
  return ok.toFloat / data.size.toFloat

/-- Uniform random weights, with every forget-gate bias set to `1` so that the gates start open. -/
def init (nh : Nat) (seed : UInt64) (scale : Float) : Array Float := Id.run do
  let (p, _) := (Rng.seed seed).uniformArray (nParams nh) scale
  let mut p := p
  for j in [0:nh] do
    p := p.set! (j * (nh + 2) + nh + 1) 1.0
  return p

end LeanDL.Lstm
