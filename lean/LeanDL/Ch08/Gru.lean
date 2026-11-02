import LeanDL.Ch07.Rnn

/-!
# Chapter 8, part 3 — The GRU: a lighter gated unit

Two gates per unit: the update gate `z` and the reset gate `r`.

    n_t = tanh(a_r + r_t ⊙ a_h)        (candidate, the reset gate scales the past)
    h_t = (1 − z_t) ⊙ n_t + z_t ⊙ h_{t−1}

There is no separate cell state: the *hidden state itself* is updated by a convex mix of the
old state and the new candidate, so the gradient reaching `h_{t−1}` is a product of factors
`z_t ∈ (0, 1)` — the same constant-error carousel as the LSTM's forget gates, in half the
parameters. The BPTT below is hand-coded, like the LSTM's, and `lake exe gru` checks every
partial derivative against central finite differences.

Parameters, flat: for gate `k ∈ {r, z}` and unit `j` a block of `nh + 2` numbers
(`nh` recurrent weights, one input weight, one bias) at offset `(k·nh + j)(nh + 2)`;
for the candidate `n`, unit `j` a block of `nh + 1` numbers (`nh` recurrent weights,
one bias) at offset `2·nh·(nh + 2) + j·(nh + 1)` (the reset gate multiplies the recurrent
part, the input weight is absent — the standard GRU form); then the readout `wo`
(`nh` numbers) and `bo`.
-/

namespace LeanDL.Gru

open LeanDL.Rnn

def nParams (nh : Nat) : Nat := 2 * nh * (nh + 2) + nh * (nh + 1) + nh + 1

def sig (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

/-- Pre-activation of the *input* part for gate `k ∈ {r, z}`, unit `j`, at step `t`:
bias + input weight · x. -/
def preactIn (nh : Nat) (p : Array Float) (_t : Nat) (x : Float) (k j : Nat) : Float :=
  p[(k * nh + j) * (nh + 2) + nh + 1]! + p[(k * nh + j) * (nh + 2) + nh]! * x

/-- Pre-activation of gate `k ∈ {0 = r, 1 = z, 2 = n}`, unit `j`, given the previous hidden
row `hprev` (scaled by the reset gate when `k = 2`). -/
def preact (nh : Nat) (p : Array Float) (hprev : Array Float) (x : Float)
    (r _z : Nat → Float) (k j : Nat) : Float := Id.run do
  if k < 2 then
    let o := (k * nh + j) * (nh + 2)
    let mut a := p[o + nh + 1]! + p[o + nh]! * x
    for i in [0:nh] do
      a := a + p[o + i]! * hprev[i]!
    return a
  else
    let o := 2 * nh * (nh + 2) + j * (nh + 1)
    let mut a := p[o + nh]!
    for i in [0:nh] do
      a := a + r i * (p[o + i]! * hprev[i]!)
    return a

structure Fwd where
  hs : Array Float   -- (T+1) × nh
  rs : Array Float   -- T × nh, gate values
  zs : Array Float
  ns : Array Float
  prob : Float

-- ANCHOR: forward
def forward (nh : Nat) (p : Array Float) (xs : Array Float) : Fwd := Id.run do
  let T := xs.size
  let mut hs := Array.replicate ((T + 1) * nh) 0.0
  let mut rs := Array.replicate (T * nh) 0.0
  let mut zs := Array.replicate (T * nh) 0.0
  let mut ns := Array.replicate (T * nh) 0.0
  for t in [0:T] do
    let rfun := fun j => rs[t * nh + j]!
    let zfun := fun j => zs[t * nh + j]!
    for j in [0:nh] do
      let hprev := hs.extract (t * nh) ((t + 1) * nh)
      let r := sig (preact nh p hprev xs[t]! rfun zfun 0 j)
      let z := sig (preact nh p hprev xs[t]! rfun zfun 1 j)
      let n := Float.tanh (preact nh p hprev xs[t]! (fun _ => r) (fun _ => z) 2 j)
      -- The state is a convex mix: this is the path the gradient follows.
      let h := (1.0 - z) * n + z * hs[t * nh + j]!
      rs := rs.set! (t * nh + j) r
      zs := zs.set! (t * nh + j) z
      ns := ns.set! (t * nh + j) n
      hs := hs.set! ((t + 1) * nh + j) h
  let owo := 2 * nh * (nh + 2) + nh * (nh + 1)
  let mut acc := hs.extract (T * nh) ((T + 1) * nh)
  let mut z0 := 0.0
  for j in [0:nh] do
    z0 := z0 + p[owo + j]! * acc[j]!
  z0 := z0 + p[owo + nh]!
  return ⟨hs, rs, zs, ns, sig z0⟩
-- ANCHOR_END: forward

def norm (v : Array Float) : Float := Float.sqrt (v.foldl (fun s x => s + x * x) 0.0)

-- ANCHOR: bptt
/-- Loss, gradient, and the sizes `‖∂L/∂h_t‖` for `t = T, …, 1`. -/
def lossGrad (nh : Nat) (p : Array Float) (xs : Array Float) (y : Float) :
    Float × Array Float × Array Float := Id.run do
  let T := xs.size
  let fw := forward nh p xs
  let prob := fw.prob
  let loss := -(y * Float.log prob + (1.0 - y) * Float.log (1.0 - prob))
  let owo := 2 * nh * (nh + 2) + nh * (nh + 1)
  let mut g := Array.replicate (nParams nh) 0.0
  let dz := prob - y
  g := g.set! (owo + nh) dz
  let mut dh := Array.replicate nh 0.0
  for j in [0:nh] do
    g := g.set! (owo + j) (dz * fw.hs[T * nh + j]!)
    dh := dh.set! j (dz * p[owo + j]!)
  let mut dhNorms := Array.mkEmpty T
  for k in [0:T] do
    let t := T - k
    let mut dhPrev := Array.replicate nh 0.0
    -- First pass: the three gate pre-activation gradients.
    let mut da := Array.replicate (3 * nh) 0.0
    for j in [0:nh] do
      let hprevj := fw.hs[(t - 1) * nh + j]!
      let z := fw.zs[(t - 1) * nh + j]!
      let n := fw.ns[(t - 1) * nh + j]!
      let dj := dh[j]!
      -- h = (1−z)·n + z·hprev, so ∂h/∂z = hprev − n and ∂h/∂n = 1 − z.
      da := da.set! (1 * nh + j) (dj * (hprevj - n) * z * (1.0 - z))
      da := da.set! (2 * nh + j) (dj * (1.0 - z) * (1.0 - n * n))
    -- The candidate reads the recurrent part through the reset gate:
    -- a_n(j) = b_j + Σ_i r_i · p_ji · h_i, so ∂L/∂a_r(i) = Σ_j da_n(j) · p_ji · h_i,
    -- then da_r(i) = that · r_i(1 − r_i).
    let mut dra := Array.replicate nh 0.0
    for j in [0:nh] do
      let dn := da[2 * nh + j]!
      let o := 2 * nh * (nh + 2) + j * (nh + 1)
      for i in [0:nh] do
        dra := dra.set! i (dra[i]! + dn * p[o + i]! * fw.hs[(t - 1) * nh + i]!)
    for i in [0:nh] do
      let r := fw.rs[(t - 1) * nh + i]!
      da := da.set! (0 * nh + i) (dra[i]! * r * (1.0 - r))
    -- Second pass: parameter gradients and the gradient sent to h_{t−1}.
    -- Gates r and z read hprev through their own recurrent weights.
    for gate in [0:3] do
      for j in [0:nh] do
        let d := da[gate * nh + j]!
        if gate < 2 then
          let o := (gate * nh + j) * (nh + 2)
          g := g.set! (o + nh) (g[o + nh]! + d * xs[t - 1]!)
          g := g.set! (o + nh + 1) (g[o + nh + 1]! + d)
          for i in [0:nh] do
            g := g.set! (o + i) (g[o + i]! + d * fw.hs[(t - 1) * nh + i]!)
            dhPrev := dhPrev.set! i (dhPrev[i]! + p[o + i]! * d)
        else
          let o := 2 * nh * (nh + 2) + j * (nh + 1)
          g := g.set! (o + nh) (g[o + nh]! + d)
          for i in [0:nh] do
            let r := fw.rs[(t - 1) * nh + i]!
            g := g.set! (o + i) (g[o + i]! + d * r * fw.hs[(t - 1) * nh + i]!)
            dhPrev := dhPrev.set! i (dhPrev[i]! + p[o + i]! * d * r)
    dhNorms := dhNorms.push (norm dh)
    dh := dhPrev
  return (loss, g, dhNorms)
-- ANCHOR_END: bptt

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
    if ((forward nh p xs).prob > 0.5) == (y > 0.5) then ok := ok + 1
  return ok.toFloat / data.size.toFloat

/-- Uniform random weights, with every update-gate bias set to `0.5` so the state path
starts mostly open. -/
def init (nh : Nat) (seed : UInt64) (scale : Float) : Array Float := Id.run do
  let (p, _) := (Rng.seed seed).uniformArray (nParams nh) scale
  let mut p := p
  for j in [0:nh] do
    p := p.set! (1 * nh * (nh + 2) + j * (nh + 2) + nh + 1) 0.5
  return p

end LeanDL.Gru