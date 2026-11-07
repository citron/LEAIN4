import LeanDL.Core.Rng

/-!
# Chapter 9, part 3 — A stack of causal Transformer blocks, in Lean

The single block of `Gpt.lean`, replicated `nLayer` times: token + position embeddings →
`nLayer` blocks of (causal one-head self-attention with a residual connection, then a ReLU
MLP with a residual connection) → linear read-out → softmax. The backward pass is written
by hand: the read-out gradient is computed first, then the blocks are walked in reverse,
each block propagating its input gradient to the block below while accumulating its own
parameter gradients.

All parameters live in one flat array; `CfgN.total` is its length. Layer normalisation is
proved in `Attention.lean` but not used here (same as `Gpt.lean`): at this size the
network trains fine without it.
-/

namespace LeanDL.GptN

structure CfgN where
  V : Nat        -- vocabulary size
  d : Nat        -- model width
  hd : Nat       -- MLP hidden width
  Tmax : Nat     -- longest sequence (number of position embeddings)
  usePos : Bool  -- add position embeddings?
  nLayer : Nat   -- number of stacked transformer blocks

namespace CfgN
def oE (_ : CfgN) : Nat := 0
def oP (c : CfgN) : Nat := c.V * c.d
/-- Parameters of one block: Wq, Wk, Wv (each d×d), W1 (hd×d), b1 (hd), W2 (d×hd), b2 (d). -/
def blk (c : CfgN) : Nat :=
  3 * (c.d * c.d) + c.hd * c.d + c.hd + c.d * c.hd + c.d
def oWq (c : CfgN) (L : Nat) : Nat := c.oP + c.Tmax * c.d + L * c.blk
def oWk (c : CfgN) (L : Nat) : Nat := c.oWq L + c.d * c.d
def oWv (c : CfgN) (L : Nat) : Nat := c.oWk L + c.d * c.d
def oW1 (c : CfgN) (L : Nat) : Nat := c.oWv L + c.d * c.d
def ob1 (c : CfgN) (L : Nat) : Nat := c.oW1 L + c.hd * c.d
def oW2 (c : CfgN) (L : Nat) : Nat := c.ob1 L + c.hd
def ob2 (c : CfgN) (L : Nat) : Nat := c.oW2 L + c.d * c.hd
def oWo (c : CfgN) : Nat := c.oP + c.Tmax * c.d + c.nLayer * c.blk
def obo (c : CfgN) : Nat := c.oWo + c.V * c.d
def total (c : CfgN) : Nat := c.obo + c.V
end CfgN

def init (c : CfgN) (seed : UInt64) : Array Float :=
  (Rng.seed seed).uniformArray c.total (0.4 / Float.sqrt c.d.toFloat) |>.1

/-- Everything the backward pass needs. Matrices are row-major `T × width`; the `*s`
arrays have one entry per block, `Xs L` being the input of block `L`
(`Xs c.nLayer` is the output of the last block, feeding the read-out). -/
structure FwdN where
  Xs : Array (Array Float)
  Qs : Array (Array Float)
  Ks : Array (Array Float)
  Vs : Array (Array Float)
  As : Array (Array Float)   -- T × T attention weights (zero above the diagonal)
  Hs : Array (Array Float)
  Zs : Array (Array Float)
  Us : Array (Array Float)
  P : Array Float            -- T × V probabilities

def forward (c : CfgN) (p : Array Float) (toks : Array Nat) : FwdN := Id.run do
  let T := toks.size
  let d := c.d
  let hd := c.hd
  let scale := 1.0 / Float.sqrt d.toFloat
  let mut X := Array.replicate (T * d) 0.0
  for t in [0:T] do
    for k in [0:d] do
      let pos := if c.usePos then p[c.oP + t * d + k]! else 0.0
      X := X.set! (t * d + k) (p[c.oE + toks[t]! * d + k]! + pos)
  let proj (o : Nat) (src : Array Float) : Array Float := Id.run do
    let mut out := Array.replicate (T * d) 0.0
    for t in [0:T] do
      for k in [0:d] do
        let mut s := 0.0
        for i in [0:d] do
          s := s + p[o + k * d + i]! * src[t * d + i]!
        out := out.set! (t * d + k) s
    return out
  let mut Xs := Array.mkEmpty (c.nLayer + 1)
  let mut Qs := Array.mkEmpty c.nLayer
  let mut Ks := Array.mkEmpty c.nLayer
  let mut Vs := Array.mkEmpty c.nLayer
  let mut As := Array.mkEmpty c.nLayer
  let mut Hs := Array.mkEmpty c.nLayer
  let mut Zs := Array.mkEmpty c.nLayer
  let mut Us := Array.mkEmpty c.nLayer
  Xs := Xs.push X
  for L in [0:c.nLayer] do
    let Q := proj (c.oWq L) X
    let K := proj (c.oWk L) X
    let Vv := proj (c.oWv L) X
    -- Causal attention: position `t` only looks at positions `j ≤ t`.
    let mut A := Array.replicate (T * T) 0.0
    let mut H := X
    for t in [0:T] do
      let mut mx := -1.0e30
      for j in [0:t + 1] do
        let mut s := 0.0
        for k in [0:d] do
          s := s + Q[t * d + k]! * K[j * d + k]!
        s := s * scale
        A := A.set! (t * T + j) s
        mx := max mx s
      let mut tot := 0.0
      for j in [0:t + 1] do
        let e := Float.exp (A[t * T + j]! - mx)
        A := A.set! (t * T + j) e
        tot := tot + e
      for j in [0:t + 1] do
        A := A.set! (t * T + j) (A[t * T + j]! / tot)
      for k in [0:d] do
        let mut o := 0.0
        for j in [0:t + 1] do
          o := o + A[t * T + j]! * Vv[j * d + k]!
        H := H.set! (t * d + k) (X[t * d + k]! + o)
    -- MLP with a residual connection.
    let mut Z := Array.replicate (T * hd) 0.0
    let mut U := Array.replicate (T * hd) 0.0
    let mut Y := H
    for t in [0:T] do
      for m in [0:hd] do
        let mut s := p[c.ob1 L + m]!
        for i in [0:d] do
          s := s + p[c.oW1 L + m * d + i]! * H[t * d + i]!
        Z := Z.set! (t * hd + m) s
        U := U.set! (t * hd + m) (if 0 < s then s else 0.0)
      for k in [0:d] do
        let mut s := p[c.ob2 L + k]!
        for m in [0:hd] do
          s := s + p[c.oW2 L + k * hd + m]! * U[t * hd + m]!
        Y := Y.set! (t * d + k) (H[t * d + k]! + s)
    Xs := Xs.push Y
    Qs := Qs.push Q
    Ks := Ks.push K
    Vs := Vs.push Vv
    As := As.push A
    Hs := Hs.push H
    Zs := Zs.push Z
    Us := Us.push U
    X := Y
  -- Read-out and softmax.
  let V := c.V
  let mut P := Array.replicate (T * V) 0.0
  for t in [0:T] do
    let mut mx := -1.0e30
    for v in [0:V] do
      let mut s := p[c.obo + v]!
      for k in [0:d] do
        s := s + p[c.oWo + v * d + k]! * X[t * d + k]!
      P := P.set! (t * V + v) s
      mx := max mx s
    let mut tot := 0.0
    for v in [0:V] do
      let e := Float.exp (P[t * V + v]! - mx)
      P := P.set! (t * V + v) e
      tot := tot + e
    for v in [0:V] do
      P := P.set! (t * V + v) (P[t * V + v]! / tot)
  return ⟨Xs, Qs, Ks, Vs, As, Hs, Zs, Us, P⟩

/-- Mean cross-entropy over the positions that have a target (`tg t < V`). -/
def loss (c : CfgN) (p : Array Float) (toks tg : Array Nat) : Float := Id.run do
  let fw := forward c p toks
  let mut l := 0.0
  let mut n := 0
  for t in [0:toks.size] do
    if tg[t]! < c.V then
      l := l - Float.log fw.P[t * c.V + tg[t]!]!
      n := n + 1
  return l / (max n 1).toFloat

def lossGrad (c : CfgN) (p : Array Float) (toks tg : Array Nat) : Float × Array Float := Id.run do
  let T := toks.size
  let d := c.d
  let hd := c.hd
  let V := c.V
  let scale := 1.0 / Float.sqrt d.toFloat
  let fw := forward c p toks
  let mut cnt := 0
  for t in [0:T] do
    if tg[t]! < V then cnt := cnt + 1
  let inv := 1.0 / (max cnt 1).toFloat
  let mut g := Array.replicate c.total 0.0
  let mut loss := 0.0
  let mut dX := Array.replicate (T * d) 0.0
  -- Read-out: softmax cross-entropy gives `probs - onehot` (Chapter 5).
  let Y := fw.Xs[c.nLayer]!
  for t in [0:T] do
    if tg[t]! < V then
      loss := loss - Float.log fw.P[t * V + tg[t]!]! * inv
      for v in [0:V] do
        let dl := (fw.P[t * V + v]! - (if v == tg[t]! then 1.0 else 0.0)) * inv
        g := g.set! (c.obo + v) (g[c.obo + v]! + dl)
        for k in [0:d] do
          g := g.set! (c.oWo + v * d + k) (g[c.oWo + v * d + k]! + dl * Y[t * d + k]!)
          dX := dX.set! (t * d + k) (dX[t * d + k]! + p[c.oWo + v * d + k]! * dl)
  -- Walk the blocks in reverse: `dX` is the gradient with respect to the block output.
  for b in [0:c.nLayer] do
    let L := c.nLayer - 1 - b
    let X := fw.Xs[L]!
    let H := fw.Hs[L]!
    let Z := fw.Zs[L]!
    let U := fw.Us[L]!
    -- MLP and its residual connection.
    let mut dH := dX
    for t in [0:T] do
      for m in [0:hd] do
        let mut du := 0.0
        for k in [0:d] do
          du := du + p[c.oW2 L + k * hd + m]! * dX[t * d + k]!
          g := g.set! (c.oW2 L + k * hd + m) (g[c.oW2 L + k * hd + m]! + dX[t * d + k]! * U[t * hd + m]!)
        let dz := if 0 < Z[t * hd + m]! then du else 0.0
        g := g.set! (c.ob1 L + m) (g[c.ob1 L + m]! + dz)
        for i in [0:d] do
          g := g.set! (c.oW1 L + m * d + i) (g[c.oW1 L + m * d + i]! + dz * H[t * d + i]!)
          dH := dH.set! (t * d + i) (dH[t * d + i]! + p[c.oW1 L + m * d + i]! * dz)
      for k in [0:d] do
        g := g.set! (c.ob2 L + k) (g[c.ob2 L + k]! + dX[t * d + k]!)
    -- Attention: `H = X + softmax(Q Kᵀ / √d) V`.
    let mut dXi := dH
    let mut dQ := Array.replicate (T * d) 0.0
    let mut dK := Array.replicate (T * d) 0.0
    let mut dV := Array.replicate (T * d) 0.0
    let A := fw.As[L]!
    let Vv := fw.Vs[L]!
    let Q := fw.Qs[L]!
    let K := fw.Ks[L]!
    for t in [0:T] do
      -- dA[t, j] = dH[t] · V[j]; the softmax Jacobian then gives dS.
      let mut dA := Array.replicate (t + 1) 0.0
      let mut dot := 0.0
      for j in [0:t + 1] do
        let mut s := 0.0
        for k in [0:d] do
          s := s + dH[t * d + k]! * Vv[j * d + k]!
          dV := dV.set! (j * d + k) (dV[j * d + k]! + A[t * T + j]! * dH[t * d + k]!)
        dA := dA.set! j s
        dot := dot + A[t * T + j]! * s
      for j in [0:t + 1] do
        let ds := A[t * T + j]! * (dA[j]! - dot) * scale
        for k in [0:d] do
          dQ := dQ.set! (t * d + k) (dQ[t * d + k]! + ds * K[j * d + k]!)
          dK := dK.set! (j * d + k) (dK[j * d + k]! + ds * Q[t * d + k]!)
    -- Back through the three projections to the block input.
    for (o, dM) in [(c.oWq L, dQ), (c.oWk L, dK), (c.oWv L, dV)] do
      for t in [0:T] do
        for k in [0:d] do
          let dm := dM[t * d + k]!
          for i in [0:d] do
            g := g.set! (o + k * d + i) (g[o + k * d + i]! + dm * X[t * d + i]!)
            dXi := dXi.set! (t * d + i) (dXi[t * d + i]! + p[o + k * d + i]! * dm)
    dX := dXi
  -- Embeddings (shared by all blocks through the first block's input).
  for t in [0:T] do
    for k in [0:d] do
      g := g.set! (c.oE + toks[t]! * d + k) (g[c.oE + toks[t]! * d + k]! + dX[t * d + k]!)
      if c.usePos then
        g := g.set! (c.oP + t * d + k) (g[c.oP + t * d + k]! + dX[t * d + k]!)
  return (loss, g)

def argmaxRow (P : Array Float) (t V : Nat) : Nat := Id.run do
  let mut best := 0
  for v in [1:V] do
    if P[t * V + v]! > P[t * V + best]! then best := v
  return best

/-- Fraction of positions with a target on which the arg-max prediction is right. -/
def accuracy (c : CfgN) (p : Array Float) (data : Array (Array Nat × Array Nat)) : Float := Id.run do
  let mut ok := 0
  let mut n := 0
  for (toks, tg) in data do
    let fw := forward c p toks
    for t in [0:toks.size] do
      if tg[t]! < c.V then
        n := n + 1
        if argmaxRow fw.P t c.V == tg[t]! then ok := ok + 1
  return ok.toFloat / (max n 1).toFloat

end LeanDL.GptN
