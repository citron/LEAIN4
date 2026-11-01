import LeanDL.Core.Rng

/-!
# Chapter 9, part 2 — A small causal Transformer, in Lean

One block: token + position embeddings → causal self-attention (one head) with a residual
connection → a ReLU MLP with a residual connection → linear read-out → softmax. The backward
pass is written by hand. (Layer normalisation is proved in `Attention.lean` but not used here:
at this size the network trains fine without it.)

All parameters live in one flat array; `Cfg.total` is its length.
-/

namespace LeanDL.Gpt

structure Cfg where
  V : Nat        -- vocabulary size
  d : Nat        -- model width
  hd : Nat       -- MLP hidden width
  Tmax : Nat     -- longest sequence (number of position embeddings)
  usePos : Bool  -- add position embeddings?

namespace Cfg
def oE (_ : Cfg) : Nat := 0
def oP (c : Cfg) : Nat := c.V * c.d
def oWq (c : Cfg) : Nat := c.oP + c.Tmax * c.d
def oWk (c : Cfg) : Nat := c.oWq + c.d * c.d
def oWv (c : Cfg) : Nat := c.oWk + c.d * c.d
def oW1 (c : Cfg) : Nat := c.oWv + c.d * c.d
def ob1 (c : Cfg) : Nat := c.oW1 + c.hd * c.d
def oW2 (c : Cfg) : Nat := c.ob1 + c.hd
def ob2 (c : Cfg) : Nat := c.oW2 + c.d * c.hd
def oWo (c : Cfg) : Nat := c.ob2 + c.d
def obo (c : Cfg) : Nat := c.oWo + c.V * c.d
def total (c : Cfg) : Nat := c.obo + c.V
end Cfg

def init (c : Cfg) (seed : UInt64) : Array Float :=
  (Rng.seed seed).uniformArray c.total (0.4 / Float.sqrt c.d.toFloat) |>.1

/-- Everything the backward pass needs. Matrices are row-major `T × width`. -/
structure Fwd where
  X : Array Float
  Q : Array Float
  K : Array Float
  Vv : Array Float
  A : Array Float      -- T × T attention weights (zero above the diagonal)
  H : Array Float
  Z : Array Float
  U : Array Float
  Y : Array Float
  P : Array Float      -- T × V probabilities

-- ANCHOR: forward
def forward (c : Cfg) (p : Array Float) (toks : Array Nat) : Fwd := Id.run do
  let T := toks.size
  let d := c.d
  let scale := 1.0 / Float.sqrt d.toFloat
  let mut X := Array.replicate (T * d) 0.0
  for t in [0:T] do
    for k in [0:d] do
      let pos := if c.usePos then p[c.oP + t * d + k]! else 0.0
      X := X.set! (t * d + k) (p[c.oE + toks[t]! * d + k]! + pos)
  let proj (o : Nat) : Array Float := Id.run do
    let mut out := Array.replicate (T * d) 0.0
    for t in [0:T] do
      for k in [0:d] do
        let mut s := 0.0
        for i in [0:d] do
          s := s + p[o + k * d + i]! * X[t * d + i]!
        out := out.set! (t * d + k) s
    return out
  let Q := proj c.oWq
  let K := proj c.oWk
  let Vv := proj c.oWv
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
  let hd := c.hd
  let mut Z := Array.replicate (T * hd) 0.0
  let mut U := Array.replicate (T * hd) 0.0
  let mut Y := H
  for t in [0:T] do
    for m in [0:hd] do
      let mut s := p[c.ob1 + m]!
      for i in [0:d] do
        s := s + p[c.oW1 + m * d + i]! * H[t * d + i]!
      Z := Z.set! (t * hd + m) s
      U := U.set! (t * hd + m) (if 0 < s then s else 0.0)
    for k in [0:d] do
      let mut s := p[c.ob2 + k]!
      for m in [0:hd] do
        s := s + p[c.oW2 + k * hd + m]! * U[t * hd + m]!
      Y := Y.set! (t * d + k) (H[t * d + k]! + s)
  -- Read-out and softmax.
  let V := c.V
  let mut P := Array.replicate (T * V) 0.0
  for t in [0:T] do
    let mut mx := -1.0e30
    for v in [0:V] do
      let mut s := p[c.obo + v]!
      for k in [0:d] do
        s := s + p[c.oWo + v * d + k]! * Y[t * d + k]!
      P := P.set! (t * V + v) s
      mx := max mx s
    let mut tot := 0.0
    for v in [0:V] do
      let e := Float.exp (P[t * V + v]! - mx)
      P := P.set! (t * V + v) e
      tot := tot + e
    for v in [0:V] do
      P := P.set! (t * V + v) (P[t * V + v]! / tot)
  return ⟨X, Q, K, Vv, A, H, Z, U, Y, P⟩
-- ANCHOR_END: forward

/-- Mean cross-entropy over the positions that have a target (`tg t < V`). -/
def loss (c : Cfg) (p : Array Float) (toks tg : Array Nat) : Float := Id.run do
  let fw := forward c p toks
  let mut l := 0.0
  let mut n := 0
  for t in [0:toks.size] do
    if tg[t]! < c.V then
      l := l - Float.log fw.P[t * c.V + tg[t]!]!
      n := n + 1
  return l / (max n 1).toFloat

-- ANCHOR: backward
def lossGrad (c : Cfg) (p : Array Float) (toks tg : Array Nat) : Float × Array Float := Id.run do
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
  let mut dY := Array.replicate (T * d) 0.0
  -- Read-out: softmax cross-entropy gives `probs - onehot` (Chapter 5).
  for t in [0:T] do
    if tg[t]! < V then
      loss := loss - Float.log fw.P[t * V + tg[t]!]! * inv
      for v in [0:V] do
        let dl := (fw.P[t * V + v]! - (if v == tg[t]! then 1.0 else 0.0)) * inv
        g := g.set! (c.obo + v) (g[c.obo + v]! + dl)
        for k in [0:d] do
          g := g.set! (c.oWo + v * d + k) (g[c.oWo + v * d + k]! + dl * fw.Y[t * d + k]!)
          dY := dY.set! (t * d + k) (dY[t * d + k]! + p[c.oWo + v * d + k]! * dl)
  -- MLP and its residual connection.
  let mut dH := dY
  for t in [0:T] do
    for m in [0:hd] do
      let mut du := 0.0
      for k in [0:d] do
        du := du + p[c.oW2 + k * hd + m]! * dY[t * d + k]!
        g := g.set! (c.oW2 + k * hd + m) (g[c.oW2 + k * hd + m]! + dY[t * d + k]! * fw.U[t * hd + m]!)
      let dz := if 0 < fw.Z[t * hd + m]! then du else 0.0
      g := g.set! (c.ob1 + m) (g[c.ob1 + m]! + dz)
      for i in [0:d] do
        g := g.set! (c.oW1 + m * d + i) (g[c.oW1 + m * d + i]! + dz * fw.H[t * d + i]!)
        dH := dH.set! (t * d + i) (dH[t * d + i]! + p[c.oW1 + m * d + i]! * dz)
    for k in [0:d] do
      g := g.set! (c.ob2 + k) (g[c.ob2 + k]! + dY[t * d + k]!)
  -- Attention: `H = X + softmax(Q Kᵀ / √d) V`.
  let mut dX := dH
  let mut dQ := Array.replicate (T * d) 0.0
  let mut dK := Array.replicate (T * d) 0.0
  let mut dV := Array.replicate (T * d) 0.0
  for t in [0:T] do
    -- dA[t, j] = dO[t] · V[j]; the softmax Jacobian then gives dS.
    let mut dA := Array.replicate (t + 1) 0.0
    let mut dot := 0.0
    for j in [0:t + 1] do
      let mut s := 0.0
      for k in [0:d] do
        s := s + dH[t * d + k]! * fw.Vv[j * d + k]!
        dV := dV.set! (j * d + k) (dV[j * d + k]! + fw.A[t * T + j]! * dH[t * d + k]!)
      dA := dA.set! j s
      dot := dot + fw.A[t * T + j]! * s
    for j in [0:t + 1] do
      let ds := fw.A[t * T + j]! * (dA[j]! - dot) * scale
      for k in [0:d] do
        dQ := dQ.set! (t * d + k) (dQ[t * d + k]! + ds * fw.K[j * d + k]!)
        dK := dK.set! (j * d + k) (dK[j * d + k]! + ds * fw.Q[t * d + k]!)
  -- Back through the three projections to the embeddings.
  for (o, dM) in [(c.oWq, dQ), (c.oWk, dK), (c.oWv, dV)] do
    for t in [0:T] do
      for k in [0:d] do
        let dm := dM[t * d + k]!
        for i in [0:d] do
          g := g.set! (o + k * d + i) (g[o + k * d + i]! + dm * fw.X[t * d + i]!)
          dX := dX.set! (t * d + i) (dX[t * d + i]! + p[o + k * d + i]! * dm)
  for t in [0:T] do
    for k in [0:d] do
      g := g.set! (c.oE + toks[t]! * d + k) (g[c.oE + toks[t]! * d + k]! + dX[t * d + k]!)
      if c.usePos then
        g := g.set! (c.oP + t * d + k) (g[c.oP + t * d + k]! + dX[t * d + k]!)
  return (loss, g)
-- ANCHOR_END: backward

def argmaxRow (P : Array Float) (t V : Nat) : Nat := Id.run do
  let mut best := 0
  for v in [1:V] do
    if P[t * V + v]! > P[t * V + best]! then best := v
  return best

/-- Fraction of positions with a target on which the arg-max prediction is right. -/
def accuracy (c : Cfg) (p : Array Float) (data : Array (Array Nat × Array Nat)) : Float := Id.run do
  let mut ok := 0
  let mut n := 0
  for (toks, tg) in data do
    let fw := forward c p toks
    for t in [0:toks.size] do
      if tg[t]! < c.V then
        n := n + 1
        if argmaxRow fw.P t c.V == tg[t]! then ok := ok + 1
  return ok.toFloat / (max n 1).toFloat

/-- Random tokens; the target at position `t` is the token `lag` positions earlier. -/
def delayTask (r : Rng) (c : Cfg) (T lag n : Nat) : Array (Array Nat × Array Nat) × Rng := Id.run do
  let mut r := r
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let mut toks := Array.mkEmpty T
    for _ in [0:T] do
      let (u, r') := r.uniform
      r := r'
      toks := toks.push ((u * c.V.toFloat).toUInt64.toNat % c.V)
    let tg := (Array.range T).map fun t => if t ≥ lag then toks[t - lag]! else c.V
    out := out.push (toks, tg)
  return (out, r)

end LeanDL.Gpt
