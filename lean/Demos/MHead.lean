import LeanDL.Core.Rng
import LeanDL.Ch05.Optim

/-!
# Multi-head attention, end to end in Lean

One block: fixed random row codes (so positions are identifiable — the lesson of Chapter 9:
attention alone cannot see order) → h causal attention heads of width dh (Q/K/V projections,
scores / √dh, causal softmax, concatenation) → linear read-out → softmax. The backward pass
is hand-written; the demo checks it against central finite differences and then trains a
copy-the-lag-token task.

The formal properties of the head layout (concatenation loses nothing, slicing round-trips)
are proved in `LeanDL/Ch09/Attention.lean`, section `MultiHead`.
-/

namespace LeanDL.MHead

open LeanDL.Ch05

structure Cfg where
  V : Nat     -- vocabulary size
  h : Nat     -- number of heads
  dh : Nat    -- width of one head

namespace Cfg
def d (c : Cfg) : Nat := c.h * c.dh
def oWq (_c : Cfg) : Nat := 0
def oWk (c : Cfg) : Nat := c.oWq + c.d * c.d
def oWv (c : Cfg) : Nat := c.oWk + c.d * c.d
def oWo (c : Cfg) : Nat := c.oWv + c.d * c.d
def obo (c : Cfg) : Nat := c.oWo + c.V * c.d
def bq (c : Cfg) : Nat := c.obo + c.V
def bk (c : Cfg) : Nat := c.bq + c.d
def bv (c : Cfg) : Nat := c.bk + c.d
def total (c : Cfg) : Nat := c.bv + c.d
end Cfg

def initParams (c : Cfg) (seed : UInt64) : Array Float :=
  (Rng.seed seed).uniformArray c.total (0.8 / Float.sqrt c.d.toFloat) |>.1

/-- Everything the backward pass needs: `T × width` row-major arrays. -/
structure Fwd where
  Q : Array Float   -- T × d
  K : Array Float
  Vv : Array Float
  A : Array Float   -- h × T × T attention weights (zero above the diagonal)
  C : Array Float   -- T × d concatenation of the head outputs
  P : Array Float   -- T × V probabilities

-- ANCHOR: forward
def forward (c : Cfg) (p : Array Float) (emb : Array Float) : Fwd := Id.run do
  let T := emb.size / c.d
  let d := c.d
  let dh := c.dh
  let h := c.h
  let scale := 1.0 / Float.sqrt dh.toFloat
  -- Q, K, V projections (linear with a bias per output coordinate).
  let proj (o bo : Nat) : Array Float := Id.run do
    let mut out := Array.replicate (T * d) 0.0
    for t in [0:T] do
      for k in [0:d] do
        let mut s := p[bo + k]!
        for i in [0:d] do
          s := s + p[o + d * k + i]! * emb[t * d + i]!
        out := out.set! (t * d + k) s
    return out
  let Q := proj c.oWq c.bq
  let K := proj c.oWk c.bk
  let Vv := proj c.oWv c.bv
  -- Causal multi-head attention: head `k` of position `t` looks at positions `j ≤ t`,
  -- each head on its own block of dh coordinates, scores scaled by 1 / √dh.
  let mut A := Array.replicate (h * T * T) 0.0
  let mut C := Array.replicate (T * d) 0.0
  for k in [0:h] do
    for t in [0:T] do
      let mut mx := -1.0e30
      for j in [0:t + 1] do
        let mut s := 0.0
        for a in [0:dh] do
          s := s + Q[t * d + k * dh + a]! * K[j * d + k * dh + a]!
        s := s * scale
        A := A.set! (k * T * T + t * T + j) s
        mx := max mx s
      let mut tot := 0.0
      for j in [0:t + 1] do
        let e := Float.exp (A[k * T * T + t * T + j]! - mx)
        A := A.set! (k * T * T + t * T + j) e
        tot := tot + e
      for j in [0:t + 1] do
        A := A.set! (k * T * T + t * T + j) (A[k * T * T + t * T + j]! / tot)
      for a in [0:dh] do
        let mut o := 0.0
        for j in [0:t + 1] do
          o := o + A[k * T * T + t * T + j]! * Vv[j * d + k * dh + a]!
        C := C.set! (t * d + k * dh + a) o
  -- Read-out and softmax.
  let V := c.V
  let mut P := Array.replicate (T * V) 0.0
  for t in [0:T] do
    let mut mx := -1.0e30
    for v in [0:V] do
      let mut s := p[c.obo + v]!
      for i in [0:d] do
        s := s + p[c.oWo + v * d + i]! * C[t * d + i]!
      P := P.set! (t * V + v) s
      mx := max mx s
    let mut tot := 0.0
    for v in [0:V] do
      let e := Float.exp (P[t * V + v]! - mx)
      P := P.set! (t * V + v) e
      tot := tot + e
    for v in [0:V] do
      P := P.set! (t * V + v) (P[t * V + v]! / tot)
  return ⟨Q, K, Vv, A, C, P⟩
-- ANCHOR_END: forward

/-- Mean cross-entropy over positions with a target (`tg t < V`). -/
def loss (c : Cfg) (p emb : Array Float) (tg : Array Nat) : Float := Id.run do
  let fw := forward c p emb
  let T := emb.size / c.d
  let mut l := 0.0
  let mut n := 0
  for t in [0:T] do
    if tg[t]! < c.V then
      l := l - Float.log fw.P[t * c.V + tg[t]!]!
      n := n + 1
  return l / (max n 1).toFloat

-- ANCHOR: backward
def lossGrad (c : Cfg) (p emb : Array Float) (tg : Array Nat) :
    Float × Array Float × Array Float := Id.run do
  let T := emb.size / c.d
  let d := c.d
  let dh := c.dh
  let h := c.h
  let V := c.V
  let scale := 1.0 / Float.sqrt dh.toFloat
  let fw := forward c p emb
  let mut cnt := 0
  for t in [0:T] do
    if tg[t]! < V then cnt := cnt + 1
  let inv := 1.0 / (max cnt 1).toFloat
  let mut g := Array.replicate c.total 0.0
  let mut gE := Array.replicate emb.size 0.0
  let mut loss := 0.0
  let mut dC := Array.replicate (T * d) 0.0
  -- Read-out: softmax cross-entropy gives `probs - onehot` (Chapter 5).
  for t in [0:T] do
    if tg[t]! < V then
      loss := loss - Float.log fw.P[t * V + tg[t]!]! * inv
      for v in [0:V] do
        let dl := (fw.P[t * V + v]! - (if v == tg[t]! then 1.0 else 0.0)) * inv
        g := g.set! (c.obo + v) (g[c.obo + v]! + dl)
        for i in [0:d] do
          g := g.set! (c.oWo + v * d + i) (g[c.oWo + v * d + i]! + dl * fw.C[t * d + i]!)
          dC := dC.set! (t * d + i) (dC[t * d + i]! + p[c.oWo + v * d + i]! * dl)
  -- Per head: attention output, then the softmax Jacobian on the causal row.
  let mut dQ := Array.replicate (T * d) 0.0
  let mut dK := Array.replicate (T * d) 0.0
  let mut dV := Array.replicate (T * d) 0.0
  for k in [0:h] do
    for t in [0:T] do
      let mut dA := Array.replicate (t + 1) 0.0
      let mut dot := 0.0
      for j in [0:t + 1] do
        let mut s := 0.0
        for a in [0:dh] do
          s := s + dC[t * d + k * dh + a]! * fw.Vv[j * d + k * dh + a]!
          dV := dV.set! (j * d + k * dh + a)
            (dV[j * d + k * dh + a]! + fw.A[k * T * T + t * T + j]! * dC[t * d + k * dh + a]!)
        dA := dA.set! j s
        dot := dot + fw.A[k * T * T + t * T + j]! * s
      for j in [0:t + 1] do
        let ds := fw.A[k * T * T + t * T + j]! * (dA[j]! - dot) * scale
        for a in [0:dh] do
          dQ := dQ.set! (t * d + k * dh + a)
            (dQ[t * d + k * dh + a]! + ds * fw.K[j * d + k * dh + a]!)
          dK := dK.set! (j * d + k * dh + a)
            (dK[j * d + k * dh + a]! + ds * fw.Q[t * d + k * dh + a]!)
  -- Back through the three projections to the row codes.
  for (o, bo, dM) in [(c.oWq, c.bq, dQ), (c.oWk, c.bk, dK), (c.oWv, c.bv, dV)] do
    for t in [0:T] do
      for k in [0:d] do
        let dm := dM[t * d + k]!
        g := g.set! (bo + k) (g[bo + k]! + dm)
        for i in [0:d] do
          g := g.set! (o + d * k + i) (g[o + d * k + i]! + dm * emb[t * d + i]!)
          gE := gE.set! (t * d + i) (gE[t * d + i]! + p[o + d * k + i]! * dm)
  return (loss, g, gE)
-- ANCHOR_END: backward

def argmaxRow (P : Array Float) (t V : Nat) : Nat := Id.run do
  let mut best := 0
  for v in [1:V] do
    if P[t * V + v]! > P[t * V + best]! then best := v
  return best

/-- Fraction of positions with a target on which the arg-max prediction is right. -/
def accuracy (c : Cfg) (p emb : Array Float) (tg : Array Nat) : Float := Id.run do
  let fw := forward c p emb
  let T := emb.size / c.d
  let mut ok := 0
  let mut n := 0
  for t in [0:T] do
    if tg[t]! < c.V then
      n := n + 1
      if argmaxRow fw.P t c.V == tg[t]! then ok := ok + 1
  return ok.toFloat / (max n 1).toFloat

/-- One random sequence of `T` tokens and its lag targets: the target at position `t` is the
token `lag` positions earlier (no target before `lag`, the first `lag` positions are free). -/
def lagTask (r : Rng) (c : Cfg) (T lag : Nat) : Array Nat × Array Nat × Rng := Id.run do
  let mut r := r
  let mut toks := Array.mkEmpty T
  for _ in [0:T] do
    let (u, r') := r.uniform
    r := r'
    toks := toks.push ((u * c.V.toFloat).toUInt64.toNat % c.V)
  let tg := (Array.range T).map fun t => if t ≥ lag then toks[t - lag]! else c.V
  return (toks, tg, r)

/-- Fixed random codes per row: a frozen token embedding (V rows) plus a frozen random
position code per row, so attention can tell positions apart (the lesson of Chapter 9:
attention alone cannot see order). The codes stay frozen during training — the task is
about routing, not vocabulary. -/
def rowCodes (c : Cfg) (toks : Array Nat) (seed : UInt64) : Array Float :=
  let d := c.d
  let nT := toks.size
  let pos := (Rng.seed seed).uniformArray (nT * d) (Float.sqrt (2.0 / d.toFloat)) |>.1
  let tab := (Rng.seed (seed + 1)).uniformArray (c.V * d) (Float.sqrt (2.0 / d.toFloat)) |>.1
  (Array.range (nT * d)).map fun q => pos[q]! + tab[toks[q / d]! * d + q % d]!

/-- Mean accuracy over `n` fresh test sequences from seed `seed`. -/
def testAcc (c : Cfg) (p : Array Float) (seed : UInt64) (T lag n : Nat) : Float := Id.run do
  let mut r := Rng.seed seed
  let mut tot := 0.0
  for _ in [0:n] do
    let (toks, tg, r') := lagTask r c T lag
    r := r'
    tot := tot + accuracy c p (rowCodes c toks 7) tg
  return tot / n.toFloat

def runExp (steps : Nat) (lr : Float) : IO Unit := do
  let c : Cfg := { V := 8, h := 4, dh := 8 }
  let T := 12
  let lag := 3
  let n := 16
  let mut rng := Rng.seed 21
  let mut p := initParams c 11
  let mut st : AdamState Float := AdamState.init c.total
  let report := max 1 (steps / 5)
  for s in [0:steps] do
    let mut g := Array.replicate c.total 0.0
    for _ in [0:n] do
      let (toks, tg, r') := lagTask rng c T lag
      rng := r'
      let gi := (lossGrad c p (rowCodes c toks 7) tg).2.1
      g := (g.zip gi).map fun (a, b) => a + b
    g := g.map (· / n.toFloat)
    let (p', st') := adamStep lr 0.9 0.999 1e-8 st p g
    p := p'; st := st'
    if (s + 1) % report == 0 then
      let acc := testAcc c p 99 T lag 200
      IO.println s!"step {s + 1}: test accuracy = {acc}"
  return ()


end LeanDL.MHead

open LeanDL LeanDL.MHead LeanDL.Ch05

/-- `lake exe mhead`                 gradient check of the multi-head BPTT
`lake exe mhead exp [steps] [lr]`   train the lag-copy task (`lr` in thousandths) -/
def main (args : List String) : IO Unit := do
  if args.head? == some "exp" then
    runExp (args.getD 1 "300").toNat! ((args.getD 2 "10").toNat!.toFloat / 1000.0)
    return
  let c : Cfg := { V := 6, h := 4, dh := 4 }
  let T := 8
  let (toks, tg, _) := lagTask (Rng.seed 3) c T 3
  let emb := rowCodes c toks 7
  let p := initParams c 11
  -- Gradient check of the hand-coded multi-head backward against central finite differences.
  let (_, g, gE) := lossGrad c p emb tg
  let mut worst := 0.0
  for q in [0:c.total] do
    let l (d : Float) := (lossGrad c (p.set! q (p[q]! + d)) emb tg).1
    worst := max worst (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - g[q]!))
  IO.println s!"multi-head gradient check over {c.total} parameters: max error = {worst}"
  let mut worstE := 0.0
  for q in [0:emb.size] do
    let l (d : Float) := (lossGrad c p (emb.set! q (emb[q]! + d)) tg).1
    worstE := max worstE (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - gE[q]!))
  IO.println s!"embedding gradient check over {emb.size} entries: max error = {worstE}"
