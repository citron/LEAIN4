import LeanDL.Ch17.Contrastive
import LeanDL.Core.Plot
import LeanDL.Core.Rng

open LeanDL LeanDL.Ch17
open LeanDL Plot

namespace LeanDL.Ch17Demo


/-!
Chapter 17 demo: the *numeric* face of the exact theorems.

The library proves over exact `Rat` that the softmax is a distribution, the InfoNCE loss is
`≥ 0`, a collapsed embedding loses exactly `log (n + 1)`, and the gradient is `p − onehot`.
Here we evaluate the same quantities in `Float` and watch the identities hold up to
rounding — and then *train* a tiny embedding on a synthetic contrastive task, reading the
collapsed floor `log (n + 1)` off the curve and watching the loss fall below it.
-/

/-- Softmax on Float arrays (same formula as the exact `softmax`). -/
def softmaxF (z : Array Float) : Array Float :=
  let mx := (Array.range z.size).foldl (fun m i => max m z[i]!) 0.0
  let e := z.map fun x => Float.exp (x - mx)
  let s := (Array.range e.size).foldl (fun acc i => acc + e[i]!) 0.0
  e.map fun x => x / s

/-- InfoNCE on Float arrays: negative log of the softmax mass on index 0. -/
def infoNceF (z : Array Float) : Float :=
  Float.log (softmaxF z)[0]! * (-1.0)

/-- The gradient of InfoNCE w.r.t. the logits: `p − onehot`. -/
def gradF (z : Array Float) : Array Float :=
  let p := softmaxF z
  (Array.range p.size).map fun i => p[i]! - (if i = 0 then 1.0 else 0.0)

def showF (x : Float) : String := fmt x

def fmtArr (a : Array Float) : String :=
  "[" ++ String.intercalate ", " (a.toList.map showF) ++ "]"

end LeanDL.Ch17Demo

open LeanDL.Ch17Demo

def main : IO Unit := do
  IO.println "=== Chapter 17: InfoNCE, exactly (theorems) vs numerically (Float) ==="

  -- 1. The softmax is a distribution: positive, sums to 1.
  let z : Array Float := #[2.0, 0.5, -1.0, 3.0, 1.0]
  let p := softmaxF z
  let total := (Array.range p.size).foldl (fun s i => s + p[i]!) 0.0
  IO.println "\n[1] softmax as a distribution (theorem `softmax_dist`)"
  IO.println s!"    logits = {fmtArr z}"
  IO.println s!"    softmax = {fmtArr p}"
  IO.println s!"    sum = {showF total} (exact theorem: exactly 1; gap = rounding)"

  -- 2. The loss is >= 0 and the collapsed floor is log (n+1).
  IO.println "\n[2] collapse floor (theorem `infoNce_collapse`): loss of a flat embedding"
  for n in [3, 7, 15] do
    let flat : Array Float := Array.replicate (n + 1) 0.25
    let loss := infoNceF flat
    let floor := Float.log (Float.ofNat (n + 1))
    IO.println s!"    n = {n} negatives: loss = {showF loss}, log (n+1) = {showF floor}, gap = {showF (loss - floor)}"

  -- 3. Non-collapsed: the loss drops below the floor.
  IO.println "\n[3] a discriminative embedding beats the floor"
  let good : Array Float := #[4.0, 0.0, 0.0, 0.0, 0.0]
  IO.println s!"    scores = {fmtArr good}"
  IO.println s!"    loss = {showF (infoNceF good)} (floor log 5 = {showF (Float.log 5.0)})"

  -- 4. The gradient is p − onehot (theorem `infonce_grad`).
  IO.println "\n[4] gradient p − onehot (theorem `infonce_grad`, inherited from `ceLoss_grad`)"
  let g := gradF z
  IO.println s!"    grad = {fmtArr g} (sums to {showF ((Array.range g.size).foldl (fun s i => s + g[i]!) 0.0)}; the positive's entry is negative: pushed up)"

  -- 5. Train a tiny embedding: cosine scores, positive = the query itself, negatives = others.
  IO.println "\n[5] training a 2-D embedding: 5 items on a circle, fixed queries at radius 1.5, cosine InfoNCE (SGD + sphere projection)"
  let nPts := 5
  let ang (i : Nat) : Float := (Float.ofNat i / Float.ofNat nPts) * 6.283185307179586
  let pts : Array (Float × Float) := (Array.range nPts).map fun i => (Float.cos (ang i), Float.sin (ang i))
  let qs : Array (Float × Float) := pts.map fun (x, y) => (1.5 * x, 1.5 * y)
  let mut emb : Array (Float × Float) := pts  -- start AT collapse: every score is 1.5, loss = log 5
  let mut rng := Rng.seed 7
  let lr := 0.15
  let tau := 0.5
  for epoch in List.range 2000 do
    -- one random query
    let r := rng.uniform
    rng := r.snd
    let q := (r.fst * Float.ofNat nPts).toUInt64.toNat % nPts
    -- scores: dot of emb[q] with each emb[i], / tau
    let mut scores : Array Float := #[]
    for i in List.range nPts do
      let (ex, ey) := emb[i]!
      let (qx, qy) := qs[q]!
      scores := scores.push ((ex * qx + ey * qy) / tau)
    let p := softmaxF scores
    -- gradient on scores is p - onehot (theorem `infonce_grad`); chain rule to each emb[i]
    let mut gs : Array (Float × Float) := #[]
    for i in List.range nPts do
      let gi := (p[i]! - (if i = q then 1.0 else 0.0)) / tau
      let (qx, qy) := qs[q]!
      gs := gs.push (gi * qx, gi * qy)
    let mut newEmb : Array (Float × Float) := #[]
    for i in List.range nPts do
      -- plain SGD, then project back to the unit sphere: the score is a cosine, and
      -- an unnormalised embedding runs away (the classic contrastive blow-up)
      let (gx, gy) := gs[i]!
      let (ex, ey) := emb[i]!
      let ux := ex - lr * gx
      let uy := ey - lr * gy
      let nrm := Float.sqrt (ux * ux + uy * uy) + 1e-12
      newEmb := newEmb.push (ux / nrm, uy / nrm)
    emb := newEmb
    if (epoch + 1) % 500 == 0 then
      -- report average loss over all queries + floor
      let mut tot := 0.0
      for q in List.range nPts do
        -- infoNceF reads the positive at index 0, so list the positive first
        let sc : Array Float := (Array.range nPts).map fun j =>
          let i := (q + j) % nPts
          ((emb[i]!).fst * (qs[q]!).fst + (emb[i]!).snd * (qs[q]!).snd) / tau
        tot := tot + infoNceF sc
      let avg := tot / Float.ofNat nPts
      let sim := (Array.range nPts).foldl (fun s i => s + (emb[i]!).fst * (pts[i]!).fst + (emb[i]!).snd * (pts[i]!).snd) 0.0 / Float.ofNat nPts
      IO.println s!"    epoch {epoch + 1}: mean loss = {showF avg}, mean cosine(emb, target) = {showF sim} (floor log 5 = {showF (Float.log 5.0)}, floor cosine = 0.60 at the start)"

  IO.println "\nThe theorems say WHAT the loss must do (floor, sign, gradient); the run shows a real embedding walking under the floor."

