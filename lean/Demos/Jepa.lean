import LeanDL.Ch15.Model
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch15

def twoPi : Float := 6.283185307179586

/-- Least squares with a bias term, by the normal equations and Gauss elimination. -/
def lstsq (xs : Array (Array Float)) (ys : Array Float) : Array Float := Id.run do
  let d := xs[0]!.size + 1
  let mut a := Array.replicate d (Array.replicate (d + 1) 0.0)
  for i in [0:xs.size] do
    let f := xs[i]!.push 1.0
    for r in [0:d] do
      for c in [0:d] do
        a := a.modify r (·.modify c (· + f[r]! * f[c]!))
      a := a.modify r (·.modify d (· + f[r]! * ys[i]!))
  for r in [0:d] do
    a := a.modify r (·.modify r (· + 1e-6))
  for col in [0:d] do
    let piv := a[col]![col]!
    for c in [0:d + 1] do
      a := a.modify col (·.modify c (· / piv))
    for r in [0:d] do
      if r != col then
        let f := a[r]![col]!
        for c in [0:d + 1] do
          a := a.modify r (·.modify c (· - f * a[col]![c]!))
  return (Array.range d).map fun r => a[r]![d]!

def predict (w : Array Float) (x : Array Float) : Float :=
  (x.push 1.0).foldl (fun (s, i) v => (s + w[i]! * v, i + 1)) (0.0, 0) |>.1

/-- `R²` of a linear probe fitted on `train` and evaluated on `test`. -/
def probe (train test : Array (Array Float)) (ytrain ytest : Array Float) : Float :=
  let w := lstsq train ytrain
  let m := ytest.foldl (· + ·) 0.0 / ytest.size.toFloat
  let sse := (Array.range test.size).foldl (fun s i => let e := ytest[i]! - predict w test[i]!; s + e * e) 0.0
  let sst := ytest.foldl (fun s y => s + (y - m) * (y - m)) 0.0
  1.0 - sse / sst

def sample (n : Nat) (seed : UInt64) : Array (Float × List Float × Float) := Id.run do
  let mut out := #[]
  let mut r := Rng.seed seed
  for _ in [0:n] do
    let (u, r1) := r.uniform
    let θ := twoPi * u
    let (v, r2) := mkView θ r1
    let (g, r3) := r2.normal
    r := r3
    out := out.push (θ, v, g)
  return out

/-- Embedding statistics and probe `R²` for `cos θ`, `sin θ` and a distractor coordinate. -/
def evaluate (name : String) (p : Array Float) : IO Unit := do
  let train := sample 1500 100
  let test := sample 1500 200
  let embs := fun (d : Array (Float × List Float × Float)) => d.map fun (_, v, _) => embed p v
  let etr := embs train
  let ete := embs test
  let std (k : Nat) : Float :=
    let col := ete.map (·[k]!)
    let m := col.foldl (· + ·) 0.0 / col.size.toFloat
    Float.sqrt (col.foldl (fun s x => s + (x - m) * (x - m)) 0.0 / col.size.toFloat)
  let r2 (f : Float × List Float × Float → Float) :=
    probe etr ete (train.map f) (test.map f)
  let rc := r2 fun (θ, _, _) => Float.cos θ
  let rs := r2 fun (θ, _, _) => Float.sin θ
  let rd := r2 fun (_, v, _) => v.getD 2 0.0 / 3.0
  IO.println s!"  {name}: embedding std ({std 0}, {std 1}); probe R^2: cos {rc}, sin {rs}, distractor {rd}"

def train (mode : String) (steps : Nat) (wv : Float) : IO (Array Float) := do
  let (p0, _) := (Rng.seed 14).uniformArray PJ 0.5
  let mut p := p0
  -- the target encoder starts as a copy of the context encoder
  for i in [0:PE] do
    p := p.set! (PE + PP + i) p[i]!
  let mut st : AdamState Float := AdamState.init PJ
  let mut rng := Rng.seed 15
  let ema := mode == "ema"
  for step in [0:steps] do
    let mut batch : List (List Float × List Float × Float) := []
    for _ in [0:32] do
      let (u, r1) := rng.uniform
      let (dl, r2) := r1.uniform
      let θ := twoPi * u
      let δ := 2.0 * dl - 1.0
      let (c, r3) := mkView θ r2
      let (y, r4) := mkView (θ + δ) r3
      rng := r4
      batch := (c, y, δ) :: batch
    let loss : Expr Float PJ :=
      if mode == "vicreg" then
        .add (predLoss false batch) (regLoss 1.0 wv wv (batch.map (·.1)))
      else predLoss ema batch
    let g := loss.backprop (vecOf p)
    let g := if ema then (Array.range PJ).map fun i => if i < PE + PP then g[i]! else 0.0 else g
    let (p1, st') := adamStep 0.003 0.9 0.999 1e-8 st p g
    p := p1; st := st'
    if ema then
      for i in [0:PE] do
        p := p.set! (PE + PP + i) (0.99 * p[PE + PP + i]! + 0.01 * p[i]!)
    if step % 1000 == 0 then
      IO.println s!"  [{mode}] step {step}: loss {loss.eval (vecOf p)}"
  return p

def main (args : List String) : IO Unit := do
  let steps := (args.getD 0 "3000").toNat!
  let (p0, _) := (Rng.seed 14).uniformArray PJ 0.5
  IO.println "JEPA: context encoder 4-8-2, predictor (embedding, action) 3-8-2, hidden angle with 2 distractors"
  evaluate "untrained encoder        " p0
  for (mode, name, w) in [("naive", "naive (no safeguard)    ", 0.0), ("ema", "EMA target + stop-grad ", 0.0),
      ("vicreg", "variance+cov, weight 1  ", 1.0), ("vicreg", "variance+cov, weight 5  ", 5.0)] do
    let p ← train mode steps w
    evaluate name p
