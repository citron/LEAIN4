import LeanDL.Ch12.Model
import LeanDL.Ch05.Optim
import LeanDL.Core.Plot

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch12

def realSample (r : Rng) : Float × Rng :=
  let (g, r) := r.normal
  let (u, r) := r.uniform
  ((if u < 0.5 then -2.0 else 2.0) + 0.4 * g, r)

def histTv (a b : Array Float) : Float := Id.run do
  let hist (v : Array Float) : Array Float := Id.run do
    let mut h := Array.replicate 16 0.0
    for x in v do
      let i := min 15 (max 0 (Float.floor ((x + 4.0) / 8.0 * 16.0)).toUInt64.toNat)
      h := h.set! i (h[i]! + 1.0 / v.size.toFloat)
    return h
  let ha := hist a
  let hb := hist b
  return 0.5 * (Array.range 16).foldl (fun s i => s + Float.abs (ha[i]! - hb[i]!)) 0.0

def stats (v : Array Float) : Float × Float :=
  let m := v.foldl (· + ·) 0.0 / v.size.toFloat
  (m, Float.sqrt (v.foldl (fun s x => s + (x - m) * (x - m)) 0.0 / v.size.toFloat))

/-- Ancestral (DDPM) sampling: stochastic reverse steps. -/
def ddpm (p : Array Float) (r : Rng) : Float × Rng := Id.run do
  let (x0, r0) := r.normal
  let mut x := x0
  let mut rng := r0
  for k in [0:T] do
    let t := T - k                      -- t = T, …, 1
    let b := betas[t - 1]!
    let ab := abars[t]!
    let e := (epsNet x (t.toFloat / T.toFloat)).eval (vecOf p)
    x := (x - b / Float.sqrt (1.0 - ab) * e) / Float.sqrt (1.0 - b)
    if t > 1 then
      let (z, r2) := rng.normal
      rng := r2
      x := x + Float.sqrt b * z
  return (x, rng)

/-- Deterministic (DDIM) sampling: the `ddimStep` of `Ch12/Diffusion.lean`, in Float. -/
def ddim (p : Array Float) (r : Rng) : Float × Rng := Id.run do
  let (x0, r0) := r.normal
  let mut x := x0
  for k in [0:T] do
    let t := T - k
    let abT := Float.sqrt abars[t]!
    let sgT := Float.sqrt (1.0 - abars[t]!)
    let abS := Float.sqrt abars[t - 1]!
    let sgS := Float.sqrt (1.0 - abars[t - 1]!)
    let e := (epsNet x (t.toFloat / T.toFloat)).eval (vecOf p)
    x := abS * ((x - sgT * e) / abT) + sgS * e
  return (x, r0)

def report (name : String) (sampler : Array Float → Rng → Float × Rng) (p : Array Float)
    (real : Array Float) : IO (Array Float) := do
  let mut out : Array Float := #[]
  let mut r := Rng.seed 77
  for _ in [0:2000] do
    let (x, r2) := sampler p r
    r := r2
    out := out.push x
  let (m, s) := stats out
  let gap := (out.filter (fun x => Float.abs x < 1.0)).size.toFloat / out.size.toFloat
  IO.println s!"  {name}: mean {m}, std {s}, mass in |x|<1: {gap}, histogram TV {histTv out real}"
  return out

def main (args : List String) : IO Unit := do
  let steps := (args.getD 0 "5000").toNat!
  let (p0, _) := (Rng.seed 5).uniformArray PD 0.5
  let mut p := p0
  let mut st : AdamState Float := AdamState.init PD
  let mut rng := Rng.seed 21
  IO.println s!"diffusion: {T} noising steps, {steps} Adam steps, {PD} parameters"
  IO.println s!"  final signal factor sqrt(abar_T) = {Float.sqrt abars[T]!}"
  for step in [0:steps] do
    let mut batch : List (Float × Float × Float) := []
    for _ in [0:32] do
      let (x0, r1) := realSample rng
      let (u, r2) := r1.uniform
      let (e, r3) := r2.normal
      rng := r3
      let t := 1 + (min (T - 1) (Float.floor (u * T.toFloat)).toUInt64.toNat)
      let ab := abars[t]!
      let xt := Float.sqrt ab * x0 + Float.sqrt (1.0 - ab) * e
      batch := (xt, t.toFloat / T.toFloat, e) :: batch
    let loss := denoiseLoss batch
    let g := loss.backprop (vecOf p)
    let (p1, st') := adamStep 0.003 0.9 0.999 1e-8 st p g
    p := p1; st := st'
    if step % 1000 == 0 then
      IO.println s!"  step {step}: loss {loss.eval (vecOf p)}"
  let mut real : Array Float := #[]
  let mut r := Rng.seed 99
  for _ in [0:2000] do
    let (x, r2) := realSample r
    r := r2
    real := real.push x
  let (mr, sr) := stats real
  IO.println s!"  data: mean {mr}, std {sr}, mass in |x|<1: {(real.filter (fun x => Float.abs x < 1.0)).size.toFloat / 2000.0}"
  IO.println s!"  (reference: two halves of the data differ by TV {histTv (real.extract 0 1000) (real.extract 1000 2000)})"
  let a ← report "DDPM (stochastic)" ddpm p real
  let b ← report "DDIM (deterministic)" ddim p real
  IO.FS.writeFile "../website/static/img/diffusion.svg"
    (Plot.histSvg 400 160 (-4.0) 4.0 16 "Data against the diffusion model's samples"
      [("data", "#999", real), ("DDPM", "#2e5aa8", a), ("DDIM", "#c4561a", b)])
