import LeanDL.Ch11.Model
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch11

/-- Total-variation distance between two samples' histograms over `[-4, 4]` (16 bins). -/
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

def run (mixture : Bool) (steps : Nat) : IO (Array Float × Array Float) := do
  let (p0, _) := (Rng.seed 6).uniformArray P 0.5
  let mut p := p0
  let mut stD : AdamState Float := AdamState.init P
  let mut stG : AdamState Float := AdamState.init P
  let mut rng := Rng.seed 12
  let gEnd := 3 * H + 1
  for step in [0:steps] do
    -- One discriminator step, then one generator step, on fresh data and noise.
    let mut reals : List Float := []
    let mut noises : List Float := []
    for _ in [0:32] do
      let (x, r1) := realSample mixture rng
      let (z, r2) := r1.normal
      rng := r2
      reals := x :: reals
      noises := z :: noises
    let gD := (discLoss reals noises).backprop (vecOf p)
    let gD := (Array.range P).map fun i => if i < gEnd then 0.0 else gD[i]!
    let (p1, stD') := adamStep 0.005 0.5 0.999 1e-8 stD p gD
    p := p1; stD := stD'
    let mut noises2 : List Float := []
    for _ in [0:32] do
      let (z, r2) := rng.normal
      rng := r2
      noises2 := z :: noises2
    let gG := (genLoss noises2).backprop (vecOf p)
    let gG := (Array.range P).map fun i => if i < gEnd then gG[i]! else 0.0
    let (p2, stG') := adamStep 0.005 0.5 0.999 1e-8 stG p gG
    p := p2; stG := stG'
    if step % 1000 == 0 then
      IO.println s!"  step {step}: D loss {(discLoss reals noises).eval (vecOf p)}, G loss {(genLoss noises2).eval (vecOf p)}"
  -- Compare 2000 generated and 2000 real samples.
  let mut gen : Array Float := #[]
  let mut real : Array Float := #[]
  let mut r := Rng.seed 99
  for _ in [0:2000] do
    let (z, r1) := r.normal
    let (x, r2) := realSample mixture r1
    r := r2
    gen := gen.push (generate p z)
    real := real.push x
  return (gen, real)

def main (args : List String) : IO Unit := do
  let steps := (args.getD 0 "6000").toNat!
  let mut series : List (String × String × Array Float) := []
  for (name, mixture) in [("single Gaussian N(2, 0.5²)", false), ("two Gaussians at ±2", true)] do
    IO.println s!"{name}: {steps} steps"
    let (gen, real) ← run mixture steps
    let (mg, sg) := stats gen
    let (mr, sr) := stats real
    IO.println s!"  data: mean {mr}, std {sr}   generated: mean {mg}, std {sg}   histogram TV {histTv gen real}"
    IO.println s!"  (reference: two halves of the real data differ by TV {histTv (real.extract 0 1000) (real.extract 1000 2000)})"
    let between (v : Array Float) := (v.filter (fun x => Float.abs x < 1.0)).size.toFloat / v.size.toFloat
    IO.println s!"  mass in |x| < 1: data {between real}, generated {between gen}"
    if mixture then
      series := [("data", "#999", real), ("GAN", "#2e5aa8", gen)]
  IO.FS.writeFile "../website/static/img/gan.svg"
    (Plot.histSvg 400 160 (-4.0) 4.0 16 "Two-Gaussian data against the GAN's samples" series)
