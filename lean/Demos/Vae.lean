import LeanDL.Ch10.Model
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch10

/-- Train for `steps` Adam steps on batches of 16 fresh points; `beta = 0` gives a plain
autoencoder, `beta = 1` the VAE. Returns the parameters. -/
def train (beta : Float) (steps : Nat) : IO (Array Float) := do
  let (p0, _) := (Rng.seed 4).uniformArray P 0.5
  let mut p := p0
  let mut st : AdamState Float := AdamState.init P
  let mut rng := Rng.seed 9
  for step in [0:steps] do
    let (batch, r1) := arcData rng 16
    rng := r1
    let mut terms : List (Expr Float P) := []
    for (x1, x2) in batch do
      let (e, r2) := rng.normal
      rng := r2
      terms := sampleLoss beta x1 x2 e :: terms
    let loss : Expr Float P := .mul (.const (1.0 / 16.0)) (Expr.sum terms)
    let g := loss.backprop (vecOf p)
    let (p', st') := adamStep 0.01 0.9 0.999 1e-8 st p g
    p := p'; st := st'
    if step % 500 == 0 || step + 1 == steps then
      IO.println s!"  step {step}: batch loss {loss.eval (vecOf p)}"
  return p

/-- Radius statistics of
` decodings of prior samples `z ~ N(0, 1)`. -/
def generate (p : Array Float) (n : Nat) : Array (Float × Float) × Float × Float × Float := Id.run do
  let mut r := Rng.seed 31
  let mut pts := Array.mkEmpty n
  for _ in [0:n] do
    let (z, r') := r.normal
    r := r'
    pts := pts.push (decode p z)
  let radii := pts.map fun (a, b) => Float.sqrt (a * a + b * b)
  let mean := radii.foldl (· + ·) 0.0 / n.toFloat
  let var := radii.foldl (fun s x => s + (x - mean) * (x - mean)) 0.0 / n.toFloat
  let near := ((pts.zip radii).filter fun (q, x) => Float.abs (x - 1.0) < 0.15 && q.2 > -0.1).size.toFloat / n.toFloat
  return (pts, mean, Float.sqrt var, near)

/-- Total-variation distance between the distribution of angles of `pts` (6 bins over
`[0, π]`) and the uniform distribution that the data follows. -/
def angleTv (pts : Array (Float × Float)) : Float := Id.run do
  let mut h := Array.replicate 6 0.0
  for (a, b) in pts do
    let ang := Float.atan2 b a
    let i := min 5 (max 0 (Float.floor (ang / 3.141592653589793 * 6.0)).toUInt64.toNat)
    h := h.set! i (h[i]! + 1.0)
  return 0.5 * h.foldl (fun s c => s + Float.abs (c / pts.size.toFloat - 1.0 / 6.0)) 0.0
def main (args : List String) : IO Unit := do
  let steps := (args.getD 0 "2000").toNat!
  let (test, _) := arcData (Rng.seed 77) 200
  IO.println s!"data itself (sampling noise floor): TV {angleTv test}"
  let mut svgSeries : List (String × String × Array (Float × Float)) := [("data", "#999", test)]
  for (name, beta, color) in [("autoencoder", 0.0, "#d9534f"), ("VAE", 1.0, "#2e5aa8")] do
    IO.println s!"{name} (β = {beta}), {steps} steps:"
    let p ← train beta steps
    let mut recErr := 0.0
    let mut kl := 0.0
    for (x1, x2) in test do
      let (mu, lv) := encode p x1 x2
      let (a, b) := decode p mu
      recErr := recErr + (a - x1) * (a - x1) + (b - x2) * (b - x2)
      kl := kl + 0.5 * (mu * mu + Float.exp lv - 1.0 - lv)
    let (pts, mean, sd, near) := generate p 400
    IO.println s!"  test reconstruction error {recErr / 200.0}, mean KL {kl / 200.0}"
    IO.println s!"  decoded N(0,1) samples: radius {mean} ± {sd}, {near * 100.0}% on the arc (radius within 0.15, y ≥ -0.1)"
    IO.println s!"  angle-distribution distance to uniform (TV): {angleTv pts}"
    if name == "VAE" then
      svgSeries := svgSeries ++ [("VAE samples", color, pts)]
  IO.FS.writeFile "../website/static/img/vae.svg"
    (Plot.scatterSvg 360 (-1.6) 1.6 "Decoded samples z ~ N(0,1) against the data" svgSeries)
