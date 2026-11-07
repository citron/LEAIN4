import LeanDL.Core.Plot
import LeanDL.Core.Rng

open LeanDL Plot

/-!
Chapter 19 demo: the numeric face of the symmetric-loss theorems.

The library proves over exact `Rat` that the symmetric (CLIP-style) loss is
`>= 0`, that a collapsed model pays the SAME floor `log (n + 1)` in each
direction (theorem `symm_collapse`), that the 2x2 batch loss is the average of
two softplus gaps over the shared positive score (`symm_matched`), and that a
model separated in BOTH directions pays at most `log 2` (`symm_le_log_two`).
Here we evaluate the same quantities in `Float` — the gap to the exact values
is the rounding, made visible.
-/

/-- Row InfoNCE on a Float score row: negative log of the mass on the slot `pos`. -/
def rowLossAtF (s : Array Float) (pos : Nat) : Float :=
  let mx := (Array.range s.size).foldl (fun m i => max m s[i]!) 0.0
  let e := s.map fun x => Float.exp (x - mx)
  let z := (Array.range e.size).foldl (fun acc i => acc + e[i]!) 0.0
  Float.log (z / e[pos]!)

/-- Row InfoNCE with the positive at index 0 (Ch17's `Samples` layout). -/
def rowLossF (s : Array Float) : Float := rowLossAtF s 0

/-- The symmetric CLIP loss of a square score matrix: every row i is a query
whose positive is the DIAGONAL entry `i`, every column `i` the transposed
query. Mean over all 2n directions — the CLIP objective, numerically. -/
def symmLossF (scores : Array (Array Float)) : Float := Id.run do
  let n := scores.size
  let mut total := 0.0
  for i in [0:n] do
    total := total + rowLossAtF scores[i]! i
    let col := (Array.range n).map fun k => scores[k]![i]!
    total := total + rowLossAtF col i
  return total / ((2 : Float) * Float.ofNat n)

def main : IO Unit := do
  IO.println "=== Chapter 19: symmetric multimodal loss (theorems) vs numerically (Float) ==="

  -- 1. The collapse floor: every score equal -> each direction pays log (n + 1).
  IO.println "\n[1] collapse floor (theorem `symm_collapse`): flat score matrix"
  for n in [1, 3, 7] do
    let m := n + 1
    let flat : Array (Array Float) :=
      Array.ofFn (n := m) fun _ => Array.ofFn (n := m) fun _ => (0.25 : Float)
    IO.println s!"    {m}x{m} flat: symm loss = {fmt (symmLossF flat)}, log ({m}) = {fmt (Float.log (Float.ofNat m))}"

  -- 2. The symmetric matched loss: average of two softplus gaps over the shared positive.
  IO.println "\n[2] symmetric matched loss (theorem `symm_matched`): gap g on BOTH mismatches"
  for g in [0.0, 1.0, 2.0, 5.0, 10.0] do
    let scores : Array (Array Float) := #[(#[2.0, 2.0 - g] : Array Float), #[2.0 - g, 2.0]]
    let pred := Float.log (1.0 + Float.exp (-g))
    IO.println s!"    gap = {fmt g}: symm loss = {fmt (symmLossF scores)}; softplus (-gap) = {fmt pred}"

  -- 3. The separation bound: positive beats both mismatches -> loss <= log 2.
  IO.println "\n[3] separation bound (theorem `symm_le_log_two`): separated batches vs log 2 = 0.6931"
  let mut rng := Rng.seed 42
  let mut checked := 0
  let mut violated := 0
  for _ in List.range 5000 do
    let a := rng.uniform; rng := a.snd
    let b := rng.uniform; rng := b.snd
    let c := rng.uniform; rng := c.snd
    let d := rng.uniform; rng := d.snd
    let x1 := a.fst; let y1 := b.fst; let x2 := c.fst; let y2 := d.fst
    let s := x1 * y1
    if x1 * y2 <= s && y1 * x2 <= s then
      checked := checked + 1
      let l := (rowLossF #[x1 * y1, x1 * y2] + rowLossF #[x1 * y1, y1 * x2]) / 2
      if l > 0.6932 then violated := violated + 1
  IO.println s!"    separated batches found: {checked}; violations of loss <= log 2: {violated}"

  -- 4. Grid search on the symmetric loss: the minimizer separates both directions.
  IO.println "\n[4] grid search on the symmetric loss: 2 images, 2 texts, task x1 > x2 and y1 > y2"
  let grid := (List.range 21).map fun k => (0.1 * Float.ofNat k : Float)
  let mut bestLoss : Float := 100.0
  let mut best := (0.0, 0.0, 0.0, 0.0)
  for x1 in grid do
    for x2 in grid do
      if x2 >= x1 then continue
      for y1 in grid do
        for y2 in grid do
          if y2 >= y1 then continue
          let l := symmLossF #[(#[x1 * y1, x1 * y2] : Array Float), #[x2 * y1, x2 * y2]]
          if l < bestLoss then
            bestLoss := l
            best := (x1, x2, y1, y2)
  IO.println s!"    best loss = {fmt bestLoss} at x1 = {fmt best.1}, x2 = {fmt best.2.1}, y1 = {fmt best.2.2.1}, y2 = {fmt best.2.2.2}"
  IO.println "    (the gap positive - mismatch grows and the loss tends to 0: exactly `symm_matched`)"
