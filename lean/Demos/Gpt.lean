import LeanDL.Ch09.Gpt
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Gpt LeanDL.Ch05

/-- Train with Adam on a fresh batch of the delay task at every step. -/
def trainDelay (usePos : Bool) (lag steps : Nat) : IO Unit := do
  let c : Cfg := { V := 8, d := 16, hd := 32, Tmax := 12, usePos }
  let mut p := init c 1
  let mut st : AdamState Float := AdamState.init c.total
  let mut rng := Rng.seed 2
  for _ in [0:steps] do
    let (batch, r') := delayTask rng c 12 lag 16
    rng := r'
    let mut g := Array.replicate c.total 0.0
    for (toks, tg) in batch do
      let (_, gi) := lossGrad c p toks tg
      g := (g.zip gi).map fun (a, b) => a + b
    g := g.map (· / 16.0)
    let (p', st') := adamStep 0.01 0.9 0.999 1e-8 st p g
    p := p'; st := st'
  let (test, _) := delayTask (Rng.seed 77) c 12 lag 200
  IO.println s!"{if usePos then "with positions   " else "without positions"}: test accuracy {accuracy c p test} (chance {1.0 / c.V.toFloat})"

/-- A tiny character-level language model. -/
def trainLm (steps : Nat) : IO Unit := do
  let base := "the cat sat on the mat. the dog sat on the log. the cat saw the dog. the dog saw the cat. "
  let text := base ++ base ++ base ++ base
  let chars := text.toList
  let vocab := (chars.eraseDups).toArray.qsort (· < ·)
  let enc (ch : Char) : Nat := (vocab.findIdx? (· == ch)).getD 0
  let ids := chars.toArray.map enc
  let c : Cfg := { V := vocab.size, d := 24, hd := 48, Tmax := 24, usePos := true }
  let mut p := init c 5
  let mut st : AdamState Float := AdamState.init c.total
  let mut rng := Rng.seed 8
  IO.println s!"vocabulary: {vocab.size} characters, {c.total} parameters"
  for step in [0:steps] do
    let mut g := Array.replicate c.total 0.0
    let mut tot := 0.0
    for _ in [0:8] do
      let (u, r') := rng.uniform
      rng := r'
      let start := (u * (ids.size - c.Tmax - 1).toFloat).toUInt64.toNat
      let toks := ids.extract start (start + c.Tmax)
      let tg := ids.extract (start + 1) (start + 1 + c.Tmax)
      let (l, gi) := lossGrad c p toks tg
      tot := tot + l
      g := (g.zip gi).map fun (a, b) => a + b
    g := g.map (· / 8.0)
    let (p', st') := adamStep 0.005 0.9 0.999 1e-8 st p g
    p := p'; st := st'
    if step % 300 == 0 || step + 1 == steps then
      IO.println s!"step {step}: loss {tot / 8.0}"
  -- Sample 80 characters after the prompt "the ".
  let mut ctx : Array Nat := "the ".toList.toArray.map enc
  let mut out := "the "
  for _ in [0:80] do
    let window := if ctx.size > c.Tmax then ctx.extract (ctx.size - c.Tmax) ctx.size else ctx
    let fw := forward c p window
    let t := window.size - 1
    let (u, r') := rng.uniform
    rng := r'
    let mut acc := 0.0
    let mut pick := c.V - 1
    for v in [0:c.V] do
      acc := acc + fw.P[t * c.V + v]!
      if acc > u then
        pick := v
        break
    ctx := ctx.push pick
    out := out.push vocab[pick]!
  IO.println s!"sample: {out}"
def main (args : List String) : IO Unit := do
  -- Gradient check of the hand-coded backward pass.
  let c : Cfg := { V := 5, d := 4, hd := 6, Tmax := 5, usePos := true }
  let p := init c 3
  let toks := #[0, 3, 1, 4, 2]
  let tg := #[1, 2, 3, 0, 5]
  let (_, g) := lossGrad c p toks tg
  let mut worst := 0.0
  for q in [0:c.total] do
    let l (dl : Float) := loss c (p.set! q (p[q]! + dl)) toks tg
    worst := max worst (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - g[q]!))
  IO.println s!"gradient check over {c.total} parameters: max error = {worst}"
  if args.head? == some "lm" then
    trainLm ((args.getD 1 "1500").toNat!)
    return
  let steps := (args.getD 0 "1500").toNat!
  IO.println s!"delay task: predict the token 2 positions back, {steps} steps"
  trainDelay true 2 steps
  trainDelay false 2 steps
