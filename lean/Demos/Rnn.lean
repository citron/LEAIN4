import LeanDL.Ch07.Rnn
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Rnn LeanDL.Ch05

def nh : Nat := 8

def train (T : Nat) (steps : Nat) : IO Unit := do
  let (data, r) := memoryTask (Rng.seed 11) T 32
  let (test, _) := memoryTask r T 300
  let (p0, _) := (Rng.seed 3).uniformArray (nParams nh) 0.5
  let mut p := p0
  let mut st : AdamState Float := AdamState.init (nParams nh)
  for _ in [0:steps] do
    let (_, g) := batchLossGrad nh p data
    let (p', st') := adamStep 0.02 0.9 0.999 1e-8 st p g
    p := p'; st := st'
  let (loss, _) := batchLossGrad nh p data
  IO.println s!"T = {T}: train loss {loss}, train accuracy {accuracy nh p data}, test accuracy {accuracy nh p test}"

def main : IO Unit := do
  let (p, _) := (Rng.seed 3).uniformArray (nParams nh) 0.5
  -- Gradient check of the hand-coded BPTT against central finite differences.
  let (xs, _) := randomBits (Rng.seed 5) 6
  let (_, g, _) := lossGrad nh p xs 1.0
  let mut worst := 0.0
  for q in [0:nParams nh] do
    let l (d : Float) := (lossGrad nh (p.set! q (p[q]! + d)) xs 1.0).1
    worst := max worst (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - g[q]!))
  IO.println s!"BPTT gradient check over {nParams nh} parameters: max error = {worst}"
  -- How big is ∂L/∂h_t as it travels back through 30 steps?
  let (xs30, _) := randomBits (Rng.seed 9) 30
  let (_, _, norms) := lossGrad nh p xs30 1.0
  IO.println "‖∂L/∂h_t‖ for t = 30, 25, 20, 15, 10, 5, 1:"
  IO.println ("  " ++ ", ".intercalate ([0, 5, 10, 15, 20, 25, 29].map fun k => s!"{norms[k]!}"))
  -- Can it learn to remember the first bit?
  IO.println "memory task (label = first bit), 8 units, Adam, 800 steps:"
  train 3 800
  train 20 800
  train 60 800
  train 120 800
