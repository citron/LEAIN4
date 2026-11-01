import LeanDL.Ch04.Network
import LeanDL.Ch05.Optim
import LeanDL.Core.Rng

open LeanDL LeanDL.Ch04 LeanDL.Ch05

abbrev sizes : List Nat := [2, 3, 3, 1]
abbrev P : Nat := 25

def data : List (Float × Float × Float) := [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]

def lossE : Expr Float P :=
  Expr.sum (data.map fun (a, b, y) =>
    let out := mlpE .tanh .sigmoid sizes 0 [.const a, .const b]
    sqErr (out.headD (.const 0)) (.const y))

def vecOf (p : Array Float) : Vec Float P := fun i => p[i.val]!

def lossAt (p : Array Float) : Float := lossE.eval (vecOf p)

def checkpoints : List Nat := [50, 100, 200, 400, 800, 1600]

def report (name : String) (losses : Array Float) : IO Unit :=
  IO.println (s!"{name}: " ++ ", ".intercalate (checkpoints.map fun c => s!"{c}: {losses[c - 1]!}"))

def main : IO Unit := do
  let (p0, _) := (Rng.seed 42).uniformArray P 1.0
  let steps := 1600
  -- Plain gradient descent.
  let mut p := p0
  let mut log : Array Float := #[]
  for _ in [0:steps] do
    p := sgdStep 0.3 p (lossE.backprop (vecOf p))
    log := log.push (lossAt p)
  report "SGD      " log
  -- Momentum.
  p := p0
  let mut v : Array Float := Array.replicate P 0
  log := #[]
  for _ in [0:steps] do
    let (p', v') := momentumStep 0.05 0.9 v p (lossE.backprop (vecOf p))
    p := p'; v := v'
    log := log.push (lossAt p)
  report "Momentum " log
  -- Adam.
  p := p0
  let mut st : AdamState Float := AdamState.init P
  log := #[]
  for _ in [0:steps] do
    let (p', st') := adamStep 0.05 0.9 0.999 1e-8 st p (lossE.backprop (vecOf p))
    p := p'; st := st'
    log := log.push (lossAt p)
  report "Adam     " log
