import LeanDL.Ch04.Network
import LeanDL.Core.Rng

open LeanDL LeanDL.Ch04

abbrev sizes : List Nat := [2, 3, 3, 1]
abbrev P : Nat := 25

def data : List (Float × Float × Float) := [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]

/-- Total squared error of the 2-3-3-1 network (tanh hidden, sigmoid output) on XOR. -/
def lossE : Expr Float P :=
  Expr.sum (data.map fun (a, b, y) =>
    let out := mlpE .tanh .sigmoid sizes 0 [.const a, .const b]
    sqErr (out.headD (.const 0)) (.const y))

def vecOf (p : Array Float) : Vec Float P := fun i => p[i.val]!

def lossAt (p : Array Float) : Float := lossE.eval (vecOf p)

def step (lr : Float) (p : Array Float) : Array Float :=
  let g := lossE.backprop (vecOf p)
  Array.ofFn (n := P) fun i => p[i.val]! - lr * g[i.val]!

def main : IO Unit := do
  IO.println s!"parameters: {mlpParams sizes}"
  let (p0, _) := (Rng.seed 42).uniformArray P 1.0
  -- Gradient check: backprop against central finite differences.
  let g := lossE.backprop (vecOf p0)
  let eps := 1e-5
  let mut worst := 0.0
  for i in [0:P] do
    let hi := p0.set! i (p0[i]! + eps)
    let lo := p0.set! i (p0[i]! - eps)
    let fd := (lossAt hi - lossAt lo) / (2 * eps)
    worst := max worst (Float.abs (fd - g[i]!))
  IO.println s!"max |backprop - finite difference| over {P} parameters = {worst}"
  -- Train.
  let mut p := p0
  for round in [0:8] do
    IO.println s!"after {round * 1000} steps: loss = {lossAt p}"
    for _ in [0:1000] do
      p := step 0.5 p
  for (a, b, y) in data do
    let out := (mlpE .tanh .sigmoid sizes 0 [.const a, .const b] : List (Expr Float P)).headD (.const 0)
    IO.println s!"({a}, {b}) -> {out.eval (vecOf p)}   target {y}"
