import LeanDL.Ch08.Gru
import LeanDL.Ch08.Lstm
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch05

/-- GRU vs LSTM vs vanilla RNN on the memory task, Adam, batches of 32 fresh sequences. -/
def runGru (steps : Nat) (nh : Nat) (lr : Float) : IO Unit := do
  let mut rng := Rng.seed 21
  let mut pG := Gru.init nh 3 0.5
  let mut stG : AdamState Float := AdamState.init (Gru.nParams nh)
  for T in [10, 20, 30, 40] do
    for _ in [0:steps] do
      let (batch, r') := Rnn.memoryTask rng T 32
      rng := r'
      let (_, g) := Gru.batchLossGrad nh pG batch
      let (p', st') := adamStep lr 0.9 0.999 1e-8 stG pG g
      pG := p'; stG := st'
    let (test, _) := Rnn.memoryTask (Rng.seed 99) T 300
    let accG := Gru.accuracy nh pG test
    IO.println s!"T = {T}: GRU test accuracy {accG}"

/-- `lake exe gru`                 gradient check and gradient sizes
`lake exe gru exp T steps nh lr`  training on the memory task (`lr` in thousandths) -/
def main (args : List String) : IO Unit := do
  if args.head? == some "exp" then
    runGru (args.getD 2 "1500").toNat! (args.getD 3 "8").toNat!
      ((args.getD 4 "5").toNat!.toFloat / 1000.0)
    return
  let nh := 8
  let p := Gru.init nh 3 0.5
  -- Gradient check of the hand-coded GRU BPTT against central finite differences.
  let (xs, _) := Rnn.randomBits (Rng.seed 5) 6
  let (_, g, _) := Gru.lossGrad nh p xs 1.0
  let mut worst := 0.0
  for q in [0:Gru.nParams nh] do
    let l (d : Float) := (Gru.lossGrad nh (p.set! q (p[q]! + d)) xs 1.0).1
    worst := max worst (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - g[q]!))
  IO.println s!"GRU gradient check over {Gru.nParams nh} parameters: max error = {worst}"
  -- How big is the gradient at earlier and earlier steps?
  let (xs30, _) := Rnn.randomBits (Rng.seed 9) 30
  let (_, _, dhN) := Gru.lossGrad nh p xs30 1.0
  let pick (a : Array Float) := ", ".intercalate ([0, 5, 10, 15, 20, 25, 29].map fun k => s!"{a[k]!}")
  IO.println "t = 30, 25, 20, 15, 10, 5, 1"
  IO.println s!"  ‖∂L/∂h_t‖: {pick dhN}"
