import LeanDL.Ch08.Lstm
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch05

/-- Both models on the memory task, trained with Adam on batches of 32 fresh sequences.
`stages` lists the sequence lengths in order; with a single stage this is plain training.
The parameters are kept from one stage to the next (a curriculum). -/
def run (useLstm : Bool) (stages : List Nat) (steps : Nat) (nh : Nat) (lr : Float) : IO Unit := do
  let mut rng := Rng.seed 21
  let mut pL := Lstm.init nh 3 0.5
  let mut stL : AdamState Float := AdamState.init (Lstm.nParams nh)
  let mut pR := (Rng.seed 3).uniformArray (Rnn.nParams nh) 0.5 |>.1
  let mut stR : AdamState Float := AdamState.init (Rnn.nParams nh)
  for T in stages do
    for _ in [0:steps] do
      let (batch, r') := Rnn.memoryTask rng T 32
      rng := r'
      if useLstm then
        let (_, g) := Lstm.batchLossGrad nh pL batch
        let (p', st') := adamStep lr 0.9 0.999 1e-8 stL pL g
        pL := p'; stL := st'
      else
        let (_, g) := Rnn.batchLossGrad nh pR batch
        let (p', st') := adamStep lr 0.9 0.999 1e-8 stR pR g
        pR := p'; stR := st'
    let (test, _) := Rnn.memoryTask (Rng.seed 99) T 300
    let acc := if useLstm then Lstm.accuracy nh pL test else Rnn.accuracy nh pR test
    IO.println s!"{if useLstm then "LSTM" else "RNN "} T = {T}: test accuracy {acc}"

/-- `lake exe lstm`                      gradient check and gradient sizes
`lake exe lstm exp T steps nh lr rnn|lstm`   plain training (`lr` in thousandths)
`lake exe lstm curr rnn|lstm`           curriculum T = 10, 20, …, 60 -/
def main (args : List String) : IO Unit := do
  let useLstm := (args.getD (if args.head? == some "curr" then 1 else 5) "lstm") == "lstm"
  if args.head? == some "curr" then
    run useLstm [10, 20, 30, 40, 50, 60] 1500 8 0.005
    return
  if args.head? == some "exp" then
    run useLstm [(args.getD 1 "20").toNat!] (args.getD 2 "2500").toNat! (args.getD 3 "8").toNat!
      ((args.getD 4 "5").toNat!.toFloat / 1000.0)
    return
  let nh := 8
  let p := Lstm.init nh 3 0.5
  -- Gradient check of the hand-coded LSTM BPTT against central finite differences.
  let (xs, _) := Rnn.randomBits (Rng.seed 5) 6
  let (_, g, _, _) := Lstm.lossGrad nh p xs 1.0
  let mut worst := 0.0
  for q in [0:Lstm.nParams nh] do
    let l (d : Float) := (Lstm.lossGrad nh (p.set! q (p[q]! + d)) xs 1.0).1
    worst := max worst (Float.abs ((l 1e-5 - l (-1e-5)) / 2e-5 - g[q]!))
  IO.println s!"LSTM gradient check over {Lstm.nParams nh} parameters: max error = {worst}"
  -- How big is the gradient at earlier and earlier steps?
  let (xs30, _) := Rnn.randomBits (Rng.seed 9) 30
  let (_, _, dhN, dcN) := Lstm.lossGrad nh p xs30 1.0
  let pick (a : Array Float) := ", ".intercalate ([0, 5, 10, 15, 20, 25, 29].map fun k => s!"{a[k]!}")
  IO.println "t = 30, 25, 20, 15, 10, 5, 1"
  IO.println s!"  ‖∂L/∂h_t‖: {pick dhN}"
  IO.println s!"  ‖∂L/∂c_t‖: {pick dcN}"
