import LeanDL.Ch05.Mnist

open LeanDL LeanDL.Mnist

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "../data/mnist"
  let nTrain := (args.getD 0 "10000").toNat!
  let nTest := (args.getD 1 "2000").toNat!
  let epochs := (args.getD 2 "3").toNat!
  unless (← (dir / "train-images-idx3-ubyte").pathExists) do
    IO.eprintln "MNIST not found. Run scripts/get-mnist.ps1 (or .sh) from the repository root first."
    IO.Process.exit 1
  let trainX ← loadImages (dir / "train-images-idx3-ubyte") nTrain
  let trainY ← loadLabels (dir / "train-labels-idx1-ubyte") nTrain
  let testX ← loadImages (dir / "t10k-images-idx3-ubyte") nTest
  let testY ← loadLabels (dir / "t10k-labels-idx1-ubyte") nTest
  IO.println s!"train {trainX.count}, test {testX.count}"
  let mut net := Net.init 64 7
  let mut rng := Rng.seed 123
  for e in [0:epochs] do
    let (order, r') := shuffle rng trainX.count
    rng := r'
    for i in order do
      net := net.sgdStep 0.01 trainX.pixels (i * 784) trainY[i]!
    IO.println s!"epoch {e + 1}: test accuracy = {net.accuracy testX testY}"
