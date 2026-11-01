import LeanDL.Ch06.Cnn

open LeanDL LeanDL.Cnn

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "../data/mnist"
  let nTrain := (args.getD 0 "20000").toNat!
  let nTest := (args.getD 1 "5000").toNat!
  let epochs := (args.getD 2 "2").toNat!
  unless (← (dir / "train-images-idx3-ubyte").pathExists) do
    IO.eprintln "MNIST not found. Run scripts/get-mnist.ps1 (or .sh) from the repository root first."
    IO.Process.exit 1
  let trainX ← Mnist.loadImages (dir / "train-images-idx3-ubyte") nTrain
  let trainY ← Mnist.loadLabels (dir / "train-labels-idx1-ubyte") nTrain
  let testX ← Mnist.loadImages (dir / "t10k-images-idx3-ubyte") nTest
  let testY ← Mnist.loadLabels (dir / "t10k-labels-idx1-ubyte") nTest
  -- Gradient check of the hand-coded kernel gradient against finite differences.
  let small := Net.init 2 5
  let g := small.backward trainX.pixels 0 trainY[0]! (small.forward trainX.pixels 0)
  let mut worst := 0.0
  for q in [0:18] do
    let fd := small.numericKernelGrad trainX.pixels 0 trainY[0]! q 1e-5
    worst := max worst (Float.abs (fd - g.dK.get! q))
  IO.println s!"kernel gradient check: max |backprop - finite difference| = {worst}"
  IO.println s!"train {trainX.count}, test {testX.count}"
  let mut net := Net.init 4 7
  let mut rng := Rng.seed 123
  for e in [0:epochs] do
    let (order, r') := Mnist.shuffle rng trainX.count
    rng := r'
    for i in order do
      net := net.sgdStep 0.01 trainX.pixels (i * 784) trainY[i]!
    IO.println s!"epoch {e + 1}: test accuracy = {net.accuracy testX testY}"
