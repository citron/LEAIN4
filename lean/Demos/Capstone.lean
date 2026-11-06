import LeanDL.Ch05.Mnist
import LeanDL.Ch20.Capstone

/-!
# Chapter 20 — Capstone demo (`lake exe capstone`)

Two faces of the same recipe.

1. `Rat` exact face: the closed form `recipe_closed` and the iterate bound
   `recipe_iter_sq_le` evaluated on a concrete quadratic — the numbers in
   the output ARE instances of the theorems (the printed `w^2 <= w0^2`
   comparisons decide true, exactly as the theorem guarantees).
2. `Float` face: the same recipe — decoupled weight decay, gradient
   clipping, exponential schedule (`lrAt`) — run end to end on real MNIST
   pixels with the Chapter 5 network. This is the whole course in one
   loop: init (Ch05), forward (Ch03/Ch05), loss gradient (Ch04/Ch05),
   clip + decay + schedule (Ch05 Kit, Ch20), measure (every chapter).
-/

open LeanDL LeanDL.Mnist LeanDL.Ch05 LeanDL.Ch20

/-- Box clamp: the Float face of Kit `clip` (piecewise, same shape). -/
def clamp (c g : Float) : Float :=
  if g < -c then -c else if c < g then c else g

/-- Decoupled weight decay on every weight of the Ch05 net:
`w ← w·(1 - lr·wd)` — `decoupledShrink` (Ch05 Kit) on every entry. -/
def decayNet (N : Net) (lr wd : Float) : Net :=
  let s := 1.0 - lr * wd
  { N with
    W1 := FloatArray.mk (N.W1.data.map (· * s)),
    W2 := FloatArray.mk (N.W2.data.map (· * s)),
    b1 := FloatArray.mk (N.b1.data.map (· * s)),
    b2 := FloatArray.mk (N.b2.data.map (· * s)) }

/-- One SGD step with per-parameter gradient clipping to `[-c, c]`:
the Float face of Ch20 `recipeStep` (decay applied by the caller first,
then `clip` on every gradient coordinate, then the step). -/
def sgdStepClip (N : Net) (lr c : Float) (x : FloatArray) (off y : Nat) : Net := Id.run do
  let (a, p) := N.forward x off
  let raw := (Array.range 10).map fun k => p.get! k - (if k = y then 1.0 else 0.0)
  let d := FloatArray.mk (raw.map (clamp c))
  let mut W1 := N.W1
  let mut b1 := N.b1
  let mut W2 := N.W2
  let mut b2 := N.b2
  for j in [0:N.h] do
    let mut da := 0.0
    for k in [0:10] do
      da := da + N.W2.get! (k * N.h + j) * d.get! k
    let dz := if 0 < a.get! j then da else 0.0
    if dz != 0.0 then
      let dzc := clamp c dz
      for i in [0:784] do
        W1 := W1.set! (j * 784 + i) (W1.get! (j * 784 + i) - lr * dzc * x.get! (off + i))
      b1 := b1.set! j (b1.get! j - lr * dzc)
  for k in [0:10] do
    for j in [0:N.h] do
      W2 := W2.set! (k * N.h + j) (W2.get! (k * N.h + j) - lr * d.get! k * a.get! j)
    b2 := b2.set! k (b2.get! k - lr * d.get! k)
  return { N with W1 := W1, b1 := b1, W2 := W2, b2 := b2 }

/-- Exact face: the quadratic recipe iterated; the closed form of
`recipe_closed` and the bound of `recipe_iter_sq_le` per iterate. -/
def checkExact : IO Unit := do
  let lr : Rat := 1 / 20
  let wd : Rat := 1 / 50
  let c : Rat := 5
  -- w0 = 2 keeps the gradient 2*w0 = 4 inside the box, so the closed form applies.
  let w0 : Rat := 2
  let γ : Rat := 9 / 10
  IO.println "exact Rat face (theorem instances):"
  IO.println s!"  lr = {lr}, wd = {wd}, clip box = [-{c}, {c}], w0 = {w0}"
  IO.println s!"  box check: 2*w0 = {2 * w0} <= {c}: {toString (decide (2 * w0 <= c))}"
  let mut w := w0
  for t in [0:8] do
    let closedForm := powN (1 - lr * (2 + wd)) t * w0
    IO.println s!"  t = {t}: w = {w}  closed form = {closedForm}  w^2 <= w0^2: {toString (decide (w * w <= w0 * w0))}"
    w := plainStep lr wd w
  -- Clipping bites outside the box: at w = 3 the gradient is 6 > 5.
  let gBig : Rat := 2 * 3
  IO.println s!"  clipped gradient at w = 3: clip {c} {gBig} = {clip c gBig}"
  -- Budget theorem instance: eta0 = 1/10, gamma = 9/10 over 10 epochs.
  let η₀ : Rat := 1 / 10
  let budget : Rat := η₀ / (1 - γ)
  let spent := (List.range 10).map (fun t => lrAt η₀ γ t) |>.foldl (· + ·) 0
  IO.println s!"  schedule budget (10 epochs): spent {spent} <= bound {budget}: {toString (decide (spent <= budget))}"

/-- Float face: the full recipe on MNIST with the Ch05 network. -/
def runMnist (nTrain nTest epochs : Nat) : IO Unit := do
  let dir : System.FilePath := "../data/mnist"
  unless (← (dir / "train-images-idx3-ubyte").pathExists) do
    IO.eprintln "MNIST not found. Run scripts/get-mnist.ps1 (or .sh) from the repository root first."
    IO.Process.exit 1
  let trainX ← loadImages (dir / "train-images-idx3-ubyte") nTrain
  let trainY ← loadLabels (dir / "train-labels-idx1-ubyte") nTrain
  let testX ← loadImages (dir / "t10k-images-idx3-ubyte") nTest
  let testY ← loadLabels (dir / "t10k-labels-idx1-ubyte") nTest
  IO.println s!"MNIST face: train {trainX.count}, test {testX.count}"
  -- The recipe knobs: Float face of the Rat definitions checked above.
  let lr0 : Float := 0.05
  let γ : Float := 0.7
  let wd : Float := 1e-4
  let mut net := Net.init 64 20261106
  let mut rng := Rng.seed 777
  for e in [0:epochs] do
    -- Exponential schedule: Float face of `lrAt η₀ γ e` (Ch05 Kit).
    let lr := lr0 * Float.pow γ (Float.ofNat e)
    let (order, r') := shuffle rng trainX.count
    rng := r'
    for i in order do
      -- Ch20 recipe: decoupled decay on the weights first, then the
      -- clipped-gradient SGD step.
      net := decayNet net lr wd
      net := sgdStepClip net lr 1.0 trainX.pixels (i * 784) trainY[i]!
    IO.println s!"  epoch {e + 1}: lr = {lr}, test accuracy = {net.accuracy testX testY}"

def main (args : List String) : IO Unit := do
  checkExact
  runMnist (args.getD 0 "10000").toNat! (args.getD 1 "2000").toNat!
    (args.getD 2 "3").toNat!
