import LeanDL.Core.Rng

/-!
# Chapter 5, part 4 — MNIST in Lean

An IDX parser and a one-hidden-layer network trained by hand-coded backpropagation on unboxed
`FloatArray`s. The output-layer gradient is exactly `softmax z - onehot y`, which is the theorem
`ceLoss_grad` of `LeanDL.Ch05.Loss`.
-/

namespace LeanDL.Mnist

-- ANCHOR: idx
/-- Big-endian 32-bit integer, as used by the IDX file format. -/
def be32 (b : ByteArray) (off : Nat) : Nat :=
  (b.get! off).toNat * 16777216 + (b.get! (off + 1)).toNat * 65536 +
    (b.get! (off + 2)).toNat * 256 + (b.get! (off + 3)).toNat

/-- Images flattened row by row, pixels scaled to `[0, 1]`. -/
structure Images where
  count : Nat
  size : Nat
  pixels : FloatArray

def loadImages (path : System.FilePath) (limit : Nat) : IO Images := do
  let b ← IO.FS.readBinFile path
  if be32 b 0 != 2051 then throw (IO.userError s!"{path}: not an IDX image file")
  let n := min (be32 b 4) limit
  let size := be32 b 8 * be32 b 12
  let mut px := FloatArray.emptyWithCapacity (n * size)
  for i in [0:n * size] do
    px := px.push (Float.ofNat (b.get! (16 + i)).toNat / 255.0)
  return ⟨n, size, px⟩

def loadLabels (path : System.FilePath) (limit : Nat) : IO (Array Nat) := do
  let b ← IO.FS.readBinFile path
  if be32 b 0 != 2049 then throw (IO.userError s!"{path}: not an IDX label file")
  let n := min (be32 b 4) limit
  return (Array.range n).map fun i => (b.get! (8 + i)).toNat
-- ANCHOR_END: idx

-- ANCHOR: net
/-- Input → `h` ReLU units → 10 logits. Weight matrices are stored row-major. -/
structure Net where
  h : Nat
  W1 : FloatArray
  b1 : FloatArray
  W2 : FloatArray
  b2 : FloatArray

def Net.init (h : Nat) (seed : UInt64) : Net :=
  let (w1, r) := (Rng.seed seed).uniformArray (h * 784) (Float.sqrt (6.0 / 784.0))
  let (w2, _) := r.uniformArray (10 * h) (Float.sqrt (6.0 / h.toFloat))
  ⟨h, ⟨w1⟩, ⟨Array.replicate h 0.0⟩, ⟨w2⟩, ⟨Array.replicate 10 0.0⟩⟩

/-- Hidden activations and class probabilities for the image starting at offset `off`. -/
def Net.forward (N : Net) (x : FloatArray) (off : Nat) : FloatArray × FloatArray := Id.run do
  let mut a := FloatArray.mk (Array.replicate N.h 0.0)
  for j in [0:N.h] do
    let mut s := N.b1.get! j
    for i in [0:784] do
      s := s + N.W1.get! (j * 784 + i) * x.get! (off + i)
    a := a.set! j (if 0 < s then s else 0)
  let mut z := FloatArray.mk (Array.replicate 10 0.0)
  let mut zmax := -1.0e30
  for k in [0:10] do
    let mut s := N.b2.get! k
    for j in [0:N.h] do
      s := s + N.W2.get! (k * N.h + j) * a.get! j
    z := z.set! k s
    zmax := max zmax s
  -- Subtracting the max keeps `exp` from overflowing; softmax does not change.
  let mut tot := 0.0
  for k in [0:10] do
    let e := Float.exp (z.get! k - zmax)
    z := z.set! k e
    tot := tot + e
  for k in [0:10] do
    z := z.set! k (z.get! k / tot)
  return (a, z)
-- ANCHOR_END: net

-- ANCHOR: sgd
/-- One SGD step on the cross-entropy of image `off / 784` with label `y`. -/
def Net.sgdStep (N : Net) (lr : Float) (x : FloatArray) (off y : Nat) : Net := Id.run do
  let (a, p) := N.forward x off
  -- Gradient with respect to the logits: `softmax z - onehot y` (theorem `ceLoss_grad`).
  let d := FloatArray.mk <| (Array.range 10).map fun k => p.get! k - (if k = y then 1.0 else 0.0)
  let mut W1 := N.W1
  let mut b1 := N.b1
  let mut W2 := N.W2
  let mut b2 := N.b2
  for j in [0:N.h] do
    -- Back through `W2` and the ReLU, using the weights *before* they are updated.
    let mut da := 0.0
    for k in [0:10] do
      da := da + N.W2.get! (k * N.h + j) * d.get! k
    let dz := if 0 < a.get! j then da else 0.0
    if dz != 0.0 then
      for i in [0:784] do
        W1 := W1.set! (j * 784 + i) (W1.get! (j * 784 + i) - lr * dz * x.get! (off + i))
      b1 := b1.set! j (b1.get! j - lr * dz)
  for k in [0:10] do
    for j in [0:N.h] do
      W2 := W2.set! (k * N.h + j) (W2.get! (k * N.h + j) - lr * d.get! k * a.get! j)
    b2 := b2.set! k (b2.get! k - lr * d.get! k)
  return { N with W1 := W1, b1 := b1, W2 := W2, b2 := b2 }
-- ANCHOR_END: sgd

def argmax (p : FloatArray) : Nat := Id.run do
  let mut best := 0
  for k in [1:10] do
    if p.get! k > p.get! best then best := k
  return best

def Net.accuracy (N : Net) (imgs : Images) (labels : Array Nat) : Float := Id.run do
  let mut ok := 0
  for i in [0:imgs.count] do
    if argmax (N.forward imgs.pixels (i * 784)).2 == labels[i]! then ok := ok + 1
  return ok.toFloat / imgs.count.toFloat

/-- Fisher–Yates shuffle driven by the deterministic generator. -/
def shuffle (r : Rng) (n : Nat) : Array Nat × Rng := Id.run do
  let mut a := Array.range n
  let mut r := r
  for i' in [0:n - 1] do
    let i := n - 1 - i'
    let (u, r') := r.uniform
    r := r'
    let j := (u * (i + 1).toFloat).toUInt64.toNat
    a := a.swapIfInBounds i (min j i)
  return (a, r)

end LeanDL.Mnist
