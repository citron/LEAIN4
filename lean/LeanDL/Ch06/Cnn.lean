import LeanDL.Ch05.Mnist

/-!
# Chapter 6, part 2 — A convolutional network on MNIST

28×28 image → 3×3 convolution with `C` channels (26×26) → ReLU → 2×2 max-pooling (13×13) →
dense → 10 logits → softmax cross-entropy. Backpropagation is hand-coded; the kernel gradient
is the correlation of Chapter 6's `conv1d_adjoint`, in two dimensions.
-/

namespace LeanDL.Cnn

open LeanDL.Mnist

-- ANCHOR: net
structure Net where
  C : Nat
  K : FloatArray   -- C × 3 × 3 kernels
  bc : FloatArray  -- C convolution biases
  W : FloatArray   -- 10 × (C · 13 · 13) dense weights
  b : FloatArray   -- 10 dense biases

def Net.init (C : Nat) (seed : UInt64) : Net :=
  let (k, r) := (Rng.seed seed).uniformArray (C * 9) (Float.sqrt (6.0 / 9.0))
  let (w, _) := r.uniformArray (10 * C * 169) (Float.sqrt (6.0 / (C * 169).toFloat))
  ⟨C, ⟨k⟩, ⟨Array.replicate C 0.0⟩, ⟨w⟩, ⟨Array.replicate 10 0.0⟩⟩

/-- Everything the backward pass needs from the forward pass. -/
structure Fwd where
  r : FloatArray    -- C × 26 × 26, after ReLU
  p : FloatArray    -- C × 13 × 13, after max-pooling
  arg : Array Nat   -- for each pooled value, the index in `r` it came from
  probs : FloatArray

def Net.forward (N : Net) (x : FloatArray) (off : Nat) : Fwd := Id.run do
  let C := N.C
  let mut r := FloatArray.mk (Array.replicate (C * 676) 0.0)
  for c in [0:C] do
    for i in [0:26] do
      for j in [0:26] do
        let mut s := N.bc.get! c
        for a in [0:3] do
          for b in [0:3] do
            s := s + N.K.get! (c * 9 + a * 3 + b) * x.get! (off + (i + a) * 28 + (j + b))
        r := r.set! (c * 676 + i * 26 + j) (if 0 < s then s else 0.0)
  let mut p := FloatArray.mk (Array.replicate (C * 169) 0.0)
  let mut arg := Array.replicate (C * 169) 0
  for c in [0:C] do
    for u in [0:13] do
      for v in [0:13] do
        let mut best := c * 676 + (2 * u) * 26 + 2 * v
        for s in [0:2] do
          for t in [0:2] do
            let idx := c * 676 + (2 * u + s) * 26 + (2 * v + t)
            if r.get! idx > r.get! best then best := idx
        p := p.set! (c * 169 + u * 13 + v) (r.get! best)
        arg := arg.set! (c * 169 + u * 13 + v) best
  let F := C * 169
  let mut z := FloatArray.mk (Array.replicate 10 0.0)
  let mut zmax := -1.0e30
  for k in [0:10] do
    let mut s := N.b.get! k
    for f in [0:F] do
      s := s + N.W.get! (k * F + f) * p.get! f
    z := z.set! k s
    zmax := max zmax s
  let mut tot := 0.0
  for k in [0:10] do
    let e := Float.exp (z.get! k - zmax)
    z := z.set! k e
    tot := tot + e
  for k in [0:10] do
    z := z.set! k (z.get! k / tot)
  return ⟨r, p, arg, z⟩
-- ANCHOR_END: net

def Net.loss (N : Net) (x : FloatArray) (off y : Nat) : Float :=
  -Float.log ((N.forward x off).probs.get! y)

structure Grads where
  dK : FloatArray
  dbc : FloatArray
  dW : FloatArray
  db : FloatArray

-- ANCHOR: backward
def Net.backward (N : Net) (x : FloatArray) (off y : Nat) (fw : Fwd) : Grads := Id.run do
  let C := N.C
  let F := C * 169
  -- Output layer: softmax cross-entropy, `p - onehot y` (Chapter 5).
  let d := FloatArray.mk <| (Array.range 10).map fun k =>
    fw.probs.get! k - (if k = y then 1.0 else 0.0)
  let mut dW := FloatArray.mk (Array.replicate (10 * F) 0.0)
  let mut dp := FloatArray.mk (Array.replicate F 0.0)
  for k in [0:10] do
    for f in [0:F] do
      dW := dW.set! (k * F + f) (d.get! k * fw.p.get! f)
      dp := dp.set! f (dp.get! f + N.W.get! (k * F + f) * d.get! k)
  -- Max-pooling sends the gradient to the position that won; the other three get zero.
  let mut dr := FloatArray.mk (Array.replicate (C * 676) 0.0)
  for f in [0:F] do
    let idx := fw.arg[f]!
    dr := dr.set! idx (dr.get! idx + dp.get! f)
  -- ReLU passes the gradient where the unit was active, then the kernel gradient is a
  -- correlation of the input with the incoming gradient.
  let mut dK := FloatArray.mk (Array.replicate (C * 9) 0.0)
  let mut dbc := FloatArray.mk (Array.replicate C 0.0)
  for c in [0:C] do
    for i in [0:26] do
      for j in [0:26] do
        let idx := c * 676 + i * 26 + j
        if 0 < fw.r.get! idx then
          let g := dr.get! idx
          if g != 0.0 then
            dbc := dbc.set! c (dbc.get! c + g)
            for a in [0:3] do
              for b in [0:3] do
                let q := c * 9 + a * 3 + b
                dK := dK.set! q (dK.get! q + g * x.get! (off + (i + a) * 28 + (j + b)))
  return ⟨dK, dbc, dW, d⟩
-- ANCHOR_END: backward

def axpy (a : FloatArray) (lr : Float) (g : FloatArray) : FloatArray := Id.run do
  let mut a := a
  for i in [0:a.size] do
    a := a.set! i (a.get! i - lr * g.get! i)
  return a

def Net.sgdStep (N : Net) (lr : Float) (x : FloatArray) (off y : Nat) : Net :=
  let g := N.backward x off y (N.forward x off)
  { N with K := axpy N.K lr g.dK, bc := axpy N.bc lr g.dbc, W := axpy N.W lr g.dW,
           b := axpy N.b lr g.db }

def Net.accuracy (N : Net) (imgs : Images) (labels : Array Nat) : Float := Id.run do
  let mut ok := 0
  for i in [0:imgs.count] do
    if argmax (N.forward imgs.pixels (i * 784)).probs == labels[i]! then ok := ok + 1
  return ok.toFloat / imgs.count.toFloat

/-- Central finite difference of the loss with respect to kernel entry `q`. -/
def Net.numericKernelGrad (N : Net) (x : FloatArray) (off y q : Nat) (eps : Float) : Float :=
  let up := { N with K := N.K.set! q (N.K.get! q + eps) }
  let dn := { N with K := N.K.set! q (N.K.get! q - eps) }
  (up.loss x off y - dn.loss x off y) / (2 * eps)

end LeanDL.Cnn
