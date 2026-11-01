import LeanDL.Ch03.Mlp

/-!
# Chapter 3, part 3 — Training a 2-layer network by hand-derived gradients

Chapter 4 derives gradients automatically; here we do the chain rule by hand once, on the
smallest interesting network, so that backpropagation is no surprise later.
-/

namespace LeanDL.Ch03

open LeanDL.Ch01

variable {α : Type} [Add α] [Sub α] [Mul α] [Div α] [Neg α] [OfNat α 0] [OfNat α 1] [HasExp α]

-- ANCHOR: net2
/-- `n` inputs, `h` sigmoid hidden units, one sigmoid output. -/
structure Net2 (α : Type) (n h : Nat) where
  W1 : Mat α h n
  b1 : Vec α h
  w2 : Vec α h
  b2 : α

def Net2.hidden {n h : Nat} (N : Net2 α n h) (x : Vec α n) : Vec α h :=
  fun j => sigmoid (Vec.dot (N.W1 j) x + N.b1 j)

def Net2.predict {n h : Nat} (N : Net2 α n h) (x : Vec α n) : α :=
  sigmoid (Vec.dot N.w2 (N.hidden x) + N.b2)
-- ANCHOR_END: net2

-- ANCHOR: sgd
/-- One SGD step on the loss `½ (ŷ - y)²`. With `a = hidden x` and `ŷ = predict x`:

* `δ₂ = (ŷ - y) · ŷ (1 - ŷ)`            (output layer error)
* `δ₁ⱼ = δ₂ · w₂ⱼ · aⱼ (1 - aⱼ)`        (error pushed back through `w₂` and the sigmoid)
* every parameter moves against `δ · (the signal that entered it)`. -/
def Net2.sgdStep {n h : Nat} (lr : α) (N : Net2 α n h) (x : Vec α n) (y : α) : Net2 α n h :=
  let a := N.hidden x
  let p := N.predict x
  let d2 := (p - y) * p * (1 - p)
  let d1 : Vec α h := fun j => d2 * N.w2 j * a j * (1 - a j)
  { W1 := fun j i => N.W1 j i - lr * d1 j * x i
    b1 := fun j => N.b1 j - lr * d1 j
    w2 := fun j => N.w2 j - lr * d2 * a j
    b2 := N.b2 - lr * d2 }
-- ANCHOR_END: sgd

/-! ## The same network on arrays, for speed

`Vec` is a function, so a parameter produced by `fun i => old i - …` keeps a reference to every
previous version of itself: iterating SGD this way is exponentially slow. The executable
version stores plain arrays; the `Vec` version above stays the readable specification. -/

-- ANCHOR: net2a
structure Net2A (α : Type) where
  W1 : Array (Array α)
  b1 : Array α
  w2 : Array α
  b2 : α

variable [Inhabited α]

def dotA (u v : Array α) : α := Id.run do
  let mut s : α := 0
  for i in [0:min u.size v.size] do
    s := s + u[i]! * v[i]!
  return s

def Net2A.hidden (N : Net2A α) (x : Array α) : Array α :=
  (N.W1.zip N.b1).map fun (row, b) => sigmoid (dotA row x + b)

def Net2A.predict (N : Net2A α) (x : Array α) : α :=
  sigmoid (dotA N.w2 (N.hidden x) + N.b2)

/-- The same update as `Net2.sgdStep`. -/
def Net2A.sgdStep (lr : α) (N : Net2A α) (x : Array α) (y : α) : Net2A α :=
  let a := N.hidden x
  let p := N.predict x
  let d2 := (p - y) * p * (1 - p)
  let d1 := (N.w2.zip a).map fun (w, aj) => d2 * w * aj * (1 - aj)
  { W1 := (N.W1.zip d1).map fun (row, dj) => (row.zip x).map fun (w, xi) => w - lr * dj * xi
    b1 := (N.b1.zip d1).map fun (b, dj) => b - lr * dj
    w2 := (N.w2.zip a).map fun (w, aj) => w - lr * d2 * aj
    b2 := N.b2 - lr * d2 }

def Net2A.fit (lr : α) (data : List (Array α × α)) : Nat → Net2A α → Net2A α
  | 0, N => N
  | e + 1, N => Net2A.fit lr data e (data.foldl (fun N xy => N.sgdStep lr xy.1 xy.2) N)
-- ANCHOR_END: net2a

/-- Read an array network back as the `Vec` specification. -/
def Net2A.toNet2 {n h : Nat} (N : Net2A α) : Net2 α n h :=
  { W1 := fun j i => (N.W1.getD j.val #[]).getD i.val 0
    b1 := fun j => N.b1.getD j.val 0
    w2 := fun j => N.w2.getD j.val 0
    b2 := N.b2 }

end LeanDL.Ch03
