import LeanDL.Core.Mat
import LeanDL.Ch01.Neuron

/-!
# Chapter 3 — The multi-layer perceptron
-/

namespace LeanDL.Ch03

open LeanDL.Ch01

variable {α : Type}

-- ANCHOR: layer
/-- A layer with `nin` inputs and `nout` neurons: one weight row and one bias per neuron. -/
structure Layer (α : Type) (nin nout : Nat) where
  W : Mat α nout nin
  b : Vec α nout

/-- The `i`-th neuron of the layer, as in Chapter 1. -/
def Layer.neuron {nin nout : Nat} (L : Layer α nin nout) (i : Fin nout) : Neuron α nin :=
  ⟨L.W i, L.b i⟩

def Layer.forward [Add α] [Mul α] [OfNat α 0] {nin nout : Nat}
    (act : α → α) (L : Layer α nin nout) (x : Vec α nin) : Vec α nout :=
  fun i => act (Vec.dot (L.W i) x + L.b i)

/-- A layer is a vector of independent neurons that share their input. -/
theorem Layer.forward_eq_fire [Add α] [Mul α] [OfNat α 0] {nin nout : Nat}
    (act : α → α) (L : Layer α nin nout) (x : Vec α nin) (i : Fin nout) :
    L.forward act x i = (L.neuron i).fire act x := rfl
-- ANCHOR_END: layer

-- ANCHOR: mlp
/-- A network from `n` inputs to `m` outputs. The sizes of consecutive layers must agree,
and this is checked by the type checker. -/
inductive MLP (α : Type) : Nat → Nat → Type
  | last {n m : Nat} : Layer α n m → MLP α n m
  | cons {n h m : Nat} : Layer α n h → MLP α h m → MLP α n m

/-- `hid` is the activation of hidden layers, `out` that of the last layer. -/
def MLP.forward [Add α] [Mul α] [OfNat α 0] (hid out : α → α) :
    {n m : Nat} → MLP α n m → Vec α n → Vec α m
  | _, _, .last L, x => L.forward out x
  | _, _, .cons L N, x => N.forward hid out (L.forward hid x)
-- ANCHOR_END: mlp

/-! ## XOR with two layers -/

-- ANCHOR: xornet
/-- XOR = AND (OR x₁ x₂) (NAND x₁ x₂): the hidden layer computes OR and NAND. -/
def xorNet : MLP Int 2 1 :=
  .cons (h := 2)
    ⟨Mat.ofLists [[1, 1], [-1, -1]], Vec.ofList [-1, 1]⟩
    (.last ⟨Mat.ofLists [[1, 1]], Vec.ofList [-2]⟩)

theorem xorNet_correct (a b : Bool) :
    xorNet.forward step step (v2 (b2i a) (b2i b)) 0 = b2i (a ^^ b) := by
  cases a <;> cases b <;> decide
-- ANCHOR_END: xornet

end LeanDL.Ch03
