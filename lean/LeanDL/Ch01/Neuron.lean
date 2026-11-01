import LeanDL.Core.Vec

/-!
# Chapter 1 — The single neuron
-/

namespace LeanDL.Ch01

open Lean.Grind

variable {α : Type}

-- ANCHOR: activations
/-- Heaviside step: the neuron "fires" (outputs 1) when its input is non-negative. -/
def step [LE α] [OfNat α 0] [OfNat α 1] [DecidableRel (α := α) (· ≤ ·)] (x : α) : α :=
  if 0 ≤ x then 1 else 0

def sigmoid [Add α] [Div α] [OfNat α 1] [Neg α] [HasExp α] (x : α) : α :=
  1 / (1 + HasExp.exp (-x))

def relu [LE α] [OfNat α 0] [DecidableRel (α := α) (· ≤ ·)] (x : α) : α :=
  if 0 ≤ x then x else 0

def tanh [Add α] [Sub α] [Div α] [Neg α] [HasExp α] (x : α) : α :=
  (HasExp.exp x - HasExp.exp (-x)) / (HasExp.exp x + HasExp.exp (-x))
-- ANCHOR_END: activations

-- ANCHOR: neuron
/-- A neuron with `n` inputs: a weight vector and a bias. -/
structure Neuron (α : Type) (n : Nat) where
  w : Vec α n
  b : α

namespace Neuron

/-- Weighted sum plus bias, before the activation. -/
def preact [Add α] [Mul α] [OfNat α 0] {n : Nat} (N : Neuron α n) (x : Vec α n) : α :=
  Vec.dot N.w x + N.b

/-- The full neuron: activation applied to the pre-activation. -/
def fire [Add α] [Mul α] [OfNat α 0] {n : Nat} (act : α → α) (N : Neuron α n) (x : Vec α n) : α :=
  act (N.preact x)
-- ANCHOR_END: neuron

end Neuron

/-! ## Logic gates as neurons -/

-- ANCHOR: gates
/-- Pair of inputs as a length-2 vector. -/
def v2 (a b : α) : Vec α 2 := fun i => if i.val = 0 then a else b

def b2i (b : Bool) : Int := if b then 1 else 0

def andN : Neuron Int 2 := ⟨v2 1 1, -2⟩
def orN : Neuron Int 2 := ⟨v2 1 1, -1⟩
def nandN : Neuron Int 2 := ⟨v2 (-1) (-1), 1⟩

theorem and_correct (a b : Bool) :
    andN.fire step (v2 (b2i a) (b2i b)) = b2i (a && b) := by
  cases a <;> cases b <;> decide

theorem or_correct (a b : Bool) :
    orN.fire step (v2 (b2i a) (b2i b)) = b2i (a || b) := by
  cases a <;> cases b <;> decide

theorem nand_correct (a b : Bool) :
    nandN.fire step (v2 (b2i a) (b2i b)) = b2i (!(a && b)) := by
  cases a <;> cases b <;> decide
-- ANCHOR_END: gates

/-! ## Properties of the pre-activation -/

section Laws
variable [CommRing α]

-- ANCHOR: linear
/-- Without bias, the pre-activation is additive: a neuron is a linear map before its activation. -/
theorem preact_add {n : Nat} (w : Vec α n) (x y : Vec α n) :
    Neuron.preact ⟨w, 0⟩ (fun i => x i + y i) =
      Neuron.preact ⟨w, 0⟩ x + Neuron.preact ⟨w, 0⟩ y := by
  simp only [Neuron.preact]
  rw [Vec.dot_add_right]
  grind

theorem preact_smul {n : Nat} (w : Vec α n) (c : α) (x : Vec α n) :
    Neuron.preact ⟨w, 0⟩ (fun i => c * x i) = c * Neuron.preact ⟨w, 0⟩ x := by
  simp only [Neuron.preact]
  rw [Vec.dot_smul_right]
  grind
-- ANCHOR_END: linear

end Laws

section Sigmoid
variable [Field α] [HasExp α] [LawfulExp α]

-- ANCHOR: sigmoid_sym
/-- `σ(x) + σ(-x) = 1`, using only `exp (x + y) = exp x * exp y` and `exp 0 = 1`.
The two non-vanishing hypotheses hold for the real exponential because `exp x > 0`. -/
theorem sigmoid_symm (x : α)
    (h1 : (1 : α) + HasExp.exp (-x) ≠ 0) (h2 : (1 : α) + HasExp.exp x ≠ 0) :
    sigmoid x + sigmoid (-x) = 1 := by
  have hm : HasExp.exp x * HasExp.exp (-x) = 1 := by
    rw [← LawfulExp.exp_add, show x + -x = 0 by grind, LawfulExp.exp_zero]
  unfold sigmoid
  rw [show - -x = x by grind]
  grind
-- ANCHOR_END: sigmoid_sym

end Sigmoid

end LeanDL.Ch01
