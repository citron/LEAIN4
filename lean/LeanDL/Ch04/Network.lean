import LeanDL.Ch04.Correct

/-!
# Chapter 4, part 3 — Networks as expressions

Any architecture that can be written as an `Expr` gets its gradient for free, and the gradient
is correct by `backprop_correct`.
-/

namespace LeanDL.Ch04

variable {α : Type} {n : Nat}

-- ANCHOR: builders
/-- The `k`-th parameter; out-of-range indices read as `0`. -/
def Expr.param [OfNat α 0] (k : Nat) : Expr α n :=
  if h : k < n then .var ⟨k, h⟩ else .const 0

def Expr.sum [OfNat α 0] (l : List (Expr α n)) : Expr α n := l.foldr .add (.const 0)

/-- A dense layer: neuron `j` has weights `base + j (nin+1) + i` and its bias right after them. -/
def denseE [OfNat α 0] (act : Expr α n → Expr α n) (base nin nout : Nat)
    (xs : List (Expr α n)) : List (Expr α n) :=
  (List.range nout).map fun j =>
    let off := base + j * (nin + 1)
    act (.add (Expr.sum ((List.range nin).map fun i => .mul (Expr.param (off + i)) (xs.getD i (.const 0))))
      (Expr.param (off + nin)))

/-- A multi-layer perceptron with layer sizes `[nin, h₁, …, nout]`; `hid` on the hidden layers,
`out` on the last one. -/
def mlpE [OfNat α 0] (hid out : Expr α n → Expr α n) :
    List Nat → Nat → List (Expr α n) → List (Expr α n)
  | nin :: nout :: rest, base, xs =>
    mlpE hid out (nout :: rest) (base + nout * (nin + 1))
      (denseE (if rest.isEmpty then out else hid) base nin nout xs)
  | _, _, xs => xs

/-- Number of parameters of such a network. -/
def mlpParams : List Nat → Nat
  | nin :: nout :: rest => nout * (nin + 1) + mlpParams (nout :: rest)
  | _ => 0

def sqErr (p y : Expr α n) : Expr α n := .mul (.sub p y) (.sub p y)
-- ANCHOR_END: builders

section DeltaRule

open Lean.Grind

variable [CommRing α] [HasAct α]

-- ANCHOR: delta_rule
/-- Squared error of one sigmoid neuron with two inputs, as an expression in `(w₀, w₁, b)`. -/
def neuronLoss (x0 x1 y : α) : Expr α 3 :=
  sqErr (.sigmoid (.add (.add (.mul (.var 0) (.const x0)) (.mul (.var 1) (.const x1))) (.var 2)))
    (.const y)

/-- Backpropagation through one neuron is the classical delta rule:
`∂L/∂w₀ = 2 (σ(u) - y) · σ(u)(1 - σ(u)) · x₀`. -/
theorem delta_rule (x0 x1 y : α) (w : Vec α 3) :
    let u := w 0 * x0 + w 1 * x1 + w 2
    ((neuronLoss x0 x1 y).backprop w).getD 0 0 =
      2 * (HasAct.sigmoid u - y) * (HasAct.sigmoid u * (1 - HasAct.sigmoid u)) * x0 := by
  intro u
  have := backprop_correct w (neuronLoss x0 x1 y) 0
  simp only [Fin.val_zero] at this
  rw [this]
  simp [neuronLoss, sqErr, Expr.deriv, Expr.eval, u]
  grind
-- ANCHOR_END: delta_rule

end DeltaRule

end LeanDL.Ch04
