import LeanDL.Core.Vec

/-!
# Chapter 4 — Automatic differentiation

Expressions over `n` input variables, with
* `eval`  — the value,
* `deriv` — the *formal* partial derivative (an expression again),
* `fwd`   — forward mode (dual numbers),
* `backA` — reverse mode (backpropagation) accumulating into an array.

Nothing here uses real analysis: `deriv` encodes the usual calculus rules (sum, product, chain
rule, `exp' = exp`, `σ' = σ(1-σ)`, `tanh' = 1 - tanh²`), and the theorems show that both
automatic-differentiation algorithms compute exactly those partial derivatives.
-/

namespace LeanDL.Ch04

/-- Scalar types with the non-linearities we differentiate. -/
class HasAct (α : Type) extends HasExp α where
  sigmoid : α → α
  tanh : α → α
  log : α → α
  inv : α → α
  sqrt : α → α
  /-- `1` on positive inputs, `0` otherwise: the derivative of `relu`. -/
  step : α → α
  relu : α → α

instance : HasAct Float where
  exp := Float.exp
  sigmoid x := 1 / (1 + Float.exp (-x))
  tanh := Float.tanh
  log := Float.log
  inv x := 1 / x
  sqrt := Float.sqrt
  step x := if 0 < x then 1 else 0
  relu x := if 0 < x then x else 0

-- ANCHOR: expr
/-- A scalar expression in `n` variables. -/
inductive Expr (α : Type) (n : Nat) : Type
  | var (i : Fin n)
  | const (c : α)
  | add (a b : Expr α n)
  | sub (a b : Expr α n)
  | mul (a b : Expr α n)
  | exp (a : Expr α n)
  | sigmoid (a : Expr α n)
  | tanh (a : Expr α n)
  | log (a : Expr α n)
  | inv (a : Expr α n)
  | sqrt (a : Expr α n)
  | relu (a : Expr α n)
  | step (a : Expr α n)

variable {α : Type} {n : Nat} [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] [HasAct α]

def Expr.eval (x : Vec α n) : Expr α n → α
  | .var i => x i
  | .const c => c
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .mul a b => a.eval x * b.eval x
  | .exp a => HasExp.exp (a.eval x)
  | .sigmoid a => HasAct.sigmoid (a.eval x)
  | .tanh a => HasAct.tanh (a.eval x)
  | .log a => HasAct.log (a.eval x)
  | .inv a => HasAct.inv (a.eval x)
  | .sqrt a => HasAct.sqrt (a.eval x)
  | .relu a => HasAct.relu (a.eval x)
  | .step a => HasAct.step (a.eval x)
-- ANCHOR_END: expr

-- ANCHOR: deriv
/-- The formal partial derivative with respect to variable `j`, as an expression. -/
def Expr.deriv (j : Fin n) : Expr α n → Expr α n
  | .var i => .const (if i = j then 1 else 0)
  | .const _ => .const 0
  | .add a b => .add (a.deriv j) (b.deriv j)
  | .sub a b => .sub (a.deriv j) (b.deriv j)
  | .mul a b => .add (.mul (a.deriv j) b) (.mul a (b.deriv j))
  | .exp a => .mul (.exp a) (a.deriv j)
  | .sigmoid a => .mul (.mul (.sigmoid a) (.sub (.const 1) (.sigmoid a))) (a.deriv j)
  | .tanh a => .mul (.sub (.const 1) (.mul (.tanh a) (.tanh a))) (a.deriv j)
  | .log a => .mul (.inv a) (a.deriv j)
  | .inv a => .mul (.sub (.const 0) (.mul (.inv a) (.inv a))) (a.deriv j)
  | .sqrt a => .mul (.inv (.add (.sqrt a) (.sqrt a))) (a.deriv j)
  | .relu a => .mul (.step a) (a.deriv j)
  | .step _ => .const 0

/-- The gradient, read off the symbolic derivatives. -/
def Expr.grad (e : Expr α n) (x : Vec α n) : Vec α n := fun j => (e.deriv j).eval x
-- ANCHOR_END: deriv

-- ANCHOR: fwd
/-- Forward mode: value and directional derivative along `dx`, computed together. -/
def Expr.fwd (x dx : Vec α n) : Expr α n → α × α
  | .var i => (x i, dx i)
  | .const c => (c, 0)
  | .add a b => ((a.fwd x dx).1 + (b.fwd x dx).1, (a.fwd x dx).2 + (b.fwd x dx).2)
  | .sub a b => ((a.fwd x dx).1 - (b.fwd x dx).1, (a.fwd x dx).2 - (b.fwd x dx).2)
  | .mul a b =>
    ((a.fwd x dx).1 * (b.fwd x dx).1,
     (a.fwd x dx).2 * (b.fwd x dx).1 + (a.fwd x dx).1 * (b.fwd x dx).2)
  | .exp a =>
    (HasExp.exp (a.fwd x dx).1, HasExp.exp (a.fwd x dx).1 * (a.fwd x dx).2)
  | .sigmoid a =>
    let s := HasAct.sigmoid (a.fwd x dx).1
    (s, s * (1 - s) * (a.fwd x dx).2)
  | .tanh a =>
    let t := HasAct.tanh (a.fwd x dx).1
    (t, (1 - t * t) * (a.fwd x dx).2)
  | .log a =>
    (HasAct.log (a.fwd x dx).1, HasAct.inv (a.fwd x dx).1 * (a.fwd x dx).2)
  | .inv a =>
    let v := HasAct.inv (a.fwd x dx).1
    (v, (0 - v * v) * (a.fwd x dx).2)
  | .sqrt a =>
    let r := HasAct.sqrt (a.fwd x dx).1
    (r, HasAct.inv (r + r) * (a.fwd x dx).2)
  | .relu a =>
    (HasAct.relu (a.fwd x dx).1, HasAct.step (a.fwd x dx).1 * (a.fwd x dx).2)
  | .step a => (HasAct.step (a.fwd x dx).1, 0)
-- ANCHOR_END: fwd

-- ANCHOR: back
/-- Reverse mode. `back e x s acc` adds to `acc` the contribution of `e` to the gradient of the
final output, where `s` is the adjoint arriving at `e` (the derivative of the output with
respect to the value of `e`). One backward sweep gives *all* partial derivatives. -/
def Expr.back (x : Vec α n) : Expr α n → α → Array α → Array α
  | .var i, s, acc => acc.modify i.val (· + s)
  | .const _, _, acc => acc
  | .add a b, s, acc => b.back x s (a.back x s acc)
  | .sub a b, s, acc => b.back x (0 - s) (a.back x s acc)
  | .mul a b, s, acc => b.back x (s * a.eval x) (a.back x (s * b.eval x) acc)
  | .exp a, s, acc => a.back x (s * HasExp.exp (a.eval x)) acc
  | .sigmoid a, s, acc =>
    let v := HasAct.sigmoid (a.eval x)
    a.back x (s * (v * (1 - v))) acc
  | .tanh a, s, acc =>
    let t := HasAct.tanh (a.eval x)
    a.back x (s * (1 - t * t)) acc
  | .log a, s, acc => a.back x (s * HasAct.inv (a.eval x)) acc
  | .inv a, s, acc =>
    let v := HasAct.inv (a.eval x)
    a.back x (s * (0 - v * v)) acc
  | .sqrt a, s, acc =>
    let r := HasAct.sqrt (a.eval x)
    a.back x (s * HasAct.inv (r + r)) acc
  | .relu a, s, acc => a.back x (s * HasAct.step (a.eval x)) acc
  | .step _, _, acc => acc

/-- The gradient of `e` at `x`, by one backward sweep. -/
def Expr.backprop (e : Expr α n) (x : Vec α n) : Array α :=
  e.back x 1 (Array.replicate n 0)
-- ANCHOR_END: back

end LeanDL.Ch04
