/-!
# Chapter 0 — A tour of Lean 4
-/

namespace LeanDL.Ch00

-- ANCHOR: hello
def double (x : Nat) : Nat := 2 * x

#eval double 21

def average (xs : List Float) : Float := xs.foldl (· + ·) 0 / xs.length.toFloat

#eval average [1.0, 2.0, 6.0]
-- ANCHOR_END: hello

-- ANCHOR: structure
structure Point where
  x : Float
  y : Float

def Point.norm2 (p : Point) : Float := p.x * p.x + p.y * p.y

#eval (Point.mk 3 4).norm2
-- ANCHOR_END: structure

-- ANCHOR: theorem
theorem double_add (a b : Nat) : double (a + b) = double a + double b := by
  unfold double
  omega

example : double 21 = 42 := rfl
-- ANCHOR_END: theorem

-- ANCHOR: generic
/-- Works for every type that has `+`, `*` and a zero. -/
def sumSq {α : Type} [Add α] [Mul α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (fun acc x => acc + x * x) 0

#eval sumSq [1, 2, 3]            -- computed with Nat
#eval sumSq [1.5, 2.5]           -- computed with Float
-- ANCHOR_END: generic

end LeanDL.Ch00
