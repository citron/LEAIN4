/-!
# Scalars

Code in this course is written once, generically over a scalar type `α`.
* To *run* it we instantiate `α := Float`.
* To *prove* things we instantiate `α` with an exact type (`Int`, `Rat`) or an abstract
  ordered ring, using the algebra classes that ship with Lean's `grind` tactic.
-/

namespace LeanDL

/-- `0 ≤ x * x` for rationals: the base inequality every variance argument uses.
Lives in Core so later chapters (Ch02, Ch16) import it, not the reverse. -/
theorem sq_nonneg (x : Rat) : 0 ≤ x * x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (a := -x) (b := -x) (by grind) (by grind)
    grind

-- ANCHOR: hasexp
/-- Types with an exponential function. -/
class HasExp (α : Type) where
  exp : α → α

instance : HasExp Float := ⟨Float.exp⟩
-- ANCHOR_END: hasexp

/-- Laws that `exp` must satisfy; `Float` does not satisfy them exactly, exact models do. -/
class LawfulExp (α : Type) [Lean.Grind.CommRing α] [HasExp α] : Prop where
  exp_add : ∀ x y : α, HasExp.exp (x + y) = HasExp.exp x * HasExp.exp y
  exp_zero : HasExp.exp (0 : α) = 1

end LeanDL
