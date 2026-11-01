/-!
# Scalars

Code in this course is written once, generically over a scalar type `α`.
* To *run* it we instantiate `α := Float`.
* To *prove* things we instantiate `α` with an exact type (`Int`, `Rat`) or an abstract
  ordered ring, using the algebra classes that ship with Lean's `grind` tactic.
-/

namespace LeanDL

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
