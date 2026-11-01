import LeanDL.Ch02.Xor

/-! Exercises for Chapter 2. Replace each `sorry`. -/

namespace LeanDL.Ch02

open Lean.Grind LeanDL.Ch01

-- ANCHOR: ex1
/-- Exercise: XNOR is the negation of XOR; no single neuron computes it either. -/
def XnorSpec {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] [LE α]
    [DecidableRel (α := α) (· ≤ ·)] (N : Neuron α 2) : Prop :=
  ∀ a b : Bool, N.fire step (v2 (bit a) (bit b)) = (bit (a == b) : α)

theorem exercise_xnor {α : Type} [CommRing α] [LE α] [LT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] [OrderedRing α] [DecidableRel (α := α) (· ≤ ·)]
    (N : Neuron α 2) : ¬ XnorSpec N := by
  sorry
-- ANCHOR_END: ex1

end LeanDL.Ch02
