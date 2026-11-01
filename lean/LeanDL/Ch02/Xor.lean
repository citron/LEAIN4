import LeanDL.Ch01.Neuron

/-!
# Chapter 2 — The perceptron, and why XOR froze AI

Part 1: no single neuron computes XOR (the 1969 Minsky–Papert observation).
Part 2: the perceptron learning rule and Novikoff's mistake bound.
-/

namespace LeanDL.Ch02

open Lean.Grind LeanDL.Ch01

/-! ## Part 1 — XOR is not computable by one neuron -/

-- ANCHOR: xor_def
/-- A bit as a scalar: `false ↦ 0`, `true ↦ 1`. -/
def bit {α : Type} [OfNat α 0] [OfNat α 1] (b : Bool) : α := if b then 1 else 0

/-- The XOR truth table as a specification. -/
def XorSpec {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1] [LE α]
    [DecidableRel (α := α) (· ≤ ·)] (N : Neuron α 2) : Prop :=
  ∀ a b : Bool, N.fire step (v2 (bit a) (bit b)) = (bit (a ^^ b) : α)
-- ANCHOR_END: xor_def

-- ANCHOR: xor_impossible
/-- No threshold neuron computes XOR — over `Int`, `Rat`, or any linearly ordered ring. -/
theorem xor_impossible {α : Type} [CommRing α] [LE α] [LT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] [OrderedRing α] [DecidableRel (α := α) (· ≤ ·)]
    (N : Neuron α 2) : ¬ XorSpec N := by
  intro h
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp only [Neuron.fire, Neuron.preact, Vec.dot, v2, bit, step] at h00 h01 h10 h11
  simp at h00 h01 h10 h11
  grind
-- ANCHOR_END: xor_impossible

example (N : Neuron Rat 2) : ¬ XorSpec N := xor_impossible N

end LeanDL.Ch02
