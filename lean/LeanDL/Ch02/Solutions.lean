import LeanDL.Ch02.Exercises

/-! Solutions for the Chapter 2 exercises. -/

namespace LeanDL.Ch02

open Lean.Grind LeanDL.Ch01

/-- No threshold neuron computes XNOR either: the four constraints are
`b ≥ 0`, `w₁ + b < 0`, `w₂ + b < 0`, `w₁ + w₂ + b ≥ 0`, which are jointly unsatisfiable. -/
theorem exercise_xnor_solution {α : Type} [CommRing α] [LE α] [LT α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] [OrderedRing α] [DecidableRel (α := α) (· ≤ ·)]
    (N : Neuron α 2) : ¬ XnorSpec N := by
  intro h
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp only [Neuron.fire, Neuron.preact, Vec.dot, v2, bit, step] at h00 h01 h10 h11
  simp at h00 h01 h10 h11
  grind

end LeanDL.Ch02
