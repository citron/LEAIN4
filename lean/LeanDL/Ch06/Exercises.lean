import LeanDL.Ch06.Conv

/-! Exercises for Chapter 6. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch06

variable {α : Type} [Lean.Grind.CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: convolving the zero signal gives the zero signal. -/
theorem exercise_conv_zero {m k : Nat} (ker : Vec α (k + 1)) :
    conv1d ker (fun _ : Fin (m + k) => (0 : α)) = fun _ => 0 := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: convolution of `x + x` is twice the convolution of `x` (use `conv1d_add`). -/
theorem exercise_conv_double {m k : Nat} (ker : Vec α (k + 1)) (x : Vec α (m + k)) :
    conv1d ker (fun i => x i + x i) = fun i => conv1d ker x i + conv1d ker x i := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch06