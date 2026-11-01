import LeanDL.Ch06.Conv

/-! Solutions for the Chapter 6 exercises. -/

namespace LeanDL.Ch06

open Lean.Grind LeanDL.Ch05

variable {α : Type} [CommRing α]

-- ANCHOR: sol1
theorem exercise_conv_zero_solution {m k : Nat} (ker : Vec α (k + 1)) :
    conv1d ker (fun _ : Fin (m + k) => (0 : α)) = fun _ => 0 := by
  funext i
  simp only [conv1d]
  have h : (fun j : Fin (k + 1) => ker j * (0 : α)) = fun _ => 0 := by
    funext j; grind
  rw [h]
  exact vsum_zero
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_conv_double_solution {m k : Nat} (ker : Vec α (k + 1)) (x : Vec α (m + k)) :
    conv1d ker (fun i => x i + x i) = fun i => conv1d ker x i + conv1d ker x i :=
  conv1d_add ker x x
-- ANCHOR_END: sol2

end LeanDL.Ch06