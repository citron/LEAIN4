import LeanDL.Ch20.Exercises

/-! Proven solutions for the Chapter 20 exercises. -/

namespace LeanDL.Ch20

open Lean.Grind
open LeanDL.Ch05

-- ANCHOR: sol1
theorem exercise_plain_sgd_solution (lr wd c w g : Rat)
    (hlo : -c ≤ g) (hhi : g ≤ c) :
    recipeStep lr wd c w g = w - lr * g - lr * (wd * w) := by
  unfold recipeStep
  rw [clip_id c g hlo hhi]
  unfold decoupledShrink
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_budget_one_solution (η₀ γ : Rat) (h0 : 0 < γ) (h1 : γ < 1) :
    LeanDL.vsum (fun t : Fin 1 => lrAt η₀ γ (t : Nat)) = η₀ := by
  unfold LeanDL.vsum
  show lrAt η₀ γ (⟨0, by omega⟩ : Fin 1).val + vsum (fun i : Fin 0 => lrAt η₀ γ (i : Nat)) = η₀
  have h0sum : LeanDL.vsum (fun i : Fin 0 => lrAt η₀ γ (i : Nat)) = 0 := by
    unfold LeanDL.vsum
    grind
  rw [h0sum]
  unfold lrAt
  show η₀ * powN γ 0 + 0 = η₀
  have hpow : powN γ 0 = (1 : Rat) := by
    unfold powN
    grind
  rw [hpow]
  grind
-- ANCHOR_END: sol2

end LeanDL.Ch20
