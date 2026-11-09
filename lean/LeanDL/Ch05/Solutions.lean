import LeanDL.Ch05.Kit
import LeanDL.Ch05.Optim
import LeanDL.Core.Ieee754

/-! Solutions for the Chapter 5 exercises. -/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: sol1
theorem exercise_sgd_two_steps_solution (η a w : α) :
    sgdQuad η a w 2 = (1 - η * a) * ((1 - η * a) * w) := by
  rw [sgdQuad_closed η a 2 w]
  simp only [powN]
  grind
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_ema_first_solution (β g : α) : ema β g 1 = (1 - β) * g := by
  simp only [ema]
  grind
-- ANCHOR_END: sol2


-- ANCHOR: sol3
theorem exercise_clip_idem_solution (c x : Rat) (hc : 0 <= c) :
    clip c (clip c x) = clip c x := by
  by_cases h1 : x < -c
  . have heq : clip c x = -c := by
      unfold clip
      split <;> grind
    rw [heq]
    unfold clip
    split <;> grind
  . by_cases h2 : c < x
    . have heq : clip c x = c := by
        unfold clip
        split <;> grind
      rw [heq]
      unfold clip
      split <;> grind
    . have heq : clip c x = x := by
        unfold clip
        split <;> grind
      rw [heq]
      unfold clip
      split <;> grind
-- ANCHOR_END: sol3

-- ANCHOR: sol4
theorem exercise_clip_fixed_solution (c x : Rat) (hc : 0 <= c) :
    clip c x = x <-> -c <= x /\ x <= c := by
  constructor
  . intro h
    by_cases h1 : x < -c
    . have heq : clip c x = -c := by
        unfold clip
        split <;> grind
      rw [heq] at h
      grind
    . by_cases h2 : c < x
      . have heq : clip c x = c := by
          unfold clip
          split <;> grind
        rw [heq] at h
        grind
      . exact ⟨by grind, by grind⟩
  . rintro ⟨h1, h2⟩
    unfold clip
    split <;> grind
-- ANCHOR_END: sol4


-- ANCHOR: sol5
theorem exercise_fixed_grid_solution (p k : Nat) :
    LeanDL.Core.Ieee754.fixedGrid p ((k : Rat) / (2 : Rat) ^ p) =
      (k : Rat) / (2 : Rat) ^ p := by
  unfold LeanDL.Core.Ieee754.fixedGrid
  have hp : (0 : Rat) < (2 : Rat) ^ p := LeanDL.Core.Ieee754.pow2_pos p
  have hmul : ((k : Rat) / (2 : Rat) ^ p) * (2 : Rat) ^ p = (k : Rat) := by
    push_cast
    grind [Rat.div_def]
  have hfl : Rat.floor ((k : Rat) + 1 / 2) = (k : Int) := by
    have h1 : (k : Int) ≤ Rat.floor ((k : Rat) + 1 / 2) := by
      rw [Rat.le_floor_iff]
      push_cast
      grind
    have h2 : Rat.floor ((k : Rat) + 1 / 2) < (k : Int) + 1 := by
      rw [Rat.floor_lt_iff]
      push_cast
      grind
    omega
  rw [hmul, hfl]
  push_cast
  grind
-- ANCHOR_END: sol5

end LeanDL.Ch05