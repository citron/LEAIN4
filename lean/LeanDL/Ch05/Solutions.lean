import LeanDL.Ch05.Kit
import LeanDL.Ch05.Optim

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

end LeanDL.Ch05