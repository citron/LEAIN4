import LeanDL.Ch05.Kit
import LeanDL.Ch05.Optim
import LeanDL.Core.Ieee754

/-! Exercises for Chapter 5. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch05

open Lean.Grind

variable {α : Type} [CommRing α]

-- ANCHOR: ex1
/-- Exercise 1: two steps of gradient descent on `a w² / 2` multiply `w` by `1 - η a` twice. -/
theorem exercise_sgd_two_steps (η a w : α) :
    sgdQuad η a w 2 = (1 - η * a) * ((1 - η * a) * w) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: the first value of the moving average is `(1 - β) g`. -/
theorem exercise_ema_first (β g : α) : ema β g 1 = (1 - β) * g := by
  sorry
-- ANCHOR_END: ex2


-- ANCHOR: ex3
/-- Exercise 3: clipping is idempotent — clipping an already clipped
gradient changes nothing. -/
theorem exercise_clip_idem (c x : Rat) (hc : 0 <= c) :
    clip c (clip c x) = clip c x := by
  sorry
-- ANCHOR_END: ex3

-- ANCHOR: ex4
/-- Exercise 4: clipping is the identity exactly on its box. -/
theorem exercise_clip_fixed (c x : Rat) (hc : 0 <= c) :
    clip c x = x <-> -c <= x /\ x <= c := by
  sorry
-- ANCHOR_END: ex4


-- ANCHOR: ex5
/-- Exercise 5 (IEEE-754): on the fixed grid of step `2⁻ᵖ`, the
constructive rounding `fixedGrid p x = floor (x · 2ᵖ + ½) / 2ᵖ`
fixes the grid point `k · 2⁻ᵖ`. Prove it: show
`floor (k + ½) = k` from `Rat.le_floor_iff` and `Rat.floor_lt_iff`,
then close the division with `push_cast` and `grind [Rat.div_def]`
(remember `0 < 2 ^ p`). -/
theorem exercise_fixed_grid (p k : Nat) :
    LeanDL.Core.Ieee754.fixedGrid p ((k : Rat) / (2 : Rat) ^ p) =
      (k : Rat) / (2 : Rat) ^ p := by
  sorry
-- ANCHOR_END: ex5

end LeanDL.Ch05