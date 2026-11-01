import LeanDL.Ch14.WorldModel

/-! Exercises for Chapter 14. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch14

open Lean.Grind LeanDL.Ch13

-- ANCHOR: ex1
/-- Exercise 1: for `L = 1` the geometric sum grows by one at each step. -/
theorem exercise_geom_one_succ {α : Type} [CommRing α] (k : Nat) :
    geom (1 : α) (k + 1) = 1 + geom 1 k := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: a perfect one-step model (`ε = 0`) gives perfect imagined rollouts. -/
theorem exercise_no_model_error (f fh : Nat → Rat → Rat) (xs ys : Nat → Rat) (L : Rat)
    (hL : 0 ≤ L)
    (hx : ∀ k, xs (k + 1) = f k (xs k)) (hy : ∀ k, ys (k + 1) = fh k (ys k))
    (h0 : ys 0 = xs 0)
    (hε : ∀ k a, absQ (fh k a - f k a) ≤ 0)
    (hlip : ∀ k a b, absQ (fh k a - fh k b) ≤ L * absQ (a - b)) (k : Nat) :
    absQ (ys k - xs k) ≤ 0 := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch14