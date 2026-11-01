import LeanDL.Ch14.WorldModel

/-! Solutions for the Chapter 14 exercises. -/

namespace LeanDL.Ch14

open Lean.Grind LeanDL.Ch13

theorem exercise_geom_one_succ_solution {α : Type} [CommRing α] (k : Nat) :
    geom (1 : α) (k + 1) = 1 + geom 1 k := by
  simp only [geom]
  grind

theorem exercise_no_model_error_solution (f fh : Nat → Rat → Rat) (xs ys : Nat → Rat) (L : Rat)
    (hL : 0 ≤ L)
    (hx : ∀ k, xs (k + 1) = f k (xs k)) (hy : ∀ k, ys (k + 1) = fh k (ys k))
    (h0 : ys 0 = xs 0)
    (hε : ∀ k a, absQ (fh k a - f k a) ≤ 0)
    (hlip : ∀ k a b, absQ (fh k a - fh k b) ≤ L * absQ (a - b)) (k : Nat) :
    absQ (ys k - xs k) ≤ 0 := by
  have h := compounding_error f fh xs ys 0 L hL hx hy h0 hε hlip k
  grind

end LeanDL.Ch14