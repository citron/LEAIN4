import LeanDL.Ch16.Tools
import LeanDL.Core.Theory

/-! Solutions for the Chapter 16 exercises. -/

namespace LeanDL.Ch16

open Lean.Grind
open Dist

variable [LawfulLog]

-- ANCHOR: sol1
theorem exercise_expect_sub_solution {n : Nat} (p : Dist n) (f g : Vec Rat n) :
    p.expect (fun i => f i - g i) = p.expect f - p.expect g := by
  show Vec.dot p.w (fun i => f i - g i) = Vec.dot p.w f - Vec.dot p.w g
  exact dot_sub _ _ _
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_kl_single_solution (p q : Dist 1) : p.kl q = 0 := by
  -- On one point, `sum1` unfolds to `w 0 · 1 = 1`: the only weight is 1.
  have hp0 : p.w 0 = 1 := by
    have := p.sum1
    simp only [Vec.dot, Rat.mul_one] at this
    rw [← Rat.add_zero (p.w 0)]
    exact this
  have hq0 : q.w 0 = 1 := by
    have := q.sum1
    simp only [Vec.dot, Rat.mul_one] at this
    rw [← Rat.add_zero (q.w 0)]
    exact this
  have hl : LawfulLog.log (1 : Rat) - LawfulLog.log 1 = 0 := by
    rw [log_one]
    grind
  show Vec.dot p.w (fun i => LawfulLog.log (p.w i) - LawfulLog.log (q.w i)) = 0
  simp only [Vec.dot]
  rw [hp0, hq0, hl]
  grind
-- ANCHOR_END: sol2

-- ANCHOR: sol3
theorem exercise_variance_const_solution {n : Nat} (p : Dist n) (c : Rat) :
    p.variance (fun _ => c) = 0 := by
  have h1 : p.expect (fun _ => c * c) = c * c := expect_const p (c * c)
  have h2 : p.expect (fun _ => c) = c := expect_const p c
  have hrew : (fun i : Fin n => (fun _ => c) i * (fun _ => c) i)
      = (fun _ => c * c) := by
    funext i
    grind
  simp only [variance, hrew, h1, h2]
  grind
-- ANCHOR_END: sol3

-- ANCHOR: sol4
theorem exercise_entropy_single_solution (p : Dist 1) : p.entropy = 0 := by
  have hp0 : p.w 0 = 1 := by
    have := p.sum1
    simp only [Vec.dot, Rat.mul_one] at this
    rw [← Rat.add_zero (p.w 0)]
    exact this
  show Vec.dot p.w (fun i => -LawfulLog.log (p.w i)) = 0
  simp only [Vec.dot]
  rw [hp0, log_one]
  grind
-- ANCHOR_END: sol4

-- ANCHOR: sol5
theorem exercise_variance_single_solution {n : Nat} (p : Dist 1) (f : Fin 1 → Vec Rat n)
    (i : Fin n) :
    Vec.dot p.w (fun k => (f k i - p.wavg f i) * (f k i - p.wavg f i)) = 0 := by
  have hp0 : p.w 0 = 1 := by
    have := p.sum1
    simp only [Vec.dot, Rat.mul_one] at this
    rw [← Rat.add_zero (p.w 0)]
    exact this
  -- With one hypothesis of weight 1, the average is that hypothesis itself.
  have hmean : p.wavg f i = f 0 i := by
    simp only [wavg, Vec.dot, hp0, Rat.one_mul, Rat.add_zero]
  simp only [Vec.dot, hp0, hmean, Rat.sub_self, Rat.mul_zero]
  grind
-- ANCHOR_END: sol5

-- ANCHOR: sol6
theorem exercise_coin_mean_solution :
    LeanDL.Theory.coin.expect (fun i => (i.val : Rat)) = 1 / 2 := by
  rw [LeanDL.Theory.coin_expect_avg]
  show ((0 : Rat) + 1) / 2 = 1 / 2
  grind
-- ANCHOR_END: sol6

-- ANCHOR: sol7
theorem exercise_nfl_random_solution (q : Dist 2) :
    q.expect (fun y => LeanDL.Theory.coin.expect (LeanDL.Theory.err y)) = 1 / 2 := by
  have h : (fun y => LeanDL.Theory.coin.expect (LeanDL.Theory.err y))
      = (fun _ => (1 / 2 : Rat)) := by
    funext y
    exact LeanDL.Theory.nfl_coin y
  rw [h, q.expect_const]
-- ANCHOR_END: sol7

end LeanDL.Ch16
