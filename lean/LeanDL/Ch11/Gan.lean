import LeanDL.Ch04.Correct
import LeanDL.Ch02.Perceptron

/-!
# Chapter 11 — GANs: the optimal discriminator

At a point `x` where the data density is `a` and the generator density is `b`, the
discriminator `d ∈ (0, 1)` should say how likely `x` is to be real. We prove what the best
answer is, for the original (logarithmic) loss and for the least-squares loss.
-/

namespace LeanDL.Ch11

open Lean.Grind LeanDL.Ch04

variable {α : Type}

section LeastSquares

-- ANCHOR: lsgan
/-- Least-squares GAN: the discriminator is pushed to `1` on real data (weight `a`) and
to `0` on generated data (weight `b`). -/
def lsLoss [Add α] [Sub α] [Mul α] [OfNat α 1] (a b d : α) : α := a * ((d - 1) * (d - 1)) + b * (d * d)

/-- The claimed optimum: the fraction of real data at this point. -/
def dStar [Div α] [Add α] (a b : α) : α := a / (a + b)

section Field

variable [Field α]

/-- Completing the square: `loss(d) = loss(d*) + (a + b)(d - d*)²`. -/
theorem lsLoss_sq (a b d : α) (h : a + b ≠ 0) :
    lsLoss a b d = lsLoss a b (dStar a b) + (a + b) * ((d - dStar a b) * (d - dStar a b)) := by
  simp only [lsLoss, dStar]
  grind

/-- At the optimum the loss is `a b / (a + b)`. -/
theorem lsLoss_value (a b : α) (h : a + b ≠ 0) : lsLoss a b (dStar a b) = a * b / (a + b) := by
  simp only [lsLoss, dStar]
  grind

/-- If generator and data agree (`a = b`, `2a ≠ 0`) the best discriminator answers `1/2`: it cannot
tell real from fake. -/
theorem dStar_equal (a : α) (h : a + a ≠ 0) : dStar a a * 2 = 1 := by
  simp only [dStar]
  grind

end Field

open LeanDL.Ch02 in
/-- **The optimal discriminator.** For non-negative densities `a`, `b` with `a + b > 0`, no
value `d` does better than `a / (a + b)`. -/
theorem lsLoss_min (a b d : Rat) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : 0 < a + b) :
    lsLoss a b (dStar a b) ≤ lsLoss a b d := by
  have h := lsLoss_sq a b d (by grind)
  have hsq := sq_nonneg (d - dStar a b)
  have : 0 ≤ (a + b) * ((d - dStar a b) * (d - dStar a b)) := Rat.mul_nonneg (by grind) hsq
  rw [h]
  have key := (Rat.add_le_add_left (a := 0) (b := (a + b) * ((d - dStar a b) * (d - dStar a b)))
    (c := lsLoss a b (dStar a b))).mpr this
  rwa [Rat.add_zero] at key
-- ANCHOR_END: lsgan

end LeastSquares

section Log

variable [Field α] [HasAct α]

-- ANCHOR: log_gan
/-- The original GAN objective at one point, as an expression in `d`:
`a log d + b log (1 - d)`. -/
def ganObj (a b : α) : Expr α 1 :=
  .add (.mul (.const a) (.log (.var 0)))
    (.mul (.const b) (.log (.sub (.const 1) (.var 0))))

/-- **The optimal discriminator is a critical point of the original objective.** At
`d = a / (a + b)` the derivative (computed by verified backpropagation) vanishes. We assume the
abstract `inv` of `HasAct` is the field inverse. -/
theorem ganObj_critical (hinv : ∀ x : α, HasAct.inv x = x⁻¹) (a b : α)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) (x : Vec α 1) (hx : x 0 = a / (a + b)) :
    ((ganObj a b).backprop x).getD 0 0 = 0 := by
  have := backprop_correct x (ganObj a b) 0
  simp only [Fin.val_zero] at this
  rw [this]
  simp only [ganObj, Expr.deriv, Expr.eval, hinv, hx]
  have h1 : 1 - a / (a + b) = b / (a + b) := by grind
  rw [h1]
  grind
-- ANCHOR_END: log_gan

end Log

end LeanDL.Ch11
