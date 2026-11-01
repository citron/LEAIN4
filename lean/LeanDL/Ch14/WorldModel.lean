import LeanDL.Ch13.Rl

/-!
# Chapter 14 — World models: why imagined rollouts drift

A world model predicts the next state from the current state and action. Used to *imagine*
trajectories, its one-step error is fed back as input at every later step. We prove how a one-step
error `ε` and a Lipschitz constant `L` of the model turn into a `k`-step error.
-/

namespace LeanDL.Ch14

open Lean.Grind LeanDL.Ch13

section Geom

variable {α : Type} [CommRing α]

-- ANCHOR: geom
/-- `geom L k = 1 + L + L² + … + L^(k-1)`. -/
def geom (L : α) : Nat → α
  | 0 => 0
  | k + 1 => 1 + L * geom L k

/-- Closed form of the geometric sum: `(L - 1) · geom L k = Lᵏ - 1`. -/
theorem geom_closed (L : α) (k : Nat) : (L - 1) * geom L k = pw L k - 1 := by
  induction k with
  | zero => simp only [geom, pw]; grind
  | succ k ih => simp only [geom, pw]; grind
-- ANCHOR_END: geom

end Geom

/-- Absolute value on the rationals. -/
def absQ (x : Rat) : Rat := if x < 0 then -x else x

theorem absQ_nonneg (x : Rat) : 0 ≤ absQ x := by
  unfold absQ; split <;> grind

theorem absQ_add_le (x y : Rat) : absQ (x + y) ≤ absQ x + absQ y := by
  unfold absQ; split <;> split <;> split <;> grind

theorem geom_nonneg (L : Rat) (hL : 0 ≤ L) (k : Nat) : 0 ≤ geom L k := by
  induction k with
  | zero => simp only [geom]; grind
  | succ k ih =>
    simp only [geom]
    have := Rat.mul_nonneg hL ih
    grind

-- ANCHOR: compounding
/-- Powers of a non-negative number are non-negative. -/
theorem pw_nonneg (L : Rat) (hL : 0 ≤ L) (k : Nat) : 0 ≤ pw L k := by
  induction k with
  | zero => simp only [pw]; grind
  | succ k ih => simp only [pw]; exact Rat.mul_nonneg hL ih
/-- **Compounding error of imagined rollouts.**

`xs` is the true trajectory (`x_{k+1} = f_k(x_k)`, the action at step `k` being absorbed into `f_k`),
`ys` the imagined one under the model (`y_{k+1} = f̂_k(y_k)`), both starting at the same state.
If the model is wrong by at most `ε` in one step, and is `L`-Lipschitz, then after `k` steps the
imagined state is off by at most `ε · (1 + L + … + L^(k-1))`. -/
theorem compounding_error (f fh : Nat → Rat → Rat) (xs ys : Nat → Rat) (ε L : Rat)
    (hL : 0 ≤ L)
    (hx : ∀ k, xs (k + 1) = f k (xs k)) (hy : ∀ k, ys (k + 1) = fh k (ys k))
    (h0 : ys 0 = xs 0)
    (hε : ∀ k a, absQ (fh k a - f k a) ≤ ε)
    (hlip : ∀ k a b, absQ (fh k a - fh k b) ≤ L * absQ (a - b)) (k : Nat) :
    absQ (ys k - xs k) ≤ ε * geom L k := by
  induction k with
  | zero => simp only [geom, h0]; unfold absQ; split <;> grind
  | succ k ih =>
    rw [hx, hy]
    have split_ : fh k (ys k) - f k (xs k) = (fh k (ys k) - fh k (xs k)) + (fh k (xs k) - f k (xs k)) := by
      grind
    rw [split_]
    have h1 := absQ_add_le (fh k (ys k) - fh k (xs k)) (fh k (xs k) - f k (xs k))
    have h2 := hlip k (ys k) (xs k)
    have h3 := hε k (xs k)
    have h4 := Rat.mul_le_mul_of_nonneg_left ih hL
    simp only [geom]
    grind

/-- With a contractive model (`L < 1`) the imagined error stays bounded: `(1 - L)·error ≤ ε`. -/
theorem compounding_bounded (f fh : Nat → Rat → Rat) (xs ys : Nat → Rat) (ε L : Rat)
    (hL : 0 ≤ L) (hL1 : L < 1) (hε0 : 0 ≤ ε)
    (hx : ∀ k, xs (k + 1) = f k (xs k)) (hy : ∀ k, ys (k + 1) = fh k (ys k))
    (h0 : ys 0 = xs 0)
    (hε : ∀ k a, absQ (fh k a - f k a) ≤ ε)
    (hlip : ∀ k a b, absQ (fh k a - fh k b) ≤ L * absQ (a - b)) (k : Nat) :
    (1 - L) * absQ (ys k - xs k) ≤ ε := by
  have hmain := compounding_error f fh xs ys ε L hL hx hy h0 hε hlip k
  have hg := geom_closed L k
  have hp : 0 ≤ pw L k := pw_nonneg L hL k
  have h5 := Rat.mul_le_mul_of_nonneg_left hmain (show 0 ≤ 1 - L by grind)
  have h6 : (1 - L) * (ε * geom L k) = ε * (1 - pw L k) := by grind
  have h7 : ε * (1 - pw L k) ≤ ε := by
    have := Rat.mul_nonneg hε0 hp
    grind
  grind
-- ANCHOR_END: compounding

end LeanDL.Ch14
