/-!
# Scalars

Code in this course is written once, generically over a scalar type `α`.
* To *run* it we instantiate `α := Float`.
* To *prove* things we instantiate `α` with an exact type (`Int`, `Rat`) or an abstract
  ordered ring, using the algebra classes that ship with Lean's `grind` tactic.
-/

namespace LeanDL

/-- `0 ≤ x * x` for rationals: the base inequality every variance argument uses.
Lives in Core so later chapters (Ch02, Ch16) import it, not the reverse. -/
theorem sq_nonneg (x : Rat) : 0 ≤ x * x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (a := -x) (b := -x) (by grind) (by grind)
    grind

-- ANCHOR: abs_laws
/-- `|x·y| = |x|·|y|` for rationals. -/
theorem abs_mul (x y : Rat) : Rat.abs (x * y) = Rat.abs x * Rat.abs y := by
  rcases Rat.le_total (a := 0) (b := x) with hx | hx
  · rcases Rat.le_total (a := 0) (b := y) with hy | hy
    · have hxy : 0 ≤ x * y := Rat.mul_nonneg hx hy
      grind [Rat.abs.eq_1]
    · have hxy : x * y ≤ 0 := by
        have h : x * y ≤ x * 0 := Rat.mul_le_mul_of_nonneg_left hy hx
        have : x * 0 = 0 := by grind
        grind
      grind [Rat.abs.eq_1]
  · rcases Rat.le_total (a := 0) (b := y) with hy | hy
    · have hxy : x * y ≤ 0 := by
        have h : x * y ≤ 0 * y := Rat.mul_le_mul_of_nonneg_right hx hy
        have : 0 * y = 0 := by grind
        grind
      grind [Rat.abs.eq_1]
    · have hx' : 0 ≤ -x := by grind
      have hy' : 0 ≤ -y := by grind
      have hxy : 0 ≤ (-x) * (-y) := Rat.mul_nonneg hx' hy'
      have : (-x) * (-y) = x * y := by grind
      grind [Rat.abs.eq_1]

/-- The triangle inequality. -/
theorem abs_add_le (x y : Rat) : Rat.abs (x + y) ≤ Rat.abs x + Rat.abs y := by
  grind [Rat.abs.eq_1]

/-- Absolute values are nonnegative. -/
theorem abs_nonneg (x : Rat) : 0 ≤ Rat.abs x := by
  grind [Rat.abs.eq_1]

/-- The interval form of “non-expansive”: `-1 ≤ c ≤ 1` means `|c| ≤ 1`. -/
theorem abs_le_one_of_interval (c : Rat) (lo : -1 ≤ c) (hi : c ≤ 1) : Rat.abs c ≤ 1 := by
  grind [Rat.abs.eq_1]
-- ANCHOR_END: abs_laws

-- ANCHOR: drift_bound
/-- **Error accumulation under a non-expansive map.** Suppose an exact run
follows `w' = c · w` (`|c| ≤ 1`: e.g. `c = 1 − ηa` in the stable SGD range)
and a perturbed run — the floating-point one — follows `v' = c · v + eₜ`
with per-step rounding errors `|eₜ| ≤ ε`, starting from the same point.
Then after `t` steps the gap grows *at most linearly*: `|v_t − w_t| ≤ t·ε`.
Rounding cannot amplify the drift while the exact dynamics are stable:
this is the bridge between the exact theorems and the `Float` demos. -/
theorem drift_bound (c : Rat) (hc : Rat.abs c ≤ 1) (ε : Rat) (hε : 0 ≤ ε)
    (v w : Nat → Rat) (e : Nat → Rat) (h0 : v 0 = w 0)
    (hv : ∀ t, v (t + 1) = c * v t + e t)
    (he : ∀ t, Rat.abs (e t) ≤ ε)
    (hw : ∀ t, w (t + 1) = c * w t) :
    ∀ t, Rat.abs (v t - w t) ≤ (t : Rat) * ε := by
  intro t
  induction t with
  | zero =>
      have hz : (0 : Nat) = (0 : Rat) := rfl
      rw [hz, h0]
      show Rat.abs (w 0 - w 0) ≤ 0 * ε
      grind
  | succ t ih =>
      have hstep : v (t + 1) - w (t + 1) = c * (v t - w t) + e t := by
        rw [hv, hw]; grind
      rw [hstep]
      have h1 : Rat.abs (c * (v t - w t) + e t) ≤ Rat.abs (c * (v t - w t)) + Rat.abs (e t) :=
        abs_add_le _ _
      have h2 : Rat.abs (c * (v t - w t)) = Rat.abs c * Rat.abs (v t - w t) := abs_mul _ _
      have h4 : Rat.abs c * Rat.abs (v t - w t) ≤ Rat.abs c * ((t : Rat) * ε) :=
        Rat.mul_le_mul_of_nonneg_left ih (abs_nonneg c)
      have h5 : Rat.abs c * ((t : Rat) * ε) ≤ 1 * ((t : Rat) * ε) :=
        Rat.mul_le_mul_of_nonneg_right hc
          (Rat.mul_nonneg (by exact_mod_cast Nat.zero_le t) hε)
      have h6 : (t.succ : Rat) * ε = (t : Rat) * ε + ε := by
        push_cast
        grind
      have h7 : 1 * ((t : Rat) * ε) = (t : Rat) * ε := by grind
      rw [h2] at h1
      rw [h6]
      rw [h7] at h5
      grind

/-- The perturbed run tracks the exact one: when the exact run converges
(e.g. `c = 0`, the critical SGD step `ηa = 1`, where `w t = 0` for `t ≥ 1`),
the floating-point run stays within `t·ε` of the minimiser. -/
theorem drift_abs (c : Rat) (hc : Rat.abs c ≤ 1) (ε : Rat) (hε : 0 ≤ ε)
    (v w : Nat → Rat) (e : Nat → Rat) (h0 : v 0 = w 0)
    (hv : ∀ t, v (t + 1) = c * v t + e t)
    (he : ∀ t, Rat.abs (e t) ≤ ε)
    (hw : ∀ t, w (t + 1) = c * w t) (t : Nat) :
    Rat.abs (v t) ≤ (t : Rat) * ε + Rat.abs (w t) := by
  have h := drift_bound c hc ε hε v w e h0 hv he hw t
  have : v t = (v t - w t) + w t := by grind
  rw [this]
  have := abs_add_le (v t - w t) (w t)
  grind
-- ANCHOR_END: drift_bound

-- ANCHOR: hasexp
/-- Types with an exponential function. -/
class HasExp (α : Type) where
  exp : α → α

instance : HasExp Float := ⟨Float.exp⟩
-- ANCHOR_END: hasexp

/-- Laws that `exp` must satisfy; `Float` does not satisfy them exactly, exact models do. -/
class LawfulExp (α : Type) [Lean.Grind.CommRing α] [HasExp α] : Prop where
  exp_add : ∀ x y : α, HasExp.exp (x + y) = HasExp.exp x * HasExp.exp y
  exp_zero : HasExp.exp (0 : α) = 1

end LeanDL
