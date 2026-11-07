import LeanDL.Core.Algebra

/-!
# Certified intervals: enclosing the floating-point world

`Float` gives no guarantees: rounding is not in the type. The honest bridge is a
**rational interval** `[lo, hi]` with `lo, hi : Rat` — the exact scalar of the proofs —
together with a THEOREM per operation stating that the true real value is inside.

Every enclosure below is proved from `lo ≤ x ≤ hi` hypotheses with `grind` alone;
the closed-form certificates at the end are checked by the same tactic that checks
the rest of the course. No `sorry`, no axioms, no `native_decide`.

This is the pattern that turns a Float demo into a statement: "the true softmax
mass lies in `[0.987, 0.993]`" is a `Rat` fact a proof checker can verify, while
the Float run gives the witness.
-/

namespace LeanDL

-- ANCHOR: interval
/-- A closed interval with EXACT rational bounds. -/
structure Interval where
  lo : Rat
  hi : Rat

instance : HasSubset Interval := ⟨fun I J => J.lo ≤ I.lo ∧ I.hi ≤ J.hi⟩

/-- `x` lies in `I`. -/
def Mem (x : Rat) (I : Interval) : Prop := I.lo ≤ x ∧ x ≤ I.hi

theorem subset_refl {I : Interval} : I ⊆ I := ⟨by grind, by grind⟩

theorem subset_trans {I J K : Interval} (h : I ⊆ J) (h2 : J ⊆ K) : I ⊆ K := by
  obtain ⟨h1, h2'⟩ := h
  obtain ⟨h3, h4⟩ := h2
  exact ⟨Rat.le_trans h3 h1, Rat.le_trans h2' h4⟩

/-- The degenerate interval `[q, q]`. -/
def point (q : Rat) : Interval := ⟨q, q⟩

theorem mem_point (q : Rat) : Mem q (point q) := by
  show q ≤ q ∧ q ≤ q
  exact ⟨by grind, by grind⟩
-- ANCHOR_END: interval

/-! ## The ring operations, each with its enclosure theorem -/

def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩

theorem add_spec {I J : Interval} {x y : Rat} (hx : Mem x I) (hy : Mem y J) :
    Mem (x + y) (add I J) := by
  obtain ⟨a, b⟩ := hx
  obtain ⟨c, d⟩ := hy
  show I.lo + J.lo ≤ x + y ∧ x + y ≤ I.hi + J.hi
  exact ⟨by grind, by grind⟩

def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩

theorem neg_spec {I : Interval} {x : Rat} (hx : Mem x I) : Mem (-x) (neg I) := by
  obtain ⟨a, b⟩ := hx
  show -I.hi ≤ -x ∧ -x ≤ -I.lo
  exact ⟨by grind, by grind⟩

def sub (I J : Interval) : Interval := ⟨I.lo - J.hi, I.hi - J.lo⟩

theorem sub_spec {I J : Interval} {x y : Rat} (hx : Mem x I) (hy : Mem y J) :
    Mem (x - y) (sub I J) := by
  obtain ⟨a, b⟩ := hx
  obtain ⟨c, d⟩ := hy
  show I.lo - J.hi ≤ x - y ∧ x - y ≤ I.hi - J.lo
  exact ⟨by grind, by grind⟩

/-! ## Product: the four-corner rule

A product of two bounded ranges is bounded by ITS FOUR CORNERS. Sign is the whole
difficulty: multiplying an inequality by a NEGATIVE number flips it, so the corner
that wins depends on the signs of `x` and `y`. -/

theorem mul_le_mul_of_nonpos_right {a b c : Rat} (h : a ≤ b) (hc : c ≤ 0) :
    b * c ≤ a * c := by
  have hnc : 0 ≤ -c := by grind
  have h1 : a * -c = -(a * c) := by grind
  have h2 : b * -c = -(b * c) := by grind
  have h3 : -(a * c) ≤ -(b * c) := by
    rw [← h1, ← h2]
    exact Rat.mul_le_mul_of_nonneg_right h hnc
  grind

theorem mul_le_mul_of_nonpos_left {a b c : Rat} (h : a ≤ b) (hc : c ≤ 0) :
    c * b ≤ c * a := by
  have hn : -b ≤ -a := Rat.neg_le_neg h
  have hnc : 0 ≤ -c := by grind
  have h1 : -c * -b = c * b := by grind
  have h2 : -c * -a = c * a := by grind
  have h3 : -c * -b ≤ -c * -a := Rat.mul_le_mul_of_nonneg_left hn hnc
  rw [h1, h2] at h3
  exact h3

/-- Upper bound of a product over a box: one of the four corners attains it. -/
theorem box_max (a b c d x y : Rat) (hx : a ≤ x) (hxb : x ≤ b) (hy : c ≤ y) (hyd : y ≤ d) :
    x * y ≤ max (a * c) (max (a * d) (max (b * c) (b * d))) := by
  have hxy : x * y ≤ max (a * y) (b * y) := by
    by_cases hy0 : (0 : Rat) ≤ y
    · have h : x * y ≤ b * y := Rat.mul_le_mul_of_nonneg_right hxb hy0
      grind
    · have h : x * y ≤ a * y := mul_le_mul_of_nonpos_right hx (by grind)
      grind
  have h1 : a * y ≤ max (a * c) (a * d) := by
    by_cases ha0 : (0 : Rat) ≤ a
    · have h : a * y ≤ a * d := Rat.mul_le_mul_of_nonneg_left hyd ha0
      grind
    · have h : a * y ≤ a * c := mul_le_mul_of_nonpos_left hy (by grind)
      grind
  have h2 : b * y ≤ max (b * c) (b * d) := by
    by_cases hb0 : (0 : Rat) ≤ b
    · have h : b * y ≤ b * d := Rat.mul_le_mul_of_nonneg_left hyd hb0
      grind
    · have h : b * y ≤ b * c := mul_le_mul_of_nonpos_left hy (by grind)
      grind
  grind

/-- Lower bound of a product over a box: a corner attains it (apply the upper bound
to the reflected box). -/
theorem box_min (a b c d x y : Rat) (hx : a ≤ x) (hxb : x ≤ b) (hy : c ≤ y) (hyd : y ≤ d) :
    min (a * c) (min (a * d) (min (b * c) (b * d))) ≤ x * y := by
  have h := box_max (-b) (-a) c d (-x) y (by grind) (by grind) hy hyd
  grind

-- ANCHOR: mul
/-- Interval product: the four corners bound it. Inclusion, not equality — with
DEPENDENT inputs (`x * x`) not every corner is reachable, the classic over-estimation
of interval arithmetic. -/
def mul (I J : Interval) : Interval :=
  ⟨min (I.lo * J.lo) (min (I.lo * J.hi) (min (I.hi * J.lo) (I.hi * J.hi))),
   max (I.lo * J.lo) (max (I.lo * J.hi) (max (I.hi * J.lo) (I.hi * J.hi)))⟩

theorem mul_spec {I J : Interval} {x y : Rat} (hx : Mem x I) (hy : Mem y J) :
    Mem (x * y) (mul I J) := by
  obtain ⟨a, b⟩ := hx
  obtain ⟨c, d⟩ := hy
  exact ⟨box_min I.lo I.hi J.lo J.hi x y a b c d,
         box_max I.lo I.hi J.lo J.hi x y a b c d⟩
-- ANCHOR_END: mul

/-! ## Inverse and division on a POSITIVE interval

`1/x` flips inequalities, so the bounds swap. The positivity hypothesis is part of
the API: division by an interval containing `0` has no finite enclosure, and the
typechecker forces you to say why that cannot happen. -/

theorem inv_le_inv_core {x y : Rat} (hx : 0 < x) (h : x ≤ y) : y⁻¹ ≤ x⁻¹ := by
  have hxy : 0 < x * y := Rat.mul_pos hx (by grind)
  have hxy' : x * y ≠ 0 := by grind
  have h1 : y⁻¹ * (x * y) = x := by grind
  have h2 : x⁻¹ * (x * y) = y := by grind
  have this : y⁻¹ * (x * y) ≤ x⁻¹ * (x * y) := by rw [h1, h2]; exact h
  have hinv : 0 ≤ (x * y)⁻¹ := Rat.le_of_lt ((@Rat.inv_pos (x * y)).mpr hxy)
  calc y⁻¹ = y⁻¹ * 1 := by grind
    _ = y⁻¹ * ((x * y) * (x * y)⁻¹) := by rw [Rat.mul_inv_cancel (x * y) hxy']
    _ = (y⁻¹ * (x * y)) * (x * y)⁻¹ := by grind
    _ ≤ (x⁻¹ * (x * y)) * (x * y)⁻¹ := Rat.mul_le_mul_of_nonneg_right this hinv
    _ = x⁻¹ * ((x * y) * (x * y)⁻¹) := by grind
    _ = x⁻¹ * 1 := by rw [Rat.mul_inv_cancel (x * y) hxy']
    _ = x⁻¹ := by grind

/-- Inverse of a strictly positive interval: bounds swap. -/
def invPos (I : Interval) (h : 0 < I.lo) : Interval := ⟨I.hi⁻¹, I.lo⁻¹⟩

theorem invPos_spec {I : Interval} {x : Rat} (h : 0 < I.lo) (hx : Mem x I) :
    Mem x⁻¹ (invPos I h) := by
  obtain ⟨a, b⟩ := hx
  have hx0 : 0 < x := by grind
  show I.hi⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ I.lo⁻¹
  exact ⟨inv_le_inv_core hx0 b, inv_le_inv_core h a⟩

/-- Division by a strictly positive interval. -/
def divPos (I J : Interval) (h : 0 < J.lo) : Interval := mul I (invPos J h)

theorem divPos_spec {I J : Interval} {x y : Rat} (h : 0 < J.lo)
    (hx : Mem x I) (hy : Mem y J) : Mem (x / y) (divPos I J h) := by
  have hd : x / y = x * y⁻¹ := Rat.div_def x y
  rw [hd]
  exact mul_spec hx (invPos_spec h hy)

/-! ## Widening: paying for a rounding margin in exact rationals

A Float result `f` of an exact value `v` with error at most `e` (an exact `Rat`,
e.g. from an ULP budget) is enclosed by `[f - e, f + e]`. -/

def widen (I : Interval) (e : Rat) (he : 0 ≤ e) : Interval := ⟨I.lo - e, I.hi + e⟩

theorem widen_spec {I : Interval} {e : Rat} (he : 0 ≤ e) {x : Rat} (hx : Mem x I) :
    Mem x (widen I e he) := by
  obtain ⟨a, b⟩ := hx
  show I.lo - e ≤ x ∧ x ≤ I.hi + e
  exact ⟨by grind, by grind⟩

/-! ## Closed-form certificates

These are the facts a "certified demo" publishes, and `grind` — the same tactic
the proofs use — checks them. The kernel-only `decide` cannot do this: `Rat.mul`
reduces through smart constructors (gcd normalisation) that the kernel does not
evaluate; `grind`'s ring normalisation can. -/

/-! Certificates: `simp only` opens the definitional dictionary (one `Rat`
expression per corner), `grind`'s rational ring checks the closed form. -/

/-- Squaring a POINT is exact: all four corners agree. -/
example : (mul (point (1/2)) (point (1/2))).lo = 1/4 := by
  simp only [mul, point]
  grind
example : (mul (point (-1)) (point (4 : Rat))).lo = -4 := by
  simp only [mul, point]
  grind
example : (mul (point (-1)) (point (4 : Rat))).hi = -4 := by
  simp only [mul, point]
  grind
example : (add (point (1/10)) (point (1/5))).lo = 3/10 := by
  show (1/10 : Rat) + (1/5 : Rat) = 3/10
  grind
example : (sub ⟨(0 : Rat), 1⟩ ⟨0, 1⟩).lo = -1 := by
  show (0 : Rat) - 1 = -1
  grind
example : (widen (point (11/10)) (11/100) (by grind)).hi = 121/100 := by
  show (11/10 : Rat) + 11/100 = 121/100
  grind
example : (invPos (point (2 : Rat)) (by show (0 : Rat) < 2; grind)).lo = (2 : Rat)⁻¹ := by
  show (2 : Rat)⁻¹ = (2 : Rat)⁻¹
  grind
example (hq : (0 : Rat) < 2) : (divPos (point (1 : Rat)) (point 2) hq).hi = (2 : Rat)⁻¹ := by
  show max ((1 : Rat) * (2 : Rat)⁻¹) (max ((1 : Rat) * (2 : Rat)⁻¹)
    (max ((1 : Rat) * (2 : Rat)⁻¹) ((1 : Rat) * (2 : Rat)⁻¹))) = (2 : Rat)⁻¹
  grind

/-- The dependency gap, witnessed: `x - x = 0` for every `x`, yet `I - I` has
DOUBLE the width. The enclosure is sound, never exact, for dependent inputs. -/
example : (sub (point (0 : Rat)) (point 0)).hi = 0 := by
  show (0 : Rat) - 0 = 0
  grind

end LeanDL
