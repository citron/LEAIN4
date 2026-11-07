import LeanDL.Ch02.Xor

/-!
# Chapter 2, part 2 — The perceptron learning rule and Novikoff's theorem

Bias is folded into the weights with `Vec.cons1`, so a perceptron is just a vector `w`.
Labels are `+1` / `-1`.
-/

namespace LeanDL.Ch02

open Lean.Grind LeanDL.Ch01

/-! ## Algebra of the dot product over `Rat` -/

/-- Moved to `LeanDL.sq_nonneg` (Core); kept as the chapter's name. -/
theorem sq_nonneg (x : Rat) : 0 ≤ x * x := LeanDL.sq_nonneg x

theorem dot_self_nonneg : ∀ {n : Nat} (x : Vec Rat n), 0 ≤ Vec.dot x x
  | 0, x => by simp only [Vec.dot]; grind
  | n + 1, x => by
    have ih := dot_self_nonneg (fun i : Fin n => x i.succ)
    simp only [Vec.dot]
    have := sq_nonneg (x 0)
    grind

/-- Expansion of `(s a + t b)·(s a + t b)`. -/
theorem dot_lin {n : Nat} (a b : Vec Rat n) (s t : Rat) :
    Vec.dot (fun i => s * a i + t * b i) (fun i => s * a i + t * b i) =
      s * s * Vec.dot a a + 2 * s * t * Vec.dot a b + t * t * Vec.dot b b := by
  simp only [Vec.dot_add_left, Vec.dot_add_right, Vec.dot_smul_left, Vec.dot_smul_right]
  rw [Vec.dot_comm b a]
  generalize Vec.dot a a = A
  generalize Vec.dot a b = C
  generalize Vec.dot b b = B
  grind

-- ANCHOR: cauchy_schwarz
/-- Cauchy–Schwarz, proved without square roots: `(a·b)² ≤ (a·a)(b·b)`. -/
theorem cauchy_schwarz {n : Nat} (a b : Vec Rat n) :
    Vec.dot a b * Vec.dot a b ≤ Vec.dot a a * Vec.dot b b := by
  have hq : ∀ s t : Rat, 0 ≤ s * s * Vec.dot a a + 2 * s * t * Vec.dot a b
      + t * t * Vec.dot b b := by
    intro s t
    rw [← dot_lin]
    exact dot_self_nonneg _
  have hA := dot_self_nonneg a
  have hB := dot_self_nonneg b
  by_cases hb : Vec.dot b b = 0
  · by_cases hc : Vec.dot a b = 0
    · rw [hc, hb]; grind
    · exfalso
      have h2 : (2 : Rat) * Vec.dot a b ≠ 0 := by grind
      have hd := Rat.div_mul_cancel (a := -(Vec.dot a a + 1)) h2
      have := hq 1 (-(Vec.dot a a + 1) / (2 * Vec.dot a b))
      rw [hb] at this
      grind
  · have hpos : 0 < Vec.dot b b := by grind
    have := hq (Vec.dot b b) (-Vec.dot a b)
    exact Rat.le_of_mul_le_mul_left (c := Vec.dot b b) (by grind) hpos
-- ANCHOR_END: cauchy_schwarz

/-! ## The learning rule -/

/-! The same laws, restated at `Rat` so that `grind` sees one syntactic form of `Vec.dot`. -/

theorem dotQ_add_right {n : Nat} (x y z : Vec Rat n) :
    Vec.dot x (fun i => y i + z i) = Vec.dot x y + Vec.dot x z := Vec.dot_add_right x y z

theorem dotQ_smul_right {n : Nat} (c : Rat) (x y : Vec Rat n) :
    Vec.dot x (fun i => c * y i) = c * Vec.dot x y := Vec.dot_smul_right c x y

theorem dotQ_add_left {n : Nat} (x y z : Vec Rat n) :
    Vec.dot (fun i => x i + y i) z = Vec.dot x z + Vec.dot y z := Vec.dot_add_left x y z

theorem dotQ_smul_left {n : Nat} (c : Rat) (x y : Vec Rat n) :
    Vec.dot (fun i => c * x i) y = c * Vec.dot x y := Vec.dot_smul_left c x y

theorem dotQ_comm {n : Nat} (x y : Vec Rat n) : Vec.dot x y = Vec.dot y x := Vec.dot_comm x y

theorem dotQ_zero_right {n : Nat} (x : Vec Rat n) : Vec.dot x (fun _ => (0 : Rat)) = 0 := by
  rw [Vec.dot_comm]; exact Vec.dot_zero_left x

-- ANCHOR: update
/-- One perceptron step on a mistaken example `(x, y)` with label `y = ±1`. -/
def update {α : Type} [Add α] [Mul α] {n : Nat} (w x : Vec α n) (y : α) : Vec α n :=
  fun i => w i + y * x i

/-- Prediction is the sign of `w · x`; the example is a mistake if `y (w · x) ≤ 0`. -/
def Mistake {α : Type} [Add α] [Mul α] [OfNat α 0] [LE α] {n : Nat} (w x : Vec α n) (y : α) :
    Prop := y * Vec.dot w x ≤ 0
-- ANCHOR_END: update

section Novikoff

variable {n k : Nat} (ws xs : Nat → Vec Rat n) (ys : Nat → Rat)
  (wstar : Vec Rat n) (γ R2 : Rat)

/-- Every iterate of the rule gains at least `γ` of alignment with a separator `w*`. -/
theorem alignment_grows (h0 : ws 0 = fun _ => 0)
    (hstep : ∀ t < k, ws (t + 1) = update (ws t) (xs t) (ys t))
    (hsep : ∀ t < k, γ ≤ ys t * Vec.dot wstar (xs t)) :
    ∀ t ≤ k, (t : Rat) * γ ≤ Vec.dot wstar (ws t) := by
  intro t
  induction t with
  | zero => intro _; rw [h0, dotQ_zero_right]; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := hsep t (by omega)
    rw [hstep t (by omega)]
    unfold update
    rw [dotQ_add_right, dotQ_smul_right]
    have : ((t + 1 : Nat) : Rat) = (t : Rat) + 1 := by simp
    rw [this]
    grind

/-- Every iterate has squared norm at most `t R²`, because each update is a mistake. -/
theorem norm_grows (h0 : ws 0 = fun _ => 0)
    (hstep : ∀ t < k, ws (t + 1) = update (ws t) (xs t) (ys t))
    (hmist : ∀ t < k, ys t * Vec.dot (ws t) (xs t) ≤ 0)
    (hy : ∀ t < k, ys t * ys t = 1)
    (hR : ∀ t < k, Vec.dot (xs t) (xs t) ≤ R2) :
    ∀ t ≤ k, Vec.dot (ws t) (ws t) ≤ (t : Rat) * R2 := by
  intro t
  induction t with
  | zero => intro _; rw [h0, Vec.dot_zero_left]; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := hmist t (by omega)
    have h3 := hy t (by omega)
    have h4 := hR t (by omega)
    rw [hstep t (by omega)]
    unfold update
    simp only [dotQ_add_left, dotQ_add_right, dotQ_smul_left, dotQ_smul_right]
    rw [dotQ_comm (xs t) (ws t)]
    have : ((t + 1 : Nat) : Rat) = (t : Rat) + 1 := by simp
    rw [this]
    have h5 : ys t * (ys t * Vec.dot (xs t) (xs t)) = Vec.dot (xs t) (xs t) := by grind
    grind

-- ANCHOR: novikoff
/-- **Novikoff (1962).** If a run of mistake-driven updates starting from `0` is separated by
`w*` with margin `γ > 0` and all examples have squared norm `≤ R²`, then the number `k` of
updates satisfies `k γ² ≤ ‖w*‖² R²`. In particular the perceptron makes finitely many mistakes. -/
theorem novikoff (hγ : 0 < γ) (hR2 : 0 ≤ R2)
    (h0 : ws 0 = fun _ => 0)
    (hstep : ∀ t < k, ws (t + 1) = update (ws t) (xs t) (ys t))
    (hmist : ∀ t < k, ys t * Vec.dot (ws t) (xs t) ≤ 0)
    (hy : ∀ t < k, ys t * ys t = 1)
    (hR : ∀ t < k, Vec.dot (xs t) (xs t) ≤ R2)
    (hsep : ∀ t < k, γ ≤ ys t * Vec.dot wstar (xs t)) :
    (k : Rat) * (γ * γ) ≤ Vec.dot wstar wstar * R2 := by
  have hA := alignment_grows ws xs ys wstar γ h0 hstep hsep k (Nat.le_refl k)
  have hB := norm_grows ws xs ys R2 h0 hstep hmist hy hR k (Nat.le_refl k)
  have hCS := cauchy_schwarz wstar (ws k)
  have hW := dot_self_nonneg wstar
  have hk : (0 : Rat) ≤ (k : Rat) := by grind
  have hkγ : 0 ≤ (k : Rat) * γ := Rat.mul_nonneg hk (by grind)
  have hP : 0 ≤ Vec.dot wstar (ws k) := by grind
  -- (kγ)² ≤ P²
  have s1 : (k : Rat) * γ * ((k : Rat) * γ) ≤ Vec.dot wstar (ws k) * Vec.dot wstar (ws k) :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hA hkγ) (Rat.mul_le_mul_of_nonneg_right hA hP)
  -- W ‖w_k‖² ≤ W k R²
  have s2 : Vec.dot wstar wstar * Vec.dot (ws k) (ws k) ≤ Vec.dot wstar wstar * ((k : Rat) * R2) :=
    Rat.mul_le_mul_of_nonneg_left hB hW
  have s3 : (k : Rat) * ((k : Rat) * (γ * γ)) ≤ (k : Rat) * (Vec.dot wstar wstar * R2) := by grind
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    have := Rat.mul_nonneg hW hR2
    grind
  · exact Rat.le_of_mul_le_mul_left s3 (by exact_mod_cast hk0)
-- ANCHOR_END: novikoff
end Novikoff

end LeanDL.Ch02
