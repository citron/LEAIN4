import LeanDL.Core.Algebra
import LeanDL.Core.Vec

/-!
# Rounding: a formal model and Higham's γ bound for the dot product

## The model

`RoundingModel` packages the standard **relative rounding** assumption: every
floating-point operation applied to an exact operand `x` returns `x·(1+δ)`
with `|δ| ≤ u`. It is a named structure with named hypotheses — not an axiom.

**Honest boundary of the model.** Overflow and underflow are **excluded**:
the identity `fl x = x·(1+δ)` with tiny `δ` is false for operands that
overflow to infinity or flush to subnormal/zero. This boundary is part of the
structure's contract, stated here, not hidden.

**Binary64 as an instance is a platform hypothesis, not a theorem.**
Round-to-nearest binary64 (no overflow/underflow, and products of the small
dyadic test inputs exactly representable) satisfies `RoundingModel` with
`u = 2⁻⁵³`. Lean 4 has no IEEE-754 theory for `Float`, so this instantiation
is graded **“Vérifié numériquement”**: the `Props` property test
(`prop_rounding_f`) measures the floating dot product's error against the
proved bound `γₖ · Σ |xᵢyᵢ|` on random dyadic inputs. It is **not** a theorem
about `Float`.

## The theorems (all over `Rat`, zero `sorry`)

* `one_add_delta_nonneg` — `|δ| ≤ u ≤ 1` gives `0 ≤ 1 + δ`.
* `gamma` and its algebra, `γₖ = k·u·(1 − k·u)⁻¹` (general `k`):
  `gamma_zero`, `gamma_nonneg`, `gamma_le_gamma` (monotone in `k` under
  `k·u < 1`), `gamma_step` (`γₖ + u·(1+γₖ) ≤ γ₍ₖ₊₁₎`).
* `prod_one_add_delta` — **Higham's product lemma, general `k`**: for a list
  `ds` of length `k` with every `|δ| ≤ u` and `k·u < 1`,
  `|∏(1+δᵢ) − 1| ≤ γₖ`, by induction on the list via `gamma_step`.
* `flDotGen_closed` — the rounded dot with explicit deltas `dᵢ` (product
  roundings) and `eᵢ` (running-sum roundings) equals `Σ xᵢyᵢ·cᵢ` where `cᵢ`
  is the **prefix product** `cᵢ = ∏_{j≤i}(1+dⱼ)(1+eⱼ)` (`coefList`).
* `coef_bound` — every coefficient satisfies `|cᵢ − 1| ≤ γ₍₂ₙ₎`: each `cᵢ`
  is a product of at most `2n` factors `1+δ` with `|δ| ≤ u` (`n = xs.length`
  = ys.length); the leading coefficient attains `2n` factors, so `γ₍₂ₙ₎` is
  the honest index (every partial sum is re-rounded here: `n` product
  roundings + `n` running-sum roundings).
* `flDot_eq_perturbed` — `flDot M xs ys = Σ xᵢyᵢ·(1+θᵢ)` with every
  `|θᵢ| ≤ γ₍₂ₙ₎` (general `n`, hypothesis `2n·u < 1`).
* `flDot_error` — **the Higham dot-product bound**:
  `|flDot M xs ys − Σ xᵢyᵢ| ≤ γ₍₂ₙ₎ · Σ |xᵢyᵢ|` (general `n`).
* `flMulVec_row_error`, `flMulVec_error` — the same bound for one dense
  layer (`rows : List (List Rat)`, all rows of length `n`), summed over
  rows: per row `|flDot − dot| ≤ γ₍₂ₙ₎ · Σ|rowᵢ·xᵢ|`, and
  `|Σⱼ flDotⱼ − Σⱼ dotⱼ| ≤ γ₍₂ₙ₎ · Σⱼᵢ |Wⱼᵢ·xᵢ|`. -/

namespace LeanDL

/-! ## The model -/

/-- Relative rounding model: `fl x = x·(1+δ)` with `|δ| ≤ u`, `u ≥ 0`.
Overflow/underflow are **excluded** (see module docstring): this is the
classic “no overflow, no underflow” regime of Higham's model. -/
structure RoundingModel where
  fl : Rat → Rat
  u : Rat
  u_nonneg : 0 ≤ u
  rel : ∀ x, ∃ δ, Rat.abs δ ≤ u ∧ fl x = x * (1 + δ)

/-- The chosen rounding delta of `fl` at `x` (classical choice from `rel`). -/
noncomputable def rd (M : RoundingModel) (x : Rat) : Rat :=
  Classical.choose (M.rel x)

/-- `rd` realises the model: `|rd M x| ≤ u` and `fl x = x·(1 + rd M x)`. -/
theorem rd_spec (M : RoundingModel) (x : Rat) :
    Rat.abs (rd M x) ≤ M.u ∧ M.fl x = x * (1 + rd M x) :=
  Classical.choose_spec (M.rel x)

/-- The exact round-to-identity model: `fl = id`, `u = 0`. -/
def exactRounding : RoundingModel where
  fl := fun x => x
  u := 0
  u_nonneg := by grind
  rel := fun x => ⟨0, by grind, by grind⟩

/-! ## The γ algebra: γₖ = k·u / (1 − k·u) -/

/-- Higham's γ factor: `γₖ = k·u / (1 − k·u)`, defined for every `k`; every
bound below is stated under the hypothesis `(k : Rat) * u < 1`. -/
def gamma (u : Rat) (k : Nat) : Rat := (k : Rat) * u * (1 - (k : Rat) * u)⁻¹

/-- Absolute-value split: `|x| ≤ u` gives `-u ≤ x ≤ u` (core has no
`Rat.abs_le`; recovered by case split on `Rat.abs`). -/
theorem abs_le_split {x u : Rat} (h : Rat.abs x ≤ u) : -u ≤ x ∧ x ≤ u := by
  grind [Rat.abs.eq_1]

/-- Adding two inequalities (core has only the iff left/right variants). -/
theorem add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Iff.mpr Rat.add_le_add_left h2) (Iff.mpr Rat.add_le_add_right h1)

/-- `|δ| ≤ u ≤ 1` makes `1 + δ` nonnegative: a rounded factor never flips
sign. -/
theorem one_add_delta_nonneg {δ u : Rat} (_hu : 0 ≤ u) (h : Rat.abs δ ≤ u)
    (hu1 : u ≤ 1) : 0 ≤ 1 + δ := by
  rcases abs_le_split h with ⟨h1, h2⟩
  grind

theorem gamma_zero (u : Rat) : gamma u 0 = 0 := by
  unfold gamma
  grind

theorem gamma_nonneg (u : Rat) (k : Nat) (hu : 0 ≤ u) (h : (k : Rat) * u < 1) :
    0 ≤ gamma u k := by
  unfold gamma
  have hp : 0 < 1 - (k : Rat) * u := by push_cast; grind
  refine Rat.mul_nonneg (Rat.mul_nonneg ?_ hu) (Rat.le_of_lt (Rat.inv_pos.mpr hp))
  exact_mod_cast Nat.zero_le k

/-- **γ monotonicity**: `k ≤ l` and `l·u < 1` give `γₖ ≤ γₗ` (cleared-side
inequality `k·u·(1 − l·u) ≤ l·u·(1 − k·u)`, multiplied by the positive
product of the two inverse denominators). -/
theorem gamma_le_gamma {k l : Nat} (u : Rat) (hu : 0 ≤ u) (hkl : k ≤ l)
    (h : (l : Rat) * u < 1) : gamma u k ≤ gamma u l := by
  have hk : (k : Rat) * u ≤ (l : Rat) * u :=
    Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hu
  have hka : 0 < 1 - (k : Rat) * u := by push_cast; grind
  have hla : 0 < 1 - (l : Rat) * u := by push_cast; grind
  have hcleared : (k : Rat) * u * (1 - (l : Rat) * u) ≤
      (l : Rat) * u * (1 - (k : Rat) * u) := by grind
  have hP : 0 ≤ (1 - (k : Rat) * u)⁻¹ * (1 - (l : Rat) * u)⁻¹ :=
    Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hka))
      (Rat.le_of_lt (Rat.inv_pos.mpr hla))
  have h := Rat.mul_le_mul_of_nonneg_right hcleared hP
  have h1 : (k : Rat) * u * (1 - (l : Rat) * u) *
      ((1 - (k : Rat) * u)⁻¹ * (1 - (l : Rat) * u)⁻¹) =
      (k : Rat) * u * (1 - (k : Rat) * u)⁻¹ := by grind
  have h2 : (l : Rat) * u * (1 - (k : Rat) * u) *
      ((1 - (k : Rat) * u)⁻¹ * (1 - (l : Rat) * u)⁻¹) =
      (l : Rat) * u * (1 - (l : Rat) * u)⁻¹ := by grind
  rw [h1, h2] at h
  unfold gamma
  exact h

/-- Inverse reverses order on positives: `0 < a`, `0 < b`, `b ≤ a` gives
`a⁻¹ ≤ b⁻¹` (multiply `b ≤ a` by the positive product `a⁻¹·b⁻¹`). -/
theorem inv_le_inv {a b : Rat} (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) :
    a⁻¹ ≤ b⁻¹ := by
  have hP : 0 ≤ a⁻¹ * b⁻¹ :=
    Rat.mul_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr ha)) (Rat.le_of_lt (Rat.inv_pos.mpr hb))
  have hmul := Rat.mul_le_mul_of_nonneg_right h hP
  have h1 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by grind
  have h2 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by grind
  rw [h1, h2] at hmul
  exact hmul

/-- **The γ step**: under `(k+1)·u < 1`, `γₖ + u·(1 + γₖ) ≤ γ₍ₖ₊₁₎`
(one more rounded multiply-add). -/
theorem gamma_step (k : Nat) (u : Rat) (hu : 0 ≤ u) (h : ((k : Rat) + 1) * u < 1) :
    gamma u k + u * (1 + gamma u k) ≤ gamma u (k + 1) := by
  have ha : 0 < 1 - (k : Rat) * u := by push_cast; grind
  have hb : 0 < 1 - ((k : Rat) + 1) * u := by push_cast; grind
  have heq : gamma u k + u * (1 + gamma u k) =
      ((k : Rat) + 1) * u * (1 - (k : Rat) * u)⁻¹ := by
    unfold gamma
    push_cast
    grind
  rw [heq]
  unfold gamma
  push_cast
  have hinv : (1 - (k : Rat) * u)⁻¹ ≤ (1 - ((k : Rat) + 1) * u)⁻¹ :=
    inv_le_inv ha hb (by push_cast; grind)
  have hkn : 0 ≤ ((k : Rat) + 1) * u :=
    Rat.mul_nonneg (by push_cast; grind) hu
  exact Rat.mul_le_mul_of_nonneg_left hinv hkn

/-- **Per-step shape**: a rounded multiply-add applied to a quantity already
perturbed by `|θ| ≤ g`, with `|δ| ≤ u`, stays within `g + u·(1+g)`. -/
theorem abs_perturbed_add {θ δ g u : Rat} (hu : 0 ≤ u) (_hg : 0 ≤ g)
    (hd : Rat.abs δ ≤ u) (ht : Rat.abs θ ≤ g) :
    Rat.abs (θ + δ * (1 + θ)) ≤ g + u * (1 + g) := by
  have h1 : Rat.abs (1 + θ) ≤ 1 + g := by
    have h : Rat.abs (1 + θ) ≤ Rat.abs 1 + Rat.abs θ := abs_add_le 1 θ
    have h1' : Rat.abs (1 : Rat) = 1 := by grind [Rat.abs.eq_1]
    rw [h1'] at h
    grind
  have h2 : Rat.abs (δ * (1 + θ)) = Rat.abs δ * Rat.abs (1 + θ) := abs_mul _ _
  have h3 : Rat.abs δ * Rat.abs (1 + θ) ≤ u * (1 + g) :=
    Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_right hd (abs_nonneg _))
      (Rat.mul_le_mul_of_nonneg_left h1 hu)
  calc Rat.abs (θ + δ * (1 + θ))
      ≤ Rat.abs θ + Rat.abs (δ * (1 + θ)) := abs_add_le _ _
    _ ≤ g + u * (1 + g) := by
      rw [h2]
      exact add_le_add ht h3

/-- Length of `zipWith`. -/
theorem zipWith_length (f : Rat → Rat → Rat) : ∀ p q : List Rat,
    (List.zipWith f p q).length = min p.length q.length
  | [], q => by
      cases q <;> rfl
  | x :: xs, [] => rfl
  | x :: xs, y :: ys => by
      show (List.zipWith f xs ys).length + 1 = min (xs.length + 1) (ys.length + 1)
      rw [zipWith_length f xs ys]
      omega

/-- **Higham's γ lemma**: for deltas with `|δᵢ| ≤ u` and `k·u < 1`
(`k = ds.length`), `|∏(1+δᵢ) − 1| ≤ γₖ`. -/
theorem prod_one_add_delta (ds : List Rat) (u : Rat) (hu : 0 ≤ u)
    (h : (ds.length : Rat) * u < 1) (hd : ∀ d ∈ ds, Rat.abs d ≤ u) :
    Rat.abs (List.prod (List.map (1 + ·) ds) - 1) ≤ gamma u ds.length := by
  induction ds with
  | nil =>
      show Rat.abs (1 - 1) ≤ gamma u 0
      rw [gamma_zero]
      grind
  | cons d ds ih =>
      have hc : ((d :: ds).length : Rat) = (ds.length : Rat) + 1 := by
        show ((ds.length + 1 : Nat) : Rat) = (ds.length : Rat) + 1
        rw [Rat.natCast_add]
        grind
      have hu' : (ds.length : Rat) * u < 1 := by
        have h2 := h
        rw [hc] at h2
        grind
      have h1u : ((ds.length : Rat) + 1) * u < 1 := by
        rw [← hc]
        exact h
      have hd' : ∀ x ∈ ds, Rat.abs x ≤ u :=
        fun x hx => hd x (List.mem_cons.mpr (Or.inr hx))
      have ih' := ih hu' hd'
      have hd0 : Rat.abs d ≤ u := hd d (by simp)
      have hstep := abs_perturbed_add hu (gamma_nonneg u ds.length hu hu') hd0 ih'
      have hprod : List.prod (List.map (1 + ·) (d :: ds)) =
          (1 + d) * List.prod (List.map (1 + ·) ds) := rfl
      have hrew : (1 + d) * List.prod (List.map (1 + ·) ds) - 1 =
          (List.prod (List.map (1 + ·) ds) - 1) +
            d * (1 + (List.prod (List.map (1 + ·) ds) - 1)) := by grind
      rw [hprod, hrew]
      exact Rat.le_trans hstep (gamma_step ds.length u hu h1u)

/-! ## List machinery (minimal self-contained vector API) -/

/-- Sum of a list. -/
def lsum : List Rat → Rat
  | [] => 0
  | x :: xs => x + lsum xs

theorem lsum_append : ∀ a b : List Rat, lsum (a ++ b) = lsum a + lsum b
  | [], b => by
      show lsum b = 0 + lsum b
      grind
  | x :: xs, b => by
      have ih := lsum_append xs b
      show x + lsum (xs ++ b) = x + lsum xs + lsum b
      rw [ih]
      grind

theorem lsum_map_smul (c : Rat) : ∀ l : List Rat,
    lsum (List.map (c * ·) l) = c * lsum l
  | [] => by
      show 0 = c * 0
      grind
  | x :: xs => by
      show c * x + lsum (List.map (c * ·) xs) = c * (x + lsum xs)
      rw [lsum_map_smul c xs]
      grind

theorem lsum_map_smul' (c : Rat) : ∀ l : List Rat,
    lsum (List.map (· * c) l) = c * lsum l
  | [] => by
      show 0 = c * 0
      grind
  | x :: xs => by
      show x * c + lsum (List.map (· * c) xs) = c * (x + lsum xs)
      rw [lsum_map_smul' c xs]
      grind

/-- Triangle inequality over a list: `|Σ l| ≤ Σ |x|`. -/
theorem lsum_abs_le : ∀ l : List Rat, Rat.abs (lsum l) ≤ lsum (List.map Rat.abs l)
  | [] => by
      show 0 ≤ 0
      grind
  | x :: xs => by
      show Rat.abs (x + lsum xs) ≤ Rat.abs x + lsum (List.map Rat.abs xs)
      refine Rat.le_trans (abs_add_le x (lsum xs)) ?_
      exact Iff.mpr Rat.add_le_add_left (lsum_abs_le xs)

/-- Coefficient form of a perturbed sum: if every `|cᵢ − 1| ≤ γ` then
`|Σ pᵢcᵢ − Σ pᵢ| ≤ γ · Σ |pᵢ|`. -/
theorem lsum_coef_error (γ : Rat) (_hγ : 0 ≤ γ) : ∀ p c : List Rat,
    p.length = c.length → (∀ x ∈ c, Rat.abs (x - 1) ≤ γ) →
    Rat.abs (lsum (List.zipWith (· * ·) p c) - lsum p) ≤
      γ * lsum (List.map Rat.abs p) := by
  intro p
  induction p with
  | nil =>
      intro c hlen _
      cases c with
      | nil =>
          simp only [List.zipWith, List.map, lsum]
          rw [Rat.sub_self, Rat.abs_zero, Rat.mul_zero]
          grind
      | cons cy cs =>
          rw [List.length_nil, List.length_cons] at hlen
          omega
  | cons x xs ih =>
      intro c hlen hc
      cases c with
      | nil =>
          rw [List.length_cons, List.length_nil] at hlen
          omega
      | cons cy cs =>
        show Rat.abs ((x * cy + lsum (List.zipWith (· * ·) xs cs)) - (x + lsum xs)) ≤
            γ * (Rat.abs x + lsum (List.map Rat.abs xs))
        have hlen' : xs.length = cs.length := by
          rw [List.length_cons, List.length_cons] at hlen
          omega
        have hc0 : Rat.abs (cy - 1) ≤ γ := hc cy (by simp)
        have hx : Rat.abs (x * cy - x) ≤ γ * Rat.abs x := by
          have h1 : x * cy - x = x * (cy - 1) := by grind
          rw [h1, abs_mul]
          have h2 := Rat.mul_le_mul_of_nonneg_right hc0 (abs_nonneg x)
          grind
        have hxs := ih cs (by assumption) (fun z hz => hc z (List.mem_cons.mpr (Or.inr hz)))
        have hsum : (x * cy + lsum (List.zipWith (· * ·) xs cs)) - (x + lsum xs) =
            (x * cy - x) + (lsum (List.zipWith (· * ·) xs cs) - lsum xs) := by grind
        rw [hsum]
        have htri := abs_add_le (x * cy - x) (lsum (List.zipWith (· * ·) xs cs) - lsum xs)
        have hdist : γ * Rat.abs x + γ * lsum (List.map Rat.abs xs) =
            γ * (Rat.abs x + lsum (List.map Rat.abs xs)) := by grind
        rw [← hdist]
        exact Rat.le_trans htri (add_le_add hx hxs)

/-! ## The rounded dot product -/

/-- The floating dot: `fl` applied to **every product and every addition**
(left fold over `zip xs ys`; `xs`, `ys` are read as vectors of equal length). -/
noncomputable def flDot : (M : RoundingModel) → List Rat → List Rat → Rat
  | _, [], _ => 0
  | _, _, [] => 0
  | M, x :: xs, y :: ys => M.fl (M.fl (x * y) + flDot M xs ys)

/-- The exact dot as a list sum: `Σ xᵢyᵢ`. -/
def ldot (xs ys : List Rat) : Rat := lsum (List.zipWith (· * ·) xs ys)

/-- The generator of the closed form: one rounded product and one rounded
addition per term: `G = (x·y·(1+d) + G_tail)·(1+e)`. -/
def flDotGen : List Rat → List Rat → List Rat → List Rat → Rat
  | [], _, _, _ => 0
  | _, [], _, _ => 0
  | _, _, [], _ => 0
  | _, _, _, [] => 0
  | x :: xs, y :: ys, d :: ds, e :: es =>
      (x * y * (1 + d) + flDotGen xs ys ds es) * (1 + e)

/-- Running coefficients of the closed form: the recursion
`F_k = (p_k(1+d_k) + F_{k+1})(1+e_k)` expands to `Σ pᵢ cᵢ` with
`cᵢ = ∏_{j≤i}(1+d_j)(1+e_j)`. -/
def coefList : List Rat → List Rat → List Rat
  | [], _ => []
  | _, [] => []
  | d :: ds, e :: es =>
      (1 + d) * (1 + e) :: List.map (· * (1 + e)) (coefList ds es)

theorem coefList_length : ∀ ds es : List Rat,
    (coefList ds es).length = min ds.length es.length := by
  intro ds
  induction ds with
  | nil => intro es; cases es <;> rfl
  | cons d ds ih =>
      intro es
      cases es with
      | nil => rfl
      | cons e es =>
          show List.length (List.map (· * (1 + e)) (coefList ds es)) + 1 =
              min (ds.length + 1) (es.length + 1)
          rw [List.length_map, ih]
          omega

/-- Every coefficient is a product of at most `2 * ds.length` factors
`(1 + δ)` taken from `ds ++ es`. -/
theorem coefList_factor_aux :
    ∀ ds es : List Rat, ds.length = es.length →
      ∀ c ∈ coefList ds es, ∃ l : List Rat,
        c = List.prod (List.map (1 + ·) l) ∧
        l.length ≤ 2 * ds.length ∧
        (∀ x ∈ l, x ∈ ds ∨ x ∈ es) := by
  intro ds
  induction ds with
  | nil => intro es _ c hc; cases hc
  | cons d ds ih =>
      intro es
      induction es with
      | nil => intro _ c hc; cases hc
      | cons e es =>
          intro hlen c hc
          rw [coefList] at hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · refine ⟨[d, e], ?_, ?_, ?_⟩
            · show (1 + d) * (1 + e) = List.prod (List.map (1 + ·) [d, e])
              show (1 + d) * (1 + e) = (1 + d) * ((1 + e) * 1)
              grind
            · rw [show List.length ([d, e] : List Rat) = 2 from rfl]
              rw [List.length_cons]
              omega
            · intro x hx
              rw [List.mem_cons] at hx
              rcases hx with rfl | hx
              · left; exact List.mem_cons.mpr (Or.inl rfl)
              · rw [List.mem_singleton] at hx
                subst hx
                right; exact List.mem_cons.mpr (Or.inl rfl)
          · rw [List.mem_map] at hc'
            rcases hc' with ⟨c', hc', rfl⟩
            have hlen' : ds.length = es.length := by simpa using hlen
            obtain ⟨l, hl1, hl2, hl3⟩ := ih es hlen' c' hc'
            refine ⟨e :: l, ?_, ?_, ?_⟩
            · rw [List.map_cons, List.prod_cons, ← hl1]
              grind
            · rw [List.length_cons, List.length_cons]
              omega
            · intro x hx
              rw [List.mem_cons] at hx
              rcases hx with rfl | hx
              · right; simp
              · rcases hl3 x hx with hd | he
                · left; exact List.mem_cons.mpr (Or.inr hd)
                · right; exact List.mem_cons.mpr (Or.inr he)

theorem coefList_factor (ds es : List Rat) (hlen : ds.length = es.length) :
    ∀ c ∈ coefList ds es, ∃ l : List Rat,
      c = List.prod (List.map (1 + ·) l) ∧
      l.length ≤ 2 * ds.length ∧
      (∀ x ∈ l, x ∈ ds ∨ x ∈ es) :=
  coefList_factor_aux ds es hlen

/-- **Coefficient bound**: every `c ∈ coefList ds es` satisfies
`|c − 1| ≤ γ₍₂ₙ₎` (`n = ds.length`) when all deltas are bounded by `u`
and `2n·u < 1` (each coefficient is a product of at most `2n` factors
`(1+δ)`; Higham's product lemma + γ monotonicity). -/
theorem coef_bound (ds es : List Rat) (u : Rat) (hlen : ds.length = es.length)
    (hu : 0 ≤ u) (hγ : ((2 * ds.length : Nat) : Rat) * u < 1)
    (hud : ∀ d ∈ ds ++ es, Rat.abs d ≤ u) :
    ∀ c ∈ coefList ds es, Rat.abs (c - 1) ≤ gamma u (2 * ds.length) := by
  intro c hc
  obtain ⟨l, hl1, hl2, hl3⟩ := coefList_factor ds es hlen c hc
  have hlenl : (l.length : Rat) * u < 1 := by
    have hle : (l.length : Rat) ≤ 2 * (ds.length : Rat) := by
      push_cast
      exact_mod_cast hl2
    have hmul := Rat.mul_le_mul_of_nonneg_right hle hu
    rw [Rat.natCast_mul] at hγ
    grind
  have hdl : ∀ x ∈ l, Rat.abs x ≤ u := by
    intro x hx
    rcases hl3 x hx with hx | hx
    · exact hud x (List.mem_append.mpr (Or.inl hx))
    · exact hud x (List.mem_append.mpr (Or.inr hx))
  have hmono : gamma u l.length ≤ gamma u (2 * ds.length) :=
    gamma_le_gamma u hu (by exact_mod_cast hl2) hγ
  have hprod := prod_one_add_delta l u hu hlenl hdl
  rw [hl1]
  exact Rat.le_trans hprod hmono

theorem zipWith_map_mul (g : Rat) : ∀ p q : List Rat, p.length = q.length →
    List.zipWith (· * ·) p (List.map (· * g) q)
      = List.map (· * g) (List.zipWith (· * ·) p q) := by
  intro p
  induction p with
  | nil => intro q _; cases q <;> rfl
  | cons a as ih =>
      intro q hpq
      cases q with
      | nil => simp at hpq
      | cons b bs =>
          show (a * (b * g)) :: List.zipWith (· * ·) as (List.map (· * g) bs)
              = (a * b * g) :: List.map (· * g) (List.zipWith (· * ·) as bs)
          rw [ih bs (by simpa using hpq)]
          grind

/-- **Closed form** (Higham product form): the rounded dot with explicit
per-operation deltas `d` (products) and `e` (additions) equals
`Σ xᵢyᵢ·cᵢ` with `cᵢ = (1+dᵢ)·∏ⱼ≥ᵢ(1+eⱼ)`. -/
theorem flDotGen_closed : ∀ p q ds es,
    p.length = q.length → q.length = ds.length → ds.length = es.length →
    flDotGen p q ds es
      = lsum (List.zipWith (· * ·) (List.zipWith (· * ·) p q) (coefList ds es)) := by
  intro p
  induction p with
  | nil =>
      intro q ds es _ _ _
      cases q <;> cases ds <;> cases es <;> rfl
  | cons a as ih =>
      intro q ds es hpq hqd hde
      cases q with
      | nil => simp at hpq
      | cons b bs =>
          cases ds with
          | nil => simp at hqd
          | cons d ds =>
              cases es with
              | nil => simp at hde
              | cons e es =>
                  show (a * b * (1 + d) + flDotGen as bs ds es) * (1 + e)
                      = lsum (List.zipWith (· * ·)
                        (a * b :: List.zipWith (· * ·) as bs)
                        ((1 + d) * (1 + e)
                          :: List.map (· * (1 + e)) (coefList ds es)))
                  have ih' := ih bs ds es (by simpa using hpq) (by simpa using hqd)
                    (by simpa using hde)
                  have hzip : List.zipWith (· * ·)
                        (a * b :: List.zipWith (· * ·) as bs)
                        ((1 + d) * (1 + e)
                          :: List.map (· * (1 + e)) (coefList ds es))
                      = (a * b * ((1 + d) * (1 + e)))
                        :: List.map (· * (1 + e))
                          (List.zipWith (· * ·) (List.zipWith (· * ·) as bs)
                            (coefList ds es)) := by
                    show (a * b * ((1 + d) * (1 + e)))
                        :: List.zipWith (· * ·) (List.zipWith (· * ·) as bs)
                            (List.map (· * (1 + e)) (coefList ds es))
                        = (a * b * ((1 + d) * (1 + e)))
                        :: List.map (· * (1 + e))
                          (List.zipWith (· * ·) (List.zipWith (· * ·) as bs)
                            (coefList ds es))
                    rw [zipWith_map_mul (1 + e)]
                    · have hl1 : as.length = bs.length := by simpa using hpq
                      have hl2 : bs.length = ds.length := by simpa using hqd
                      have hl3 : ds.length = es.length := by simpa using hde
                      rw [zipWith_length (· * ·), coefList_length]
                      omega
                  rw [hzip, lsum, lsum_map_smul', ih']
                  grind

/-! Realising the generator with the model's own deltas. -/

/-- Product deltas: `dᵢ = rd M (xᵢyᵢ)`. -/
noncomputable def deltasP : (M : RoundingModel) → List Rat → List Rat → List Rat
  | _, [], _ => []
  | _, _, [] => []
  | M, x :: xs, y :: ys => rd M (x * y) :: deltasP M xs ys

/-- Addition deltas: `eᵢ = rd M (fl(xᵢyᵢ) + tail)`, the running sum. -/
noncomputable def deltasA : (M : RoundingModel) → List Rat → List Rat → List Rat
  | _, [], _ => []
  | _, _, [] => []
  | M, x :: xs, y :: ys =>
      rd M (M.fl (x * y) + flDot M xs ys) :: deltasA M xs ys

theorem deltasP_length (M : RoundingModel) : ∀ xs ys : List Rat,
    (deltasP M xs ys).length = min xs.length ys.length := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> rfl
  | cons a as ih =>
      intro ys
      cases ys with
      | nil => rfl
      | cons b bs =>
          show (deltasP M as bs).length + 1 = min (as.length + 1) (bs.length + 1)
          rw [ih]
          omega

theorem deltasA_length (M : RoundingModel) : ∀ xs ys : List Rat,
    (deltasA M xs ys).length = min xs.length ys.length := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> rfl
  | cons a as ih =>
      intro ys
      cases ys with
      | nil => rfl
      | cons b bs =>
          show (deltasA M as bs).length + 1 = min (as.length + 1) (bs.length + 1)
          rw [ih]
          omega

/-- Every product delta is bounded by `u`. -/
theorem deltasP_bound (M : RoundingModel) : ∀ d xs ys,
    d ∈ deltasP M xs ys → Rat.abs d ≤ M.u := by
  intro d xs
  induction xs with
  | nil => intro ys hd; cases hd
  | cons a as ih =>
      intro ys hd
      cases ys with
      | nil => cases hd
      | cons b bs =>
          rw [deltasP] at hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact (rd_spec M _).1
          · exact ih bs hd

/-- Every addition delta is bounded by `u`. -/
theorem deltasA_bound (M : RoundingModel) : ∀ d xs ys,
    d ∈ deltasA M xs ys → Rat.abs d ≤ M.u := by
  intro d xs
  induction xs with
  | nil => intro ys hd; cases hd
  | cons a as ih =>
      intro ys hd
      cases ys with
      | nil => cases hd
      | cons b bs =>
          rw [deltasA] at hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact (rd_spec M _).1
          · exact ih bs hd

/-- `flDot` realises the generator with its own rounding deltas. -/
theorem flDot_eq_flDotGen (M : RoundingModel) : ∀ xs ys,
    xs.length = ys.length →
    flDot M xs ys
      = flDotGen xs ys (deltasP M xs ys) (deltasA M xs ys) := by
  intro xs
  induction xs with
  | nil => intro ys _; cases ys <;> rfl
  | cons a as ih =>
      intro ys hlen
      cases ys with
      | nil => simp at hlen
      | cons b bs =>
          show M.fl (M.fl (a * b) + flDot M as bs)
              = (a * b * (1 + rd M (a * b))
                  + flDotGen as bs (deltasP M as bs) (deltasA M as bs)) *
                (1 + rd M (M.fl (a * b) + flDot M as bs))
          have hlen' : as.length = bs.length := by simpa using hlen
          have ih' := ih bs hlen'
          have h1 : M.fl (a * b) = a * b * (1 + rd M (a * b)) := (rd_spec M (a * b)).2
          have h2 : M.fl (M.fl (a * b) + flDot M as bs) =
              (M.fl (a * b) + flDot M as bs) *
                (1 + rd M (M.fl (a * b) + flDot M as bs)) :=
            (rd_spec M (M.fl (a * b) + flDot M as bs)).2
          rw [h2, h1, ih']

/-! ## The dot-product error bound -/

/-- Cancelling the `1 + (c − 1)` round-trip on a coefficient list. -/
theorem map_add_sub_cancel : ∀ l : List Rat,
    List.map (1 + ·) (List.map (· - 1) l) = l
  | [] => rfl
  | c :: cs => by
      show (1 + (c - 1)) :: List.map (1 + ·) (List.map (· - 1) cs) = c :: cs
      rw [map_add_sub_cancel cs]
      grind

/-- **Perturbed form** (honest counting `k = 2n`: each of the `n` rounded
products contributes one factor, each of the `n` rounded sums another): the
floating dot equals `Σ xᵢyᵢ·(1+θᵢ)` with every `|θᵢ| ≤ γ₍₂ₙ₎`. -/
theorem flDot_eq_perturbed (M : RoundingModel) (xs ys : List Rat)
    (hlen : xs.length = ys.length)
    (hγ : ((2 * xs.length : Nat) : Rat) * M.u < 1) :
    ∃ thetas : List Rat,
      thetas.length = xs.length ∧
      (∀ θ ∈ thetas, Rat.abs θ ≤ gamma M.u (2 * xs.length)) ∧
      flDot M xs ys
        = lsum (List.zipWith (· * ·) (List.zipWith (· * ·) xs ys)
            (List.map (1 + ·) thetas)) := by
  let ds := deltasP M xs ys
  let es := deltasA M xs ys
  have hdlen : ds.length = min xs.length ys.length := deltasP_length M xs ys
  have helen : es.length = min xs.length ys.length := deltasA_length M xs ys
  have hclen : (coefList ds es).length = (List.zipWith (· * ·) xs ys).length := by
    rw [coefList_length, hdlen, helen, zipWith_length (· * ·)]
    omega
  have hgen : flDot M xs ys = flDotGen xs ys ds es := flDot_eq_flDotGen M xs ys hlen
  have heq : flDot M xs ys
      = lsum (List.zipWith (· * ·) (List.zipWith (· * ·) xs ys) (coefList ds es)) := by
    rw [hgen, flDotGen_closed xs ys ds es]
    · exact hlen
    · rw [hdlen, hlen]
      omega
    · rw [hdlen, helen]
  refine ⟨List.map (· - 1) (coefList ds es), ?_, ?_, ?_⟩
  · rw [List.length_map, hclen, zipWith_length (· * ·)]
    rw [hlen]
    exact Nat.min_self _
  · intro th hth
    rw [List.mem_map] at hth
    rcases hth with ⟨c, hc, rfl⟩
    have hud : ∀ d ∈ ds ++ es, Rat.abs d ≤ M.u := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact deltasP_bound M d xs ys hd
      · exact deltasA_bound M d xs ys hd
    have hlen' : ds.length = es.length := by rw [hdlen, helen]
    have hds : ds.length = xs.length := by
      rw [hdlen, hlen]
      exact Nat.min_self _
    have hγ' : ((2 * ds.length : Nat) : Rat) * M.u < 1 := by
      rw [show (2 * ds.length : Nat) = 2 * xs.length by rw [hds]]
      exact hγ
    have hcb := coef_bound ds es M.u hlen' M.u_nonneg hγ' hud c hc
    rw [show (2 * ds.length : Nat) = 2 * xs.length by rw [hds]] at hcb
    exact hcb
  · rw [heq]
    congr 1
    rw [map_add_sub_cancel (coefList ds es)]

/-- **The dot-product error bound**:
`|flDot M xs ys − Σ xᵢyᵢ| ≤ γ₍₂ₙ₎ · Σ |xᵢyᵢ|` (`n = xs.length`, `2n·u < 1`). -/
theorem flDot_error (M : RoundingModel) (xs ys : List Rat)
    (hlen : xs.length = ys.length)
    (hγ : ((2 * xs.length : Nat) : Rat) * M.u < 1) :
    Rat.abs (flDot M xs ys - ldot xs ys) ≤
      gamma M.u (2 * xs.length) * lsum (List.map Rat.abs (List.zipWith (· * ·) xs ys)) := by
  let ds := deltasP M xs ys
  let es := deltasA M xs ys
  have hdlen : ds.length = min xs.length ys.length := deltasP_length M xs ys
  have helen : es.length = min xs.length ys.length := deltasA_length M xs ys
  have hlen' : ds.length = es.length := by rw [hdlen, helen]
  have hclen : (List.zipWith (· * ·) xs ys).length = (coefList ds es).length := by
    rw [coefList_length, hdlen, helen, zipWith_length (· * ·)]
    omega
  have hgen : flDot M xs ys = flDotGen xs ys ds es := flDot_eq_flDotGen M xs ys hlen
  have heq : flDot M xs ys
      = lsum (List.zipWith (· * ·) (List.zipWith (· * ·) xs ys) (coefList ds es)) := by
    rw [hgen, flDotGen_closed xs ys ds es]
    · exact hlen
    · rw [hdlen, hlen]
      omega
    · rw [hdlen, helen]
  rw [heq]
  have hud : ∀ d ∈ ds ++ es, Rat.abs d ≤ M.u := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact deltasP_bound M d xs ys hd
    · exact deltasA_bound M d xs ys hd
  have hds : ds.length = xs.length := by
    rw [hdlen, hlen]
    exact Nat.min_self _
  have hγ' : ((2 * ds.length : Nat) : Rat) * M.u < 1 := by
    rw [show (2 * ds.length : Nat) = 2 * xs.length by rw [hds]]
    exact hγ
  have hbound : ∀ c ∈ coefList ds es, Rat.abs (c - 1) ≤ gamma M.u (2 * xs.length) := by
    intro c hc
    have hcb := coef_bound ds es M.u hlen' M.u_nonneg hγ' hud c hc
    rw [show (2 * ds.length : Nat) = 2 * xs.length by rw [hds]] at hcb
    exact hcb
  have hg : 0 ≤ gamma M.u (2 * xs.length) :=
    gamma_nonneg M.u (2 * xs.length) M.u_nonneg hγ
  exact lsum_coef_error (gamma M.u (2 * xs.length)) hg
    (List.zipWith (· * ·) xs ys) (coefList ds es) hclen hbound

/-! ## One dense layer (rows = List (List Rat), self-contained) -/

/-- Floating dense layer: each row dotted with `x` by `flDot`. -/
noncomputable def flMulVec (M : RoundingModel) (rows : List (List Rat)) (x : List Rat) :
    List Rat := rows.map (flDot M · x)

/-- Exact dense layer: each row dotted with `x` by `ldot`. -/
def lMulVec (rows : List (List Rat)) (x : List Rat) : List Rat :=
  rows.map (ldot · x)

/-- `zipWith` of two mapped lists is the mapped pointwise difference. -/
theorem zipWith_map_sub {α : Type} (f g : α → Rat) : ∀ l : List α,
    List.zipWith (· - ·) (List.map f l) (List.map g l)
      = List.map (fun x => f x - g x) l
  | [] => rfl
  | x :: xs => by
      show (f x - g x) :: List.zipWith (· - ·) (List.map f xs) (List.map g xs)
          = (f x - g x) :: List.map (fun y => f y - g y) xs
      rw [zipWith_map_sub f g xs]

/-- **Row bound**: summing over the rows of the layer,
`Σ |flDot − dot| ≤ γₖ · Σᵢⱼ |Wⱼᵢ·xᵢ|` (all rows of length `n`, `k = n + 1`). -/
theorem flMulVec_row_error (M : RoundingModel) (rows : List (List Rat)) (x : List Rat)
    (n : Nat) (hrows : ∀ r ∈ rows, r.length = n) (hx : x.length = n)
    (hγ : ((2 * n : Nat) : Rat) * M.u < 1) :
    lsum (List.map Rat.abs (List.zipWith (· - ·) (flMulVec M rows x) (lMulVec rows x))) ≤
      gamma M.u (2 * n) *
        lsum (List.map Rat.abs
          (List.flatten (List.map (List.zipWith (· * ·) · x) rows))) := by
  unfold flMulVec lMulVec
  induction rows with
  | nil =>
      show lsum ([] : List Rat) ≤ gamma M.u (2 * n) * lsum []
      have hz : lsum ([] : List Rat) = 0 := rfl
      rw [hz, Rat.mul_zero]
      show (0 : Rat) ≤ 0
      exact Rat.le_refl
  | cons r rs ih =>
      have hr : r.length = n := hrows r (by simp)
      have hlen : r.length = x.length := by rw [hr, ← hx]
      have hrow : Rat.abs (flDot M r x - ldot r x) ≤
          gamma M.u (2 * r.length) * lsum (List.map Rat.abs (List.zipWith (· * ·) r x)) :=
        flDot_error M r x hlen (by rw [hr]; exact hγ)
      rw [hr] at hrow
      have htail := ih (fun q hq => hrows q (List.mem_cons.mpr (Or.inr hq)))
      have h1 : List.zipWith (· - ·)
            (List.map (flDot M · x) (r :: rs)) (List.map (ldot · x) (r :: rs))
          = (flDot M r x - ldot r x)
            :: List.map (fun q => flDot M q x - ldot q x) rs := by
        rw [zipWith_map_sub (flDot M · x) (ldot · x), List.map_cons]
      have hsumabs : lsum (List.map Rat.abs ((List.zipWith (· * ·) r x)
            ++ List.flatten (List.map (List.zipWith (· * ·) · x) rs)))
          = lsum (List.map Rat.abs (List.zipWith (· * ·) r x))
            + lsum (List.map Rat.abs
              (List.flatten (List.map (List.zipWith (· * ·) · x) rs))) := by
        rw [List.map_append, lsum_append]
      rw [h1, List.map_cons, lsum, List.map_cons, List.flatten_cons,
        hsumabs]
      have htail' : lsum (List.map Rat.abs
            (List.map (fun q => flDot M q x - ldot q x) rs))
          ≤ gamma M.u (2 * n)
            * lsum (List.map Rat.abs
              (List.flatten (List.map (List.zipWith (· * ·) · x) rs))) := by
        rw [show List.map (fun q => flDot M q x - ldot q x) rs
            = List.zipWith (· - ·) (List.map (flDot M · x) rs)
              (List.map (ldot · x) rs) from
          (zipWith_map_sub (flDot M · x) (ldot · x) rs).symm]
        exact htail
      have hdist : gamma M.u (2 * n)
          * (lsum (List.map Rat.abs (List.zipWith (· * ·) r x))
            + lsum (List.map Rat.abs
              (List.flatten (List.map (List.zipWith (· * ·) · x) rs))))
          = gamma M.u (2 * n) * lsum (List.map Rat.abs (List.zipWith (· * ·) r x))
            + gamma M.u (2 * n) * lsum (List.map Rat.abs
              (List.flatten (List.map (List.zipWith (· * ·) · x) rs))) := by
        grind
      refine Rat.le_trans (add_le_add hrow htail') ?_
      rw [hdist]
      exact Rat.le_refl

/-- `Σ aᵢ − Σ bᵢ = Σ (aᵢ − bᵢ)` over mapped lists. -/
theorem lsum_map_sub {α : Type} (f g : α → Rat) : ∀ l : List α,
    lsum (List.map f l) - lsum (List.map g l)
      = lsum (List.zipWith (· - ·) (List.map f l) (List.map g l))
  | [] => by
      show (lsum ([] : List Rat)) - lsum [] = lsum []
      show (0 : Rat) - 0 = 0
      grind
  | x :: xs => by
      show (f x + lsum (List.map f xs)) - (g x + lsum (List.map g xs))
          = (f x - g x)
            + lsum (List.zipWith (· - ·) (List.map f xs) (List.map g xs))
      rw [← lsum_map_sub f g xs]
      grind

/-- **Layer bound**: the whole dense layer obeys
`|Σ flMulVec − Σ lMulVec| ≤ γ₍₂ₙ₎ · Σᵢⱼ |Wⱼᵢ·xᵢ|` (all rows of length `n`):
the outer triangle inequality plus the row bound. -/

theorem flMulVec_error (M : RoundingModel) (rows : List (List Rat)) (x : List Rat)
    (n : Nat) (hrows : ∀ r ∈ rows, r.length = n) (hx : x.length = n)
    (hγ : ((2 * n : Nat) : Rat) * M.u < 1) :
    Rat.abs (lsum (flMulVec M rows x) - lsum (lMulVec rows x)) ≤
      gamma M.u (2 * n) *
        lsum (List.map Rat.abs
          (List.flatten (List.map (List.zipWith (· * ·) · x) rows))) := by
  have hzip : List.zipWith (· - ·) (flMulVec M rows x) (lMulVec rows x)
      = List.map (fun r => flDot M r x - ldot r x) rows := by
    unfold flMulVec lMulVec
    induction rows with
    | nil => rfl
    | cons r rs ih =>
        rw [zipWith_map_sub (flDot M · x) (ldot · x)]
  have hsum : lsum (flMulVec M rows x) - lsum (lMulVec rows x)
      = lsum (List.zipWith (· - ·) (flMulVec M rows x) (lMulVec rows x)) := by
    unfold flMulVec lMulVec
    exact lsum_map_sub (flDot M · x) (ldot · x) rows
  rw [hsum, hzip]
  have hrows' := flMulVec_row_error M rows x n hrows hx hγ
  rw [hzip] at hrows'
  calc Rat.abs (lsum (List.map (fun r => flDot M r x - ldot r x) rows))
      ≤ lsum (List.map Rat.abs (List.map (fun r => flDot M r x - ldot r x) rows)) :=
        lsum_abs_le _
    _ ≤ gamma M.u (2 * n) * _ := hrows'

end LeanDL
