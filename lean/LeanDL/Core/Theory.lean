import LeanDL.Core.Prob

/-!
# Learning theory: what any learner can and cannot do

Three exact facts that bound the whole enterprise, proved on `Rat` with the
finite probability layer of `Core/Prob.lean`:

- the **union-bound atom**: with nonnegative weights, an expectation
  dominates its head term - the counting argument behind every
  "with probability at least 1 - M*delta, every hypothesis in the class
  is good" statement;
- **the coin expectation**: under the uniform law the expectation of a
  loss profile is its average over the two labels - the same number
  computes train risk and test risk for a fixed hypothesis;
- **No Free Lunch, atom**: under labels drawn uniformly, every
  prediction - deterministic or randomized - has expected 0-1 error
  exactly 1/2. On average over all labelings, no learner beats chance;
  every advantage of a learner is an assumption about the data.

The statements are exact. Their high-probability translations
(Hoeffding, Chernoff) are analytic facts about `exp`; where chapters use
them we say so, we do not hide the step.
-/

namespace LeanDL.Theory

open Lean.Grind

/-! ### The union-bound atom -/

/-- A weighted sum of nonnegative terms is nonnegative. -/
theorem dot_nonneg : ∀ {n : Nat} (w f : Vec Rat n),
    (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ f i) → 0 ≤ Vec.dot w f := by
  intro n
  induction n with
  | zero =>
      intro w f _ _
      show 0 ≤ 0
      grind
  | succ n ih =>
      intro w f hw hf
      show 0 ≤ w 0 * f 0 + Vec.dot (fun i => w i.succ) (fun i => f i.succ)
      have h0 : 0 ≤ w 0 * f 0 := Rat.mul_nonneg (hw 0) (hf 0)
      have ht := ih (fun i => w i.succ) (fun i => f i.succ)
        (fun i => hw i.succ) (fun i => hf i.succ)
      grind

-- ANCHOR: unionbound
/-- **Union-bound atom.** With nonnegative weights, an expectation
dominates its head term: the total is at least any single weighted
loss. Iterating this over the class index is exactly how a
finite-class generalization bound "P(some hypothesis bad) ≤
Σₕ P(h bad) ≤ M·δ" is proved: the union bound *is* this inequality,
iterated. -/
theorem dot_ge_head {n : Nat} (w f : Vec Rat (n + 1))
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    Vec.dot w f ≥ w 0 * f 0 := by
  show w 0 * f 0 + Vec.dot (fun i => w i.succ) (fun i => f i.succ) ≥ w 0 * f 0
  have ht := dot_nonneg (fun i => w i.succ) (fun i => f i.succ)
    (fun i => hw i.succ) (fun i => hf i.succ)
  grind
-- ANCHOR_END: unionbound

/-! ### The coin expectation (train = test for a fixed hypothesis) -/

-- ANCHOR: symmetry
/-- The **fair coin** on two labels: each label has weight `1/2`. -/
def coin : Dist 2 := by
  refine ⟨fun _ => (2 : Rat)⁻¹, fun _ => Rat.inv_pos.mpr (by decide), ?_⟩
  show (2⁻¹ : Rat) * 1 + ((2⁻¹ : Rat) * 1 + 0) = 1
  grind

/-- **Coin expectation.** Under the fair coin, the expectation of any
loss profile `f` is the average of its two values. Both roles -
"training point" and "test point" - are the same law `coin`, so a
hypothesis chosen *independently of the test point* has the same
expectation in both roles: the number computed is identical. The
generalization gap a held-out set measures is exactly the dependence
introduced by fitting. -/
theorem coin_expect_avg (f : Vec Rat 2) : coin.expect f = (f 0 + f 1) / 2 := by
  unfold Dist.expect coin
  show (2⁻¹ : Rat) * f 0 + Vec.dot (fun i => (2 : Rat)⁻¹) (fun i => f i.succ)
      = (f 0 + f 1) / 2
  have htail : Vec.dot (fun i => (2 : Rat)⁻¹) (fun i => f i.succ)
      = (2⁻¹ : Rat) * f 1 := by
    show (2⁻¹ : Rat) * f 1 + Vec.dot (fun (i : Fin 0) => (2 : Rat)⁻¹) (fun (i : Fin 0) => f i.succ.succ)
        = (2⁻¹ : Rat) * f 1
    unfold Vec.dot
    grind
  rw [htail, Rat.div_def]
  grind
-- ANCHOR_END: symmetry

/-! ### No Free Lunch: the atom -/

-- ANCHOR: nfl
/-- The 0-1 loss of predicting `y` against a label drawn from the coin:
`err y i = 1` exactly when `y` differs from `i` (and `0` when it
matches), written exactly as `(y - i)²` on `{0, 1}`. -/
def err (y : Fin 2) : Vec Rat 2 :=
  fun i => ((y.val : Rat) - (i.val : Rat)) ^ 2

/-- **No Free Lunch, atom.** Under uniform labels, *every* prediction
has expected 0-1 error exactly `1/2`: no deterministic learner beats
chance on average over all labelings. -/
theorem nfl_coin (y : Fin 2) : coin.expect (err y) = 1 / 2 := by
  unfold Dist.expect coin
  show (2⁻¹ : Rat) * err y 0 + Vec.dot (fun i => (2 : Rat)⁻¹) (fun i => err y i.succ) = 1 / 2
  have htail : Vec.dot (fun i => (2 : Rat)⁻¹) (fun i => err y i.succ)
      = (2⁻¹ : Rat) * err y 1 := by
    show (2⁻¹ : Rat) * err y 1
        + Vec.dot (fun (i : Fin 0) => (2 : Rat)⁻¹) (fun (i : Fin 0) => err y i.succ.succ)
        = (2⁻¹ : Rat) * err y 1
    unfold Vec.dot
    grind
  rw [htail]
  cases y with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · show (2⁻¹ : Rat) * (((0 : Nat) : Rat) - 0) ^ 2
          + (2⁻¹ : Rat) * (((0 : Nat) : Rat) - 1) ^ 2 = 1 / 2
      grind
    · show (2⁻¹ : Rat) * (((1 : Nat) : Rat) - 0) ^ 2
          + (2⁻¹ : Rat) * (((1 : Nat) : Rat) - 1) ^ 2 = 1 / 2
      grind

/-- **No Free Lunch, randomized.** Mixing predictions by any
distribution `q` on the two labels: the expected error is a convex
combination of `1/2`s, so it is still exactly `1/2`. Randomness buys
nothing on average over labelings. -/
theorem nfl_coin_mix (q : Dist 2) :
    q.expect (fun y => coin.expect (err y)) = 1 / 2 := by
  have h : (fun y => coin.expect (err y)) = (fun _ => (1 / 2 : Rat)) := by
    funext y
    exact nfl_coin y
  rw [h, q.expect_const]
-- ANCHOR_END: nfl

end LeanDL.Theory
