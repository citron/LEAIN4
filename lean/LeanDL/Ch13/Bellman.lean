import LeanDL.Core.Prob
import LeanDL.Core.Algebra
import LeanDL.Ch13.Rl

/-!
# Chapter 13, part 2 — A finite MDP, the Bellman operator, and its contraction

This is the deterministic fixed-point theory behind value iteration, on a **finite** MDP
with a **fixed policy**: a finite state set, exact rational rewards `r`, exact rational
transition distributions `P s : Dist S`, and a discount `0 ≤ γ < 1`.

Three exact results, all over `Rat`:

* the Bellman operator `T` is a **contraction in the sup norm** (`cheb_le`): the largest
  statewise difference between `T V` and `T W` shrinks by the factor `γ`;
* the value function is **unique** (`fixed_point_unique`): two fixed points of `T` are equal;
* **value iteration converges geometrically** (`vIter_rate`): iterating `T` from any start
  vector, the sup-norm error after `k` sweeps is at most `γᵏ` times the initial error.

Honesty note: this is the contraction of the *deterministic* Bellman operator of a fixed
policy. It is not a convergence proof for stochastic Q-learning: the noise in a sampled
update, the exploration schedule, and the function-approximation gap are out of scope here
(Chapter 13's TD lemma bounds the shrinkage of one sampled update's error, nothing more).
-/

namespace LeanDL.Ch13

open Lean.Grind LeanDL

section Chebyshev

/-- The sup norm of a finite vector, as `max |v i|` (over the empty vector: `0`). -/
def maxV : {n : Nat} → Vec Rat n → Rat
  | 0, _ => 0
  | (_n + 1), v => max (v 0) (maxV fun i => v i.succ)

/-- Every coordinate is bounded by the sup norm. -/
theorem le_maxV : ∀ {n : Nat} (v : Vec Rat n) (i : Fin n), v i ≤ maxV v := by
  intro n
  induction n with
  | zero => intro v i; exact absurd i.isLt (by simp)
  | succ n ih =>
    intro v i
    have hstep : maxV v = max (v 0) (maxV fun i => v i.succ) := rfl
    rcases Nat.eq_zero_or_pos i.val with h0 | hm
    · rw [show v i = v 0 from congrArg v (Fin.eq_of_val_eq h0), hstep]
      grind
    · have hlt : i.val - 1 < n := by omega
      let j : Fin n := ⟨i.val - 1, hlt⟩
      have hsj : Fin.succ j = i := by
        apply Fin.ext
        show (i.val - 1) + 1 = i.val
        omega
      have h2 : (fun i => v i.succ) j = v i := by
        show v (Fin.succ j) = v i
        rw [hsj]
      have := ih (fun i => v i.succ) j
      rw [hstep, ← h2]
      grind

/-- The sup norm is the **least** upper bound. -/
theorem maxV_le : ∀ {n : Nat} (v : Vec Rat n) (M : Rat), 0 ≤ M →
    (∀ i, v i ≤ M) → maxV v ≤ M := by
  intro n
  induction n with
  | zero => intro v M hM _; exact hM
  | succ n ih =>
    intro v M hM h
    have hstep : maxV v = max (v 0) (maxV fun i => v i.succ) := rfl
    rw [hstep]
    have h1 : v 0 ≤ M := h 0
    have h2 : maxV (fun i => v i.succ) ≤ M := ih (fun i => v i.succ) M hM (fun i => h i.succ)
    grind

/-- A sup norm of absolute values is nonnegative. -/
theorem maxV_abs_nonneg : ∀ {n : Nat} (v : Vec Rat n), 0 ≤ maxV (fun i => (v i).abs) := by
  intro n
  induction n with
  | zero => intro v; show 0 ≤ 0; exact Rat.le_refl
  | succ n ih =>
    intro v
    have hstep : maxV (fun i => (v i).abs) = max (v 0).abs (maxV fun i => (v i.succ).abs) := rfl
    rw [hstep]
    have h0 : 0 ≤ (v 0).abs := by grind [Rat.abs.eq_1]
    have ht : 0 ≤ maxV (fun i => (v i.succ).abs) := ih (fun i => v i.succ)
    grind

/-- **The contraction core**: `0 ≤ a`, `γ < 1` and `a ≤ γ · a` force `a = 0`.
Everything below runs through this one line of algebra. -/
theorem le_self_mul_of_lt : ∀ (a g : Rat), 0 ≤ a → g < 1 → a ≤ g * a → a ≤ 0 := by
  intro a g ha hg h
  by_cases hz : 0 < a
  · have h1 : 0 < (1 - g) * a := Rat.mul_pos (by grind) hz
    have h2 : (1 - g) * a = a - g * a := by grind
    rw [h2] at h1
    grind
  · grind

end Chebyshev

section Mdp

/-- A **finite MDP with a fixed policy**: rewards `r s`, the next-state distribution
`P s` after following the policy from `s`, and a discount `0 ≤ γ < 1`. Transitions are
exact rational distributions (Core `Dist`), so every quantity below is exact. -/
-- ANCHOR: mdp
structure PolicyMdp (S : Nat) where
  r : Vec Rat S
  P : Fin S → Dist S
  γ : Rat
  hg0 : 0 ≤ γ
  hg1 : γ < 1

/-- The **Bellman operator** of the policy: `T V s = r s + γ · E_{s' ~ P s} V s'`. -/
def T {S : Nat} (m : PolicyMdp S) (V : Vec Rat S) (s : Fin S) : Rat :=
  m.r s + m.γ * (m.P s).expect V

/-- The rewards cancel in the difference: `T V - T W` is the discounted expectation
of `V - W` alone. -/
theorem T_sub {S : Nat} (m : PolicyMdp S) (V W : Vec Rat S) (s : Fin S) :
    T m V s - T m W s = m.γ * (m.P s).expect (fun i => V i - W i) := by
  simp only [T, Dist.expect]
  rw [dot_sub]
  grind

-- ANCHOR_END: mdp
end Mdp

section Contraction

/-- **Bellman contraction in the sup norm.** The largest statewise gap between `T V`
and `T W` is at most `γ` times the largest gap between `V` and `W`. Each state's gap is a
`γ`-weighted *expectation* of coordinate gaps, and an expectation of bounded quantities
is bounded (`Dist.expect_abs_bound`). -/
-- ANCHOR: contraction
theorem cheb_le {S : Nat} (m : PolicyMdp S) (V W : Vec Rat S) :
    maxV (fun s => (T m V s - T m W s).abs) ≤ m.γ * maxV (fun s => (V s - W s).abs) := by
  apply maxV_le
  · exact Rat.mul_nonneg m.hg0 (maxV_abs_nonneg (fun s => V s - W s))
  · intro s
    rw [T_sub]
    have hga : m.γ.abs = m.γ := by grind [Rat.abs.eq_1, m.hg0]
    have hb : (m.γ * (m.P s).expect (fun i => V i - W i)).abs
        = m.γ * ((m.P s).expect (fun i => V i - W i)).abs := by
      rw [abs_mul, hga]
    rw [hb]
    apply Rat.mul_le_mul_of_nonneg_left
    · exact Dist.expect_abs_bound (m.P s) (fun i => V i - W i)
        (maxV (fun s => (V s - W s).abs))
        (fun i => le_maxV (fun s => (V s - W s).abs) i)
    · exact m.hg0

/-- **Uniqueness of the value function.** If `V` and `W` are both fixed points of `T`,
their sup-norm gap `a` satisfies `a ≤ γ · a`, and the contraction core forces `a = 0`. -/
theorem fixed_point_unique {S : Nat} (m : PolicyMdp S) (V W : Vec Rat S)
    (hV : ∀ s, T m V s = V s) (hW : ∀ s, T m W s = W s) : V = W := by
  have hcheb : maxV (fun s => (V s - W s).abs) ≤ m.γ * maxV (fun s => (V s - W s).abs) := by
    have H := cheb_le m V W
    have heq : (fun s => (T m V s - T m W s).abs) = (fun s => (V s - W s).abs) := by
      funext s; rw [hV s, hW s]
    rw [heq] at H
    exact H
  have h0 : 0 ≤ maxV (fun s => (V s - W s).abs) := maxV_abs_nonneg (fun s => V s - W s)
  have hz : maxV (fun s => (V s - W s).abs) ≤ 0 :=
    le_self_mul_of_lt _ m.γ h0 m.hg1 hcheb
  funext s
  have hle : (V s - W s).abs ≤ maxV (fun s => (V s - W s).abs) :=
    le_maxV (fun s => (V s - W s).abs) s
  have hz' : (V s - W s).abs ≤ 0 := Rat.le_trans hle hz
  have hA : 0 ≤ (V s - W s).abs := by grind [Rat.abs.eq_1]
  grind [Rat.abs.eq_1]

-- ANCHOR_END: contraction
end Contraction

section ValueIteration

/-- Value iteration: `vIter k` = `k` sweeps of the Bellman operator from `V0`. -/
def vIter {S : Nat} (m : PolicyMdp S) (V0 : Vec Rat S) : Nat → Vec Rat S
  | 0 => V0
  | k + 1 => fun s => T m (vIter m V0 k) s

/-- **Geometric convergence of value iteration.** For any start vector, the sup-norm
error after `k` sweeps is at most `γᵏ` times the initial error. The rate is the proved
contraction factor `γ` of `cheb_le`, multiplied out by induction. -/
-- ANCHOR: viter
theorem vIter_rate {S : Nat} (m : PolicyMdp S) (V0 vs : Vec Rat S)
    (hfix : ∀ s, T m vs s = vs s) (k : Nat) :
    maxV (fun s => (vIter m V0 k s - vs s).abs)
      ≤ pw m.γ k * maxV (fun s => (V0 s - vs s).abs) := by
  induction k with
  | zero =>
      simp only [vIter, pw]
      grind
  | succ k ih =>
      simp only [vIter, pw]
      have hc := cheb_le m (vIter m V0 k) vs
      have heq : (fun s => (T m (vIter m V0 k) s - vs s).abs)
          = (fun s => (T m (vIter m V0 k) s - T m vs s).abs) := by
        funext s; rw [hfix s]
      rw [heq]
      have hm := Rat.mul_le_mul_of_nonneg_left ih m.hg0
      grind [Rat.mul_assoc]

-- ANCHOR_END: viter
end ValueIteration

end LeanDL.Ch13
