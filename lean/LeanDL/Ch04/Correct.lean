import LeanDL.Ch04.Autodiff

/-!
# Chapter 4, part 2 — Both modes compute the formal derivative
-/

namespace LeanDL.Ch04

open Lean.Grind

variable {α : Type} {n : Nat} [CommRing α] [HasAct α]

theorem dot_basis : ∀ {n : Nat} (dx : Vec α n) (i : Fin n),
    Vec.dot dx (fun j => if i = j then (1 : α) else 0) = dx i
  | 0, _, i => i.elim0
  | n + 1, dx, i => by
    cases i using Fin.cases with
    | zero =>
      have h0 := Vec.dot_zero_left (fun j : Fin n => dx j.succ)
      rw [Vec.dot_comm] at h0
      simp only [Vec.dot]
      have : (fun j : Fin n => if (0 : Fin (n + 1)) = j.succ then (1 : α) else 0) = fun _ => 0 := by
        funext j; simp [Fin.succ_ne_zero j |>.symm]
      rw [this, h0]
      simp
      grind
    | succ k =>
      have ih := dot_basis (fun j : Fin n => dx j.succ) k
      simp only [Vec.dot]
      have : (fun j : Fin n => if k.succ = j.succ then (1 : α) else 0) =
          fun j => if k = j then (1 : α) else 0 := by
        funext j; simp [Fin.succ_inj]
      rw [this, ih]
      grind

-- ANCHOR: fwd_correct
/-- Forward mode returns the value of the expression. -/
theorem fwd_value (x dx : Vec α n) (e : Expr α n) : (e.fwd x dx).1 = e.eval x := by
  induction e with
  | var i => rfl
  | const c => rfl
  | add a b iha ihb => simp only [Expr.fwd, Expr.eval, iha, ihb]
  | sub a b iha ihb => simp only [Expr.fwd, Expr.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expr.fwd, Expr.eval, iha, ihb]
  | exp a iha => simp only [Expr.fwd, Expr.eval, iha]
  | sigmoid a iha => simp only [Expr.fwd, Expr.eval, iha]
  | tanh a iha => simp only [Expr.fwd, Expr.eval, iha]
  | log a iha => simp only [Expr.fwd, Expr.eval, iha]
  | inv a iha => simp only [Expr.fwd, Expr.eval, iha]
  | sqrt a iha => simp only [Expr.fwd, Expr.eval, iha]
  | relu a iha => simp only [Expr.fwd, Expr.eval, iha]
  | step a iha => simp only [Expr.fwd, Expr.eval, iha]

/-- Forward mode returns the directional derivative: `∑ᵢ dxᵢ · ∂ᵢe`. -/
theorem fwd_tangent (x dx : Vec α n) (e : Expr α n) :
    (e.fwd x dx).2 = Vec.dot dx (fun j => (e.deriv j).eval x) := by
  induction e with
  | var i => simp only [Expr.fwd, Expr.deriv, Expr.eval]; rw [dot_basis]
  | const c =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval]
    rw [Vec.dot_comm]
    exact (Vec.dot_zero_left dx).symm
  | add a b iha ihb =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, iha, ihb]
    rw [Vec.dot_add_right]
  | sub a b iha ihb =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, iha, ihb]
    have : (fun j => (a.deriv j).eval x - (b.deriv j).eval x) =
        fun j => (a.deriv j).eval x + (-1) * (b.deriv j).eval x := by
      funext j; grind
    rw [this, Vec.dot_add_right, Vec.dot_smul_right]
    grind
  | mul a b iha ihb =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha, ihb]
    have : (fun j => (a.deriv j).eval x * b.eval x + a.eval x * (b.deriv j).eval x) =
        fun j => b.eval x * (a.deriv j).eval x + a.eval x * (b.deriv j).eval x := by
      funext j; grind
    rw [this, Vec.dot_add_right, Vec.dot_smul_right, Vec.dot_smul_right]
    grind
  | exp a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | sigmoid a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | tanh a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | log a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | inv a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | sqrt a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | relu a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval, fwd_value, iha]
    rw [Vec.dot_smul_right]
  | step a iha =>
    simp only [Expr.fwd, Expr.deriv, Expr.eval]
    rw [Vec.dot_comm]
    exact (Vec.dot_zero_left dx).symm
-- ANCHOR_END: fwd_correct

-- ANCHOR: back_correct
/-- Invariant of the backward sweep: sizes are preserved, and the sweep *adds* `s · ∂ⱼe` to
coordinate `j` of the accumulator. -/
theorem back_spec (x : Vec α n) (e : Expr α n) :
    ∀ (s : α) (acc : Array α), acc.size = n →
      (e.back x s acc).size = n ∧
      ∀ j : Fin n, (e.back x s acc).getD j.val 0 = acc.getD j.val 0 + s * (e.deriv j).eval x := by
  induction e with
  | var i =>
    intro s acc h
    refine ⟨by simp [Expr.back, h], fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    by_cases hij : i = j
    · subst hij
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, h]
      grind
    · have : i.val ≠ j.val := fun h' => hij (Fin.ext h')
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hij, this]
      grind
  | const c =>
    intro s acc h
    refine ⟨h, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    grind
  | add a b iha ihb =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha s acc h
    obtain ⟨h2, g2⟩ := ihb s _ h1
    refine ⟨h2, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g2, g1]; grind
  | sub a b iha ihb =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha s acc h
    obtain ⟨h2, g2⟩ := ihb (0 - s) _ h1
    refine ⟨h2, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g2, g1]; grind
  | mul a b iha ihb =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * b.eval x) acc h
    obtain ⟨h2, g2⟩ := ihb (s * a.eval x) _ h1
    refine ⟨h2, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g2, g1]; grind
  | exp a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * HasExp.exp (a.eval x)) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | sigmoid a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * (HasAct.sigmoid (a.eval x) * (1 - HasAct.sigmoid (a.eval x)))) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | tanh a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * (1 - HasAct.tanh (a.eval x) * HasAct.tanh (a.eval x))) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | log a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * HasAct.inv (a.eval x)) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | inv a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * (0 - HasAct.inv (a.eval x) * HasAct.inv (a.eval x))) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | sqrt a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * HasAct.inv (HasAct.sqrt (a.eval x) + HasAct.sqrt (a.eval x))) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | relu a iha =>
    intro s acc h
    obtain ⟨h1, g1⟩ := iha (s * HasAct.step (a.eval x)) acc h
    refine ⟨h1, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    rw [g1]; grind
  | step a iha =>
    intro s acc h
    refine ⟨h, fun j => ?_⟩
    simp only [Expr.back, Expr.deriv, Expr.eval]
    grind

/-- **Backpropagation is correct**: one backward sweep returns every partial derivative. -/
theorem backprop_correct (x : Vec α n) (e : Expr α n) (j : Fin n) :
    (e.backprop x).getD j.val 0 = (e.deriv j).eval x := by
  have h := (back_spec x e 1 (Array.replicate n 0) (by simp)).2 j
  simp only [Expr.backprop]
  rw [h]
  simp [Array.getD_eq_getD_getElem?]
  grind

/-- Reverse mode is the transpose of forward mode: the directional derivative of `e` along
`dx` equals `dx · ∇e`, with `∇e` computed by backpropagation. -/
theorem forward_eq_dot_backprop (x dx : Vec α n) (e : Expr α n) :
    (e.fwd x dx).2 = Vec.dot dx (fun j => (e.backprop x).getD j.val 0) := by
  rw [fwd_tangent]
  congr 1
  funext j
  rw [backprop_correct]
-- ANCHOR_END: back_correct
end LeanDL.Ch04
