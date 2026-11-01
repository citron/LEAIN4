import LeanDL.Ch04.Network

/-!
# Chapter 5, part 1 — Losses and regularisation, with their gradients

Because losses are `Expr`s, `backprop_correct` gives their gradients for free. Here we also
*identify* those gradients with the textbook formulas.
-/

namespace LeanDL.Ch05

open Lean.Grind LeanDL.Ch04

variable {α : Type} {n : Nat}

/-- Sum of a list. -/
def sumL [Add α] [OfNat α 0] (l : List α) : α := l.foldr (· + ·) 0

section Sums

variable [CommRing α] [HasAct α]

theorem sumL_cons (a : α) (l : List α) : sumL (a :: l) = a + sumL l := rfl

theorem eval_sum (x : Vec α n) : ∀ l : List (Expr α n),
    (Expr.sum l).eval x = sumL (l.map fun e => e.eval x)
  | [] => rfl
  | e :: l => by rw [List.map_cons, sumL_cons, ← eval_sum x l]; rfl

theorem deriv_sum (j : Fin n) : ∀ l : List (Expr α n),
    (Expr.sum l).deriv j = Expr.sum (l.map fun e => e.deriv j)
  | [] => rfl
  | e :: l => congrArg (Expr.add (e.deriv j)) (deriv_sum j l)

/-- The derivative of a sum is the sum of the derivatives. -/
theorem eval_deriv_sum (x : Vec α n) (j : Fin n) (l : List (Expr α n)) :
    ((Expr.sum l).deriv j).eval x = sumL (l.map fun e => (e.deriv j).eval x) := by
  rw [deriv_sum, eval_sum, List.map_map]
  rfl

theorem sumL_zero : ∀ l : List (Fin n), sumL (l.map fun _ => (0 : α)) = 0
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, sumL_cons, sumL_zero l]; grind

/-- Summing `f i · [i = k]` over a list that contains `k` once picks out `f k`. -/
theorem sumL_indicator (f : Fin n → α) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → k ∈ l →
      sumL (l.map fun i => f i * (if i = k then (1 : α) else 0)) = f k
  | [], _, h => absurd h (by simp)
  | a :: l, hnd, hk => by
    simp only [List.map_cons, sumL_cons]
    by_cases ha : a = k
    · subst ha
      have hl : ∀ i ∈ l, i ≠ a := fun i hi h => (List.nodup_cons.mp hnd).1 (h ▸ hi)
      have : (l.map fun i => f i * (if i = a then (1 : α) else 0)) = l.map fun _ => (0 : α) :=
        List.map_congr_left fun i hi => by simp only [hl i hi, ite_false]; grind
      rw [this, sumL_zero]
      simp
      grind
    · have hk' : k ∈ l := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm ha
        · exact h
      rw [sumL_indicator f k l (List.nodup_cons.mp hnd).2 hk']
      simp [ha]
      grind

end Sums

section Softmax

variable [CommRing α] [HasAct α]

-- ANCHOR: softmax_loss
/-- Cross-entropy of the softmax with true class `y`, in log-sum-exp form:
`log (∑ᵢ exp zᵢ) - z_y`. -/
def ceLoss {m : Nat} (y : Fin m) : Expr α m :=
  .sub (.log (Expr.sum ((List.finRange m).map fun i => .exp (.var i)))) (.var y)

/-- The softmax probability of class `k`. -/
def softmax {m : Nat} (z : Vec α m) (k : Fin m) : α :=
  HasExp.exp (z k) * HasAct.inv (sumL ((List.finRange m).map fun i => HasExp.exp (z i)))

/-- The gradient of the cross-entropy with respect to the logits is `softmax z - onehot y`. -/
theorem ceLoss_grad {m : Nat} (z : Vec α m) (y k : Fin m) :
    ((ceLoss y).deriv k).eval z = softmax z k - (if y = k then 1 else 0) := by
  have hsum : sumL (((List.finRange m).map fun i => (Expr.exp (Expr.var i) : Expr α m)).map
      fun e => (e.deriv k).eval z) = HasExp.exp (z k) := by
    have := sumL_indicator (fun i => HasExp.exp (z i)) k (List.finRange m)
      (List.nodup_finRange m) (List.mem_finRange k)
    rw [← this, List.map_map]
    congr 1
  have hS : sumL (((List.finRange m).map fun i => (Expr.exp (Expr.var i) : Expr α m)).map
      fun e => e.eval z) = sumL ((List.finRange m).map fun i => HasExp.exp (z i)) := by
    rw [List.map_map]; rfl
  simp only [ceLoss, Expr.deriv, Expr.eval]
  rw [eval_deriv_sum, eval_sum, hsum, hS]
  simp only [softmax]
  grind
-- ANCHOR_END: softmax_loss

end Softmax

section L2

variable [CommRing α] [HasAct α]

-- ANCHOR: l2
/-- `c · ∑ᵢ wᵢ²`, the L2 penalty with coefficient `c` (take `c = λ/2`). -/
def l2Penalty {m : Nat} (c : α) : Expr α m :=
  .mul (.const c) (Expr.sum ((List.finRange m).map fun i => .mul (.var i) (.var i)))

/-- Weight decay: the gradient of the L2 penalty is `2 c wₖ`. -/
theorem l2_grad {m : Nat} (c : α) (w : Vec α m) (k : Fin m) :
    ((l2Penalty c).deriv k).eval w = 2 * c * w k := by
  have h := sumL_indicator (fun i => 2 * w i) k (List.finRange m) (List.nodup_finRange m)
    (List.mem_finRange k)
  have hs : sumL (((List.finRange m).map fun i => (Expr.mul (Expr.var i) (Expr.var i) : Expr α m)).map
      fun e => (e.deriv k).eval w) = 2 * w k := by
    rw [← h, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Expr.deriv, Expr.eval]
    by_cases hik : i = k
    · simp [hik]; grind
    · simp [hik]; grind
  simp only [l2Penalty, Expr.deriv, Expr.eval]
  rw [eval_deriv_sum, hs]
  grind
-- ANCHOR_END: l2

end L2

end LeanDL.Ch05
