import LeanDL.Ch06.Conv
import LeanDL.Ch05.Loss
import LeanDL.Ch04.Autodiff

/-!
# Chapter 9 — Attention: what can be proved

Four facts about the building blocks of a Transformer:
* attention weights are a probability distribution, and the softmax does not change when all
  scores are shifted (the stability trick of Chapter 5);
* attention does not see the *order* of its inputs (so positions must be injected);
* a causal mask really prevents information from the future from reaching a position;
* layer normalisation does not change when a constant is added to its input.
-/

namespace LeanDL.Ch09

open Lean.Grind LeanDL.Ch05 LeanDL.Ch04 LeanDL.Ch06

variable {α : Type} {n : Nat}

section Softmax

variable [Field α] [HasExp α]

-- ANCHOR: weights
/-- The attention weights of one query: softmax of its scores `z`. -/
def weights (z : Vec α n) : Vec α n :=
  fun i => HasExp.exp (z i) / vsum (fun j => HasExp.exp (z j))

/-- **The weights sum to one**, as soon as the normaliser is non-zero (it is positive for the
real exponential). -/
theorem weights_sum (z : Vec α n) (h : vsum (fun j => HasExp.exp (z j)) ≠ 0) :
    vsum (weights z) = 1 := by
  have e : weights z = fun i => (vsum (fun j => HasExp.exp (z j)))⁻¹ * HasExp.exp (z i) := by
    funext i; simp only [weights]; grind
  rw [e, vsum_smul]
  grind

/-- **Shift invariance**: subtracting the same constant from all scores changes nothing, which
is why implementations subtract the maximum before exponentiating. -/
theorem weights_shift [LawfulExp α] (z : Vec α n) (c : α)
    (h : vsum (fun j => HasExp.exp (z j)) ≠ 0) :
    weights (fun i => z i - c) = weights z := by
  have hm : HasExp.exp c * HasExp.exp (-c) = 1 := by
    rw [← LawfulExp.exp_add, show c + -c = 0 by grind, LawfulExp.exp_zero]
  have he : ∀ i, HasExp.exp (z i - c) = HasExp.exp (z i) * HasExp.exp (-c) := fun i => by
    rw [← LawfulExp.exp_add]; congr 1; grind
  have hs : vsum (fun j => HasExp.exp (z j - c)) =
      HasExp.exp (-c) * vsum (fun j => HasExp.exp (z j)) := by
    rw [← vsum_smul]; congr 1; funext j; rw [he]; grind
  funext i
  simp only [weights]
  rw [hs, he]
  have hE : HasExp.exp (-c) ≠ 0 := by
    intro h0; rw [h0] at hm; grind
  grind
-- ANCHOR_END: weights

end Softmax

section PermSum

variable [CommRing α]

theorem sumL_perm {l₁ l₂ : List α} (h : l₁.Perm l₂) : sumL l₁ = sumL l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [sumL_cons, ih]
  | swap a b l => simp only [sumL_cons]; grind
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

end PermSum

section Order

variable [Field α] [HasExp α]

-- ANCHOR: perm
/-- Attention of one query over a *list* of items, given a score and a value for each item. -/
def attendL {κ : Type} (items : List κ) (score val : κ → α) : α :=
  sumL (items.map fun i => HasExp.exp (score i) * val i) /
    sumL (items.map fun i => HasExp.exp (score i))


/-- **Attention is a function of a set, not of a sequence**: reordering the items does not
change the output. Without positional information a Transformer cannot tell "dog bites man" from
"man bites dog". -/
theorem attendL_perm {κ : Type} {l₁ l₂ : List κ} (h : l₁.Perm l₂) (score val : κ → α) :
    attendL l₁ score val = attendL l₂ score val := by
  simp only [attendL]
  rw [sumL_perm (h.map _), sumL_perm (h.map _)]
-- ANCHOR_END: perm

end Order

section Mask

variable [Field α] [HasExp α]

-- ANCHOR: mask
/-- Attention with a 0/1 mask `m`: masked positions get weight `0`. -/
def attendM (m s v : Vec α n) : α :=
  vsum (fun j => m j * HasExp.exp (s j) * v j) / vsum (fun j => m j * HasExp.exp (s j))

/-- The causal mask for position `t`: only positions `j ≤ t` are visible. -/
def causal (t : Nat) : Vec α n := fun j => if j.val ≤ t then 1 else 0

/-- **No leakage from the future.** If two inputs agree on the visible positions `j ≤ t`, the
causal attention output at position `t` is the same, whatever happens after `t`. -/
theorem causal_no_leak (t : Nat) (s v s' v' : Vec α n)
    (h : ∀ j : Fin n, j.val ≤ t → s j = s' j ∧ v j = v' j) :
    attendM (causal t) s v = attendM (causal t) s' v' := by
  have key : ∀ j : Fin n, (causal t : Vec α n) j * HasExp.exp (s j) * v j =
      (causal t : Vec α n) j * HasExp.exp (s' j) * v' j := by
    intro j
    by_cases hj : j.val ≤ t
    · obtain ⟨h1, h2⟩ := h j hj
      rw [h1, h2]
    · simp [causal, hj]; grind
  have key2 : ∀ j : Fin n, (causal t : Vec α n) j * HasExp.exp (s j) =
      (causal t : Vec α n) j * HasExp.exp (s' j) := by
    intro j
    by_cases hj : j.val ≤ t
    · rw [(h j hj).1]
    · simp [causal, hj]; grind
  simp only [attendM]
  rw [show (fun j : Fin n => (causal t : Vec α n) j * HasExp.exp (s j) * v j) =
      fun j => (causal t : Vec α n) j * HasExp.exp (s' j) * v' j from funext key,
    show (fun j : Fin n => (causal t : Vec α n) j * HasExp.exp (s j)) =
      fun j => (causal t : Vec α n) j * HasExp.exp (s' j) from funext key2]
-- ANCHOR_END: mask

end Mask

section Norm

variable [Field α] [HasAct α]

theorem vsum_add_const : ∀ {n : Nat} (x : Vec α n) (c : α),
    vsum (fun i => x i + c) = vsum x + cnt n * c := by
  intro n x c
  have := vsum_sub_const x (-c)
  have h : (fun i => x i + c) = fun i => x i - -c := by funext i; grind
  rw [h, this]
  grind

-- ANCHOR: layernorm
/-- The variance of the entries. -/
def variance (x : Vec α n) : α :=
  vsum (fun i => (x i - mean x) * (x i - mean x)) / cnt n

/-- Layer normalisation: centre, then divide by the standard deviation (`eps` avoids dividing
by zero). -/
def layerNorm (eps : α) (x : Vec α n) : Vec α n :=
  fun i => (x i - mean x) * HasAct.inv (HasAct.sqrt (variance x + eps))

/-- Adding the same constant to every entry does not change the output of layer norm. -/
theorem layerNorm_shift (eps c : α) (x : Vec α n) (hn : (cnt n : α) ≠ 0) :
    layerNorm eps (fun i => x i + c) = layerNorm eps x := by
  have hm : mean (fun i => x i + c) = mean x + c := by
    simp only [mean]
    rw [vsum_add_const]
    grind
  have hc : ∀ i, (x i + c) - mean (fun i => x i + c) = x i - mean x := fun i => by
    rw [hm]; grind
  have hv : variance (fun i => x i + c) = variance x := by
    simp only [variance]
    congr 2
    funext i
    rw [hc]
  funext i
  simp only [layerNorm]
  rw [hc, hv]
-- ANCHOR_END: layernorm

end Norm

end LeanDL.Ch09
