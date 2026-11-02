import LeanDL.Core.Vec

/-!
# Sums over finite vectors

`vsum` adds the entries of a `Vec`; `cnt` builds the scalar `n` by counting
(avoids any cast lemma). These are Core-level primitives: attention (Ch09),
convolution (Ch06) and normalisation (Ch05) all build on them, so they live
below every chapter. -/

namespace LeanDL

open Lean.Grind

variable {α : Type}

/-- The scalar `n`, built by counting (avoids any cast lemma). -/
def cnt [Add α] [OfNat α 0] [OfNat α 1] : Nat → α
  | 0 => 0
  | n + 1 => cnt n + 1

/-- Sum of the entries. -/
def vsum [Add α] [OfNat α 0] : {n : Nat} → Vec α n → α
  | 0, _ => 0
  | _ + 1, x => x 0 + vsum (fun i => x i.succ)

section Laws

variable [CommRing α]

theorem vsum_add : ∀ {n : Nat} (f g : Fin n → α),
    vsum (fun i => f i + g i) = vsum f + vsum g
  | 0, f, g => by simp only [vsum]; grind
  | n + 1, f, g => by
    have ih := vsum_add (fun i : Fin n => f i.succ) (fun i => g i.succ)
    simp only [vsum]
    rw [ih]
    grind

theorem vsum_smul : ∀ {n : Nat} (c : α) (f : Fin n → α),
    vsum (fun i => c * f i) = c * vsum f
  | 0, c, f => by simp only [vsum]; grind
  | n + 1, c, f => by
    have ih := vsum_smul c (fun i : Fin n => f i.succ)
    simp only [vsum]
    rw [ih]
    grind

theorem vsum_zero : ∀ {n : Nat}, vsum (fun _ : Fin n => (0 : α)) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := vsum_zero (n := n)
    simp only [vsum]
    rw [ih]
    grind

/-- Exchanging the order of a double sum. -/
theorem vsum_comm : ∀ {m n : Nat} (f : Fin m → Fin n → α),
    vsum (fun i => vsum (f i)) = vsum (fun j => vsum (fun i => f i j))
  | 0, n, f => by
    simp only [vsum]
    exact vsum_zero.symm
  | m + 1, n, f => by
    have ih := vsum_comm (fun (i : Fin m) => f i.succ)
    have h : (fun j : Fin n => vsum (fun i : Fin (m + 1) => f i j)) =
        fun j => f 0 j + vsum (fun i : Fin m => f i.succ j) := rfl
    rw [h, vsum_add]
    simp only [vsum]
    rw [ih]



section RatLaws

/-- The sum of a constant. -/
theorem vsum_const : ∀ (n : Nat) (c : Rat), vsum (fun _ : Fin n => c) = (n : Rat) * c
  | 0, c => by simp only [vsum]; grind
  | n + 1, c => by
      rw [vsum, vsum_const n c]
      push_cast
      grind

/-- A sum of nonnegative rationals is nonnegative. -/
theorem vsum_nonneg : ∀ (n : Nat) (f : Fin n → Rat), (∀ i, 0 ≤ f i) → 0 ≤ vsum f
  | 0, f, h => by simp only [vsum]; grind
  | n + 1, f, h => by
      rw [vsum]
      exact Rat.add_nonneg (h ⟨0, Nat.succ_pos n⟩)
        (vsum_nonneg n (fun i => f i.succ) (fun i => h i.succ))

end RatLaws

end Laws

end LeanDL
