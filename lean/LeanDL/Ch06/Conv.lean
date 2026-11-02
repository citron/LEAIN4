import LeanDL.Ch05.Norm
import LeanDL.Core.Sum

/-!
# Chapter 6 — Convolution

A convolutional layer is a dense layer with two constraints: each output looks only at a small
window of the input (*locality*), and every window uses the same weights (*weight sharing*).
We study the one-dimensional case, where proofs are short, then run the two-dimensional case on
MNIST in `Cnn.lean`.
-/

namespace LeanDL.Ch06

open Lean.Grind LeanDL.Ch05

variable {α : Type}

-- ANCHOR: conv1d
/-- Valid 1-D convolution (in the machine-learning sense, i.e. cross-correlation).
A kernel of length `k + 1` over an input of length `m + k` gives exactly `m` outputs:
the shapes are checked by the type checker. -/
def conv1d [Add α] [Mul α] [OfNat α 0] {m k : Nat} (ker : Vec α (k + 1)) (x : Vec α (m + k)) :
    Vec α m :=
  fun i => vsum (fun j : Fin (k + 1) => ker j * x ⟨i.val + j.val, by omega⟩)
-- ANCHOR_END: conv1d

section Laws

variable [CommRing α]

-- ANCHOR: conv_linear
/-- Convolution is linear in the input… -/
theorem conv1d_add {m k : Nat} (ker : Vec α (k + 1)) (x y : Vec α (m + k)) :
    conv1d ker (fun i => x i + y i) = fun i => conv1d ker x i + conv1d ker y i := by
  funext i
  simp only [conv1d]
  rw [← vsum_add]
  congr 1
  funext j
  grind

theorem conv1d_smul {m k : Nat} (ker : Vec α (k + 1)) (c : α) (x : Vec α (m + k)) :
    conv1d ker (fun i => c * x i) = fun i => c * conv1d ker x i := by
  funext i
  simp only [conv1d]
  rw [← vsum_smul]
  congr 1
  funext j
  grind

/-- …and in the kernel. -/
theorem conv1d_add_ker {m k : Nat} (a b : Vec α (k + 1)) (x : Vec α (m + k)) :
    conv1d (fun j => a j + b j) x = fun i => conv1d a x i + conv1d b x i := by
  funext i
  simp only [conv1d]
  rw [← vsum_add]
  congr 1
  funext j
  grind
-- ANCHOR_END: conv_linear

-- ANCHOR: equivariance
/-- **Translation equivariance.** Shifting the input by one position shifts the output by one
position: this is what weight sharing buys. -/
theorem conv1d_shift {m k : Nat} (ker : Vec α (k + 1)) (x : Vec α (m + 1 + k)) (i : Fin m) :
    conv1d ker (fun p : Fin (m + k) => x ⟨p.val + 1, by omega⟩) i =
      conv1d ker x ⟨i.val + 1, by omega⟩ := by
  simp only [conv1d]
  congr 1
  funext j
  have : (⟨i.val + j.val + 1, by omega⟩ : Fin (m + 1 + k)) = ⟨i.val + 1 + j.val, by omega⟩ :=
    Fin.ext (by show i.val + j.val + 1 = i.val + 1 + j.val; omega)
  simp only [this]
-- ANCHOR_END: equivariance

-- ANCHOR: corr
/-- The cross-correlation of an upstream signal `s` with the input. -/
def corr {m k : Nat} (s : Vec α m) (x : Vec α (m + k)) : Vec α (k + 1) :=
  fun j => vsum (fun i : Fin m => s i * x ⟨i.val + j.val, by omega⟩)

/-- **The gradient with respect to the kernel is a correlation.** For the linear form
`ℓ(ker) = ∑ᵢ sᵢ · (ker ⋆ x)ᵢ` (with `s` the adjoint arriving from the next layer),
`ℓ(ker) = ∑ⱼ kerⱼ · corr s x j`, so `∂ℓ/∂kerⱼ = corr s x j`. -/
theorem conv1d_adjoint {m k : Nat} (ker : Vec α (k + 1)) (s : Vec α m) (x : Vec α (m + k)) :
    vsum (fun i => s i * conv1d ker x i) = vsum (fun j => ker j * corr s x j) := by
  have h1 : (fun i : Fin m => s i * conv1d ker x i) =
      fun i => vsum (fun j : Fin (k + 1) => s i * (ker j * x ⟨i.val + j.val, by omega⟩)) := by
    funext i
    simp only [conv1d]
    rw [vsum_smul]
  have h2 : (fun j : Fin (k + 1) => ker j * corr s x j) =
      fun j => vsum (fun i : Fin m => ker j * (s i * x ⟨i.val + j.val, by omega⟩)) := by
    funext j
    simp only [corr]
    rw [vsum_smul]
  rw [h1, h2, vsum_comm]
  congr 1
  funext j
  congr 1
  funext i
  grind
-- ANCHOR_END: corr

end Laws

end LeanDL.Ch06
