import LeanDL.Core.Vec

/-!
# Matrices with their shape in the type

`Mat α m n` has `m` rows and `n` columns. Multiplying by a vector of the wrong length is a
type error.
-/

namespace LeanDL

variable {α : Type}

-- ANCHOR: mat
/-- `m` rows, each a vector of length `n`. -/
abbrev Mat (α : Type) (m n : Nat) := Fin m → Vec α n

/-- Matrix–vector product: the `i`-th output is the dot product of row `i` with `x`. -/
def Mat.mulVec [Add α] [Mul α] [OfNat α 0] {m n : Nat} (A : Mat α m n) (x : Vec α n) : Vec α m :=
  fun i => Vec.dot (A i) x
-- ANCHOR_END: mat

/-- A vector from a list; missing entries are `0`. Handy for small literals. -/
def Vec.ofList [OfNat α 0] {n : Nat} (l : List α) : Vec α n := fun i => l.getD i.val 0

/-- A matrix from a list of rows. -/
def Mat.ofLists [OfNat α 0] {m n : Nat} (rows : List (List α)) : Mat α m n :=
  fun i => Vec.ofList (rows.getD i.val [])

section Laws

open Lean.Grind

variable [CommRing α]

/-- Swapping the two sums of a double sum: `Σ_k (Σ_j x_j M_jk) y_k = Σ_j x_j (Σ_k M_jk y_k)`. -/
theorem Vec.dot_dot_comm {n p : Nat} (x : Vec α n) (M : Fin n → Vec α p) (y : Vec α p) :
    Vec.dot (fun k => Vec.dot x (fun j => M j k)) y = Vec.dot x (fun j => Vec.dot (M j) y) := by
  induction n with
  | zero => simp only [Vec.dot]; exact Vec.dot_zero_left y
  | succ n ih =>
    have h := ih (fun i => x i.succ) (fun j => M j.succ)
    have e : (fun k => Vec.dot x (fun j => M j k)) =
        fun k => x 0 * M 0 k + Vec.dot (fun i => x i.succ) (fun j => M j.succ k) := by
      funext k; simp only [Vec.dot]
    rw [e, Vec.dot_add_left, Vec.dot_smul_left (x 0) (M 0) y, h]
    simp only [Vec.dot]

/-- Matrix product: entry `(i, k)` is the dot product of row `i` of `A` with column `k` of `B`. -/
def Mat.mul {m n p : Nat} (A : Mat α m n) (B : Mat α n p) : Mat α m p :=
  fun i k => Vec.dot (A i) (fun j => B j k)

/-- The transpose swaps the two indices. -/
def Mat.transpose {m n : Nat} (A : Mat α m n) : Mat α n m := fun j i => A i j

/-- Transposing twice gives back the matrix. -/
theorem Mat.transpose_transpose {m n : Nat} (A : Mat α m n) : A.transpose.transpose = A := rfl

/-- **Associativity of the matrix product.** -/
theorem Mat.mul_assoc {m n p q : Nat} (A : Mat α m n) (B : Mat α n p) (C : Mat α p q) :
    (A.mul B).mul C = A.mul (B.mul C) := by
  funext i l
  simp only [Mat.mul]
  exact Vec.dot_dot_comm (A i) B (fun k => C k l)

/-- Multiplying by a product is multiplying twice. -/
theorem Mat.mulVec_mul {m n p : Nat} (A : Mat α m n) (B : Mat α n p) (x : Vec α p) :
    (A.mul B).mulVec x = A.mulVec (B.mulVec x) := by
  funext i
  simp only [Mat.mulVec, Mat.mul]
  exact Vec.dot_dot_comm (A i) B x

/-- The transpose of a product is the product of the transposes, in the other order. -/
theorem Mat.transpose_mul {m n p : Nat} (A : Mat α m n) (B : Mat α n p) :
    (A.mul B).transpose = B.transpose.mul A.transpose := by
  funext k i
  simp only [Mat.transpose, Mat.mul]
  exact Vec.dot_comm _ _

end Laws

end LeanDL