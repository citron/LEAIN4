import LeanDL.Core.Mat
import LeanDL.Core.Sum

/-!
## Tensors with the shape in the type

Every layer in this course runs on `Vec`/`Mat` — families indexed by a *known*
size. Real deployments flatten everything: images are `28*28*3` floats, batches
are `B*T*d` floats, and the layout (row-major, strides) is a comment in the
code. This module gives the missing middle layer: a `Tensor α m n` whose shape
lives in the **type**, stored **flattened** exactly like a real tensor, with a
proved dictionary to the formal `Mat` layer:

- `row` / `col` / `unflat`: the div/mod index arithmetic of row-major strides;
- `toMat` / `fromMat`: inverse bridges (`fromMat_toMat`, `toMat_fromMat`);
- `flatMulVec`: the flat emulation of a fully-connected layer, proved equal to
  the formal `Mat.mulVec` (`flatMulVec_eq`).

So "the flat loop we run" and "the matrix product we proved" are the same
computation — entry for entry, in the type-checked layout.
-/

open LeanDL Lean.Grind

namespace Tensors

-- ANCHOR: tensor
/-- A 2-D tensor with its shape in the type: rows `m`, columns `n`, stored
flattened in row-major order — the layout of every real tensor library. -/
abbrev Tensor (α : Type) (m n : Nat) := Fin (m * n) → α

/-- The row of a flat index (row-major: `i / n`). -/
def row (m n : Nat) (i : Fin (m * n)) : Fin m :=
  ⟨i.val / n, Nat.div_lt_of_lt_mul (show i.val < n * m from by
    rw [Nat.mul_comm n m]
    exact i.isLt)⟩

/-- The column of a flat index (row-major: `i % n`). -/
def col (m n : Nat) (i : Fin (m * n)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ (by
    cases n with
    | zero => exact absurd i.isLt (Nat.not_lt_zero _)
    | succ n => omega)⟩

/-- Flatten a (row, column) pair into an index: `i * n + j`. -/
def unflat (m n : Nat) (i : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨i.val * n + j.val, by
    have h1 : (i.val + 1) * n ≤ m * n := Nat.mul_le_mul_right n i.isLt
    have h2 : i.val * n + j.val < (i.val + 1) * n := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega⟩
-- ANCHOR_END: tensor

/-- Reading back the row of a flattened pair returns the row. -/
theorem row_unflat (m n : Nat) (i : Fin m) (j : Fin n) : row m n (unflat m n i j) = i := by
  refine Fin.ext ?_
  show (i.val * n + j.val) / n = i.val
  have hn : 0 < n := by
    cases n with
    | zero => exact absurd j.isLt (Nat.not_lt_zero _)
    | succ n => omega
  calc (i.val * n + j.val) / n
      = (j.val + n * i.val) / n := by rw [Nat.add_comm, Nat.mul_comm i.val n]
    _ = j.val / n + i.val := Nat.add_mul_div_left _ _ hn
    _ = 0 + i.val := by rw [Nat.div_eq_of_lt j.isLt]
    _ = i.val := Nat.zero_add _

/-- Reading back the column of a flattened pair returns the column. -/
theorem col_unflat (m n : Nat) (i : Fin m) (j : Fin n) : col m n (unflat m n i j) = j := by
  refine Fin.ext ?_
  show (i.val * n + j.val) % n = j.val
  rw [show i.val * n + j.val = j.val + i.val * n from by rw [Nat.add_comm]]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt j.isLt

/-- Matricize a flat tensor: the `m × n` matrix of its entries. -/
def toMat {α : Type} {m n : Nat} (t : Tensor α m n) : Mat α m n :=
  fun i j => t (unflat m n i j)

/-- Reshape a matrix into a flat tensor: `A (i / n) (i % n)`. -/
def fromMat {α : Type} {m n : Nat} (A : Mat α m n) : Tensor α m n :=
  fun i => A (row m n i) (col m n i)

/-- **Flatten-then-matricize is the identity**: the strides round-trip
(`unflat (row i) (col i) = i` via `div_add_mod`). -/
theorem fromMat_toMat {α : Type} {m n : Nat} (t : Tensor α m n) :
    fromMat (toMat t) = t := by
  funext i
  show t (unflat m n (row m n i) (col m n i)) = t i
  congr 1
  refine Fin.ext ?_
  calc (unflat m n (row m n i) (col m n i)).val
      = (i.val / n) * n + i.val % n := rfl
    _ = i.val := by
        rw [Nat.mul_comm (i.val / n) n]
        exact Nat.div_add_mod i.val n

/-- **Matricize-then-flatten is the identity** (via `row_unflat` + `col_unflat`). -/
theorem toMat_fromMat {α : Type} {m n : Nat} (A : Mat α m n) :
    toMat (fromMat A) = A := by
  funext i j
  show A (row m n (unflat m n i j)) (col m n (unflat m n i j)) = A i j
  rw [row_unflat, col_unflat]

/-- Entrywise map: tensors are closed under pointwise functions (activations). -/
def tmap {α β : Type} {m n : Nat} (f : α → β) (t : Tensor α m n) : Tensor β m n :=
  fun i => f (t i)

/-- Pointwise sum (residuals). -/
def tadd {α : Type} [Add α] {m n : Nat} (s t : Tensor α m n) : Tensor α m n :=
  fun i => s i + t i

-- ANCHOR: matvec
/-- **The matvec bridge**: the flat, row-major emulation of a fully-connected
layer — the exact loop an untyped production network runs. -/
def flatMulVec {α : Type} [Mul α] [AddCommMonoid α] {m n : Nat}
    (A : Tensor α m n) (v : Fin n → α) : Fin m → α :=
  fun i => Vec.dot (fun j => A (unflat m n i j)) v

/-- **The flat emulation IS the formal matrix-vector product**, entry for entry:
`toMat` turns the flat loop into `Mat.mulVec` without changing one product. -/
theorem flatMulVec_eq {α : Type} [Mul α] [AddCommMonoid α] {m n : Nat}
    (A : Tensor α m n) (v : Fin n → α) (i : Fin m) :
    flatMulVec A v i = Mat.mulVec (toMat A) v i := by
  show Vec.dot (fun j => A (unflat m n i j)) v = Vec.dot (fun j => toMat A i j) v
  refine congrArg (Vec.dot · v) (funext fun j => ?_)
  show A (unflat m n i j) = toMat A i j
  rfl
-- ANCHOR_END: matvec

end Tensors
