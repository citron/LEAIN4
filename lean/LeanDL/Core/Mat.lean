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

end LeanDL
