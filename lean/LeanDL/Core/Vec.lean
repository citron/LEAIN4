import LeanDL.Core.Algebra

/-!
# Vectors with their length in the type

`Vec α n` is just a function `Fin n → α`: proofs are easy, and the length `n` is checked
by the type checker, so a dot product of vectors of different sizes does not even type-check.
-/

namespace LeanDL

open Lean.Grind

-- ANCHOR: vec
abbrev Vec (α : Type) (n : Nat) := Fin n → α
-- ANCHOR_END: vec

namespace Vec

variable {α : Type}

-- ANCHOR: dot
/-- Dot product, by recursion on the length. -/
def dot [Add α] [Mul α] [OfNat α 0] : {n : Nat} → Vec α n → Vec α n → α
  | 0, _, _ => 0
  | _ + 1, x, y => x 0 * y 0 + dot (fun i => x i.succ) (fun i => y i.succ)
-- ANCHOR_END: dot

def add [Add α] {n : Nat} (x y : Vec α n) : Vec α n := fun i => x i + y i

def smul [Mul α] {n : Nat} (c : α) (x : Vec α n) : Vec α n := fun i => c * x i

def zero [OfNat α 0] {n : Nat} : Vec α n := fun _ => 0

/-- Prepend a constant coordinate; this is how a bias is folded into the weights. -/
def cons1 [OfNat α 1] {n : Nat} (x : Vec α n) : Vec α (n + 1) :=
  fun i => if h : i.val = 0 then 1 else x ⟨i.val - 1, by omega⟩

section Laws

variable [CommRing α]

theorem dot_zero_left {n : Nat} (y : Vec α n) : dot (fun _ => (0 : α)) y = 0 := by
  induction n with
  | zero => simp only [dot]
  | succ n ih =>
    have := ih (fun i => y i.succ)
    simp only [dot] at this ⊢
    grind

theorem dot_comm {n : Nat} (x y : Vec α n) : dot x y = dot y x := by
  induction n with
  | zero => simp only [dot]
  | succ n ih => simp only [dot]; rw [ih]; grind

theorem dot_add_left {n : Nat} (x y z : Vec α n) :
    dot (fun i => x i + y i) z = dot x z + dot y z := by
  induction n with
  | zero => simp only [dot]; grind
  | succ n ih =>
    have := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ)
    simp only [dot] at this ⊢
    grind

theorem dot_smul_left {n : Nat} (c : α) (x y : Vec α n) :
    dot (fun i => c * x i) y = c * dot x y := by
  induction n with
  | zero => simp only [dot]; grind
  | succ n ih =>
    have := ih (fun i => x i.succ) (fun i => y i.succ)
    simp only [dot] at this ⊢
    grind

theorem dot_add_right {n : Nat} (x y z : Vec α n) :
    dot x (fun i => y i + z i) = dot x y + dot x z := by
  rw [dot_comm, dot_add_left, dot_comm y, dot_comm z]

theorem dot_smul_right {n : Nat} (c : α) (x y : Vec α n) :
    dot x (fun i => c * y i) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

end Laws

end Vec

end LeanDL
