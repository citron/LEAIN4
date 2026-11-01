import LeanDL.Ch02.Perceptron

/-!
# Chapter 2, part 3 — Running the perceptron (on `Float`)
-/

namespace LeanDL.Ch02

variable {α : Type}

/-- A training example: bias-augmented input and a label in `{+1, -1}`. -/
abbrev Example (α : Type) (n : Nat) := Vec α n × α

-- ANCHOR: train
/-- One pass over the data; returns the new weights and the number of mistakes. -/
def epoch [Add α] [Mul α] [OfNat α 0] [LE α] [DecidableRel (α := α) (· ≤ ·)]
    {n : Nat} (w : Vec α n) (data : List (Example α n)) : Vec α n × Nat :=
  data.foldl
    (fun (acc : Vec α n × Nat) (e : Example α n) =>
      let (w, m) := acc
      if e.2 * Vec.dot w e.1 ≤ 0 then (update w e.1 e.2, m + 1) else (w, m))
    (w, 0)

/-- Run up to `fuel` epochs, stopping at the first mistake-free epoch.
Returns the final weights and the mistake count of every epoch. -/
def train [Add α] [Mul α] [OfNat α 0] [LE α] [DecidableRel (α := α) (· ≤ ·)]
    {n : Nat} (data : List (Example α n)) : Nat → Vec α n → List Nat → Vec α n × List Nat
  | 0, w, log => (w, log.reverse)
  | fuel + 1, w, log =>
    let (w', m) := epoch w data
    if m = 0 then (w', (m :: log).reverse) else train data fuel w' (m :: log)
-- ANCHOR_END: train

/-- Length-3 vector (bias, x₁, x₂). -/
def v3 (a b c : α) : Vec α 3 := fun i => if i.val = 0 then a else if i.val = 1 then b else c

end LeanDL.Ch02
