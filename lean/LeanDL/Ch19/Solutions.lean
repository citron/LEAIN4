import LeanDL.Ch19.Exercises

/-! Proven solutions for the Chapter 19 exercises. -/

namespace LeanDL.Ch19

open Lean.Grind LeanDL.Ch16 LeanDL.Ch17

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat] [MonotoneExp (α := Rat)]

-- ANCHOR: sol1
theorem exercise_row_loss_solution (x1 y1 y2 : Rat) :
    infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      = LawfulLog.log (1 + HasExp.exp (x1 * y2 - x1 * y1)) := by
  rw [infoNce_ext _ _ (row_is_matched x1 y1 y2), matched_loss]
-- ANCHOR_END: sol1

-- ANCHOR: sol2
theorem exercise_symm_collapse_floor_solution (n : Nat) (e : Rat) (he : e ≠ 0)
    (τ : Rat) (hτ : 0 < τ) :
    symmInfoNce τ hτ
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      = LawfulLog.log ((n + 1 : Nat) : Rat) := by
  rw [symm_collapse e he τ hτ]
-- ANCHOR_END: sol2

end LeanDL.Ch19
