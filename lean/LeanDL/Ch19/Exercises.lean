import LeanDL.Ch19.Multimodal

/-! Exercises for Chapter 19. Replace each `sorry`; the solutions are in `Solutions.lean`. -/

namespace LeanDL.Ch19

open Lean.Grind LeanDL.Ch16 LeanDL.Ch17

variable [LawfulLog] [HasExp Rat] [LawfulExp Rat] [MonotoneExp (α := Rat)]

-- ANCHOR: ex1
/-- Exercise 1: **one direction of the symmetric loss, alone.** For the 2x2 batch
`(x1, y1) (x2, y2)`, prove the image-to-text direction (positive `x1 * y1`,
negative `x1 * y2`) from `matched_loss` and `row_is_matched` directly:
`infoNce 1 (pairSample x1 y1 (fun _ => y2)) = log (1 + exp (x1*y2 - x1*y1))`.
(Hint: `infoNce_ext` turns the batch row into a matched pair, then apply
`matched_loss`.) -/
theorem exercise_row_loss (x1 y1 y2 : Rat) :
    infoNce 1 (by grind) (pairSample (n := 1) x1 y1 (fun _ : Fin 1 => y2))
      = LawfulLog.log (1 + HasExp.exp (x1 * y2 - x1 * y1)) := by
  sorry
-- ANCHOR_END: ex1

-- ANCHOR: ex2
/-- Exercise 2: **the collapsed model pays the SAME floor in the averaged loss.**
For `e != 0`, every score is `e * e`; conclude the closed form of
`symm_collapse` from `infoNce_collapse` and the two congruence lemmas.
(Hint: the scores of the collapsed sample and of `collapseSample (c := e*e)`
are equal as functions; feed that to `infoNce_ext`.) -/
theorem exercise_symm_collapse_floor (n : Nat) (e : Rat) (he : e ≠ 0) (τ : Rat) (hτ : 0 < τ) :
    symmInfoNce τ hτ
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      (pairSample (n := n) (x := e) (y := e) (negs := ((fun _ => e) : Vec Rat n)))
      = LawfulLog.log ((n + 1 : Nat) : Rat) := by
  sorry
-- ANCHOR_END: ex2

end LeanDL.Ch19
