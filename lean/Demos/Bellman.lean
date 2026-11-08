import LeanDL.Ch13.Bellman

/-!
# Value iteration on an exact 4-state chain — running `LeanDL/Ch13/Bellman.lean`

A four-state walking policy: from state `s` the agent advances to `s+1` with probability
`3/4` and diffuses to each other state with probability `1/12` (all probabilities stay
strictly positive, so every distribution is a legitimate `Dist`). Reward `1` at state 3,
discount `γ = 1/2`. **Everything below is exact `Rat` arithmetic** — the same numbers the
theorems talk about, not `Float`.

The run prints, for each sweep `k`: the sup-norm gap `dₖ = max |vₖ − vₖ₋₁|`, the bound
`γ · dₖ₋₁` promised by `cheb_le`, and whether the inequality actually holds on these
numbers. The theorem says it holds for every `k`; the run shows it on one MDP and prints
the Bellman residual of the final value. This is a demonstration of the proved contraction,
not a substitute for its proof.
-/

open LeanDL LeanDL.Ch13

/-- Exact rational printing. -/
def rt (q : Rat) : String :=
  if q.den = 1 then toString q.num else toString q.num ++ "/" ++ toString q.den

-- The four transition rows (probabilities 3/4 forward, 1/12 everywhere else).
def w0 : Vec Rat 4 := fun i => if i = ⟨1, by decide⟩ then 3 / 4 else 1 / 12
def w1 : Vec Rat 4 := fun i => if i = ⟨2, by decide⟩ then 3 / 4 else 1 / 12
def w2 : Vec Rat 4 := fun i => if i = ⟨3, by decide⟩ then 3 / 4 else 1 / 12
def w3 : Vec Rat 4 := fun i => if i = ⟨0, by decide⟩ then 3 / 4 else 1 / 12

theorem pos_w0 : ∀ i : Fin 4, 0 < w0 i := by
  intro i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      unfold w0
      grind
theorem pos_w1 : ∀ i : Fin 4, 0 < w1 i := by
  intro i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      unfold w1
      grind
theorem pos_w2 : ∀ i : Fin 4, 0 < w2 i := by
  intro i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      unfold w2
      grind
theorem pos_w3 : ∀ i : Fin 4, 0 < w3 i := by
  intro i
  cases i with
  | mk k hk =>
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkk with rfl | rfl | rfl | rfl
    all_goals
      unfold w3
      grind

theorem sum_w0 : Vec.dot w0 (fun _ => 1) = 1 := by
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold w0
  simp [Fin.val_succ, Fin.val_zero]
  grind
theorem sum_w1 : Vec.dot w1 (fun _ => 1) = 1 := by
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold w1
  simp [Fin.val_succ, Fin.val_zero]
  grind
theorem sum_w2 : Vec.dot w2 (fun _ => 1) = 1 := by
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold w2
  simp [Fin.val_succ, Fin.val_zero]
  grind
theorem sum_w3 : Vec.dot w3 (fun _ => 1) = 1 := by
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold Vec.dot
  unfold w3
  simp [Fin.val_succ, Fin.val_zero]
  grind

def P0 : Dist 4 := ⟨w0, pos_w0, sum_w0⟩
def P1 : Dist 4 := ⟨w1, pos_w1, sum_w1⟩
def P2 : Dist 4 := ⟨w2, pos_w2, sum_w2⟩
def P3 : Dist 4 := ⟨w3, pos_w3, sum_w3⟩

/-- The MDP: rewards `1` at state 3, the rows above as transitions, discount `1/2`. -/
def mdp : PolicyMdp 4 where
  r := fun s => if s = ⟨3, by decide⟩ then 1 else 0
  P := fun s => match s.val with
    | 0 => P0
    | 1 => P1
    | 2 => P2
    | _ => P3
  γ := 1 / 2
  hg0 := by grind [Rat.div_def]
  hg1 := by grind [Rat.div_def]

/-- Reading `q.num` forces the structure to weak-head-normal form, which collapses
the lazy closure chain accumulated by the previous sweeps. -/
def forceQ (q : Rat) : Rat :=
  let _ := q.num
  q

def forceVec (v : Vec Rat 4) : Vec Rat 4 :=
  let a := forceQ (v 0); let b := forceQ (v 1)
  let c := forceQ (v 2); let d := forceQ (v 3)
  fun i => if (i : Fin 4).val = 0 then a else if (i : Fin 4).val = 1 then b
           else if (i : Fin 4).val = 2 then c else d

def showVec (k : Nat) (v : Vec Rat 4) : IO Unit := do
  let a := v 0; let b := v 1; let c := v 2; let d := v 3
  IO.println s!"  v_{k} = [{rt a}, {rt b}, {rt c}, {rt d}]"

def main : IO Unit := do
  IO.println "4-state chain, exact Rat arithmetic (LeanDL/Ch13/Bellman.lean)"
  IO.println "policy: advance with prob 3/4, diffuse 1/12 to the others; gamma = 1/2"
  IO.println "starting value v_0 = [0, 0, 0, 0]"
  let mut vk : Vec Rat 4 := fun _ => 0
  let mut prevGap : Option Rat := none
  for k in [1:9] do
    let vprev := vk
    let vk' := forceVec fun s => T mdp vprev s
    let g := maxV fun s => (vk' s - vprev s).abs
    match prevGap with
    | none =>
        IO.println s!"  sweep {k}: gap d_{k} = {rt g} (initial)"
    | some d =>
        let bound := (1 / 2 : Rat) * d
        let ok := if g ≤ bound then "OK" else "VIOLATED"
        IO.println s!"  sweep {k}: gap d_{k} = {rt g}   bound (1/2)*d_(k-1) = {rt bound}   {ok}"
    vk := vk'
    prevGap := some g
  showVec 8 vk
  let res := maxV fun s => (T mdp vk s - vk s).abs
  IO.println s!"  Bellman residual max |T v_8 - v_8| = {rt res}"
  IO.println "  (exact arithmetic stops at 8 sweeps: numerators and denominators"
  IO.println "   grow like 24^k, and the point — the gap obeying the proved factor —"
  IO.println "   is already made on every printed line)"
  IO.println "the inequalities printed OK are the theorem cheb_le on these numbers;"
  IO.println "vIter_rate upgrades them to the geometric bound gamma^k * d_0."