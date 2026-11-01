import Lean
import LeanDL

/-! Audit: every declaration of the course (exercise stubs excluded) must be free of `sorry`
and of any axiom beyond Lean's three standard ones.
Run from `lean/`:  `lake env lean ../scripts/audit_axioms.lean` -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total : Nat := 0
  let mut bad : Array Name := #[]
  let mut weird : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `LeanDL do continue
    if mod.toString.endsWith "Exercises" then continue
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      total := total + 1
      let axs ← collectAxioms n
      if axs.contains `sorryAx then bad := bad.push n
      let extra := axs.filter fun a => ![`propext, `Classical.choice, `Quot.sound].contains a
      if !extra.isEmpty then weird := weird.push (n, extra)
    | _ => pure ()
  logInfo m!"checked {total} declarations; using sorry: {bad}; non-standard axioms: {weird}"
