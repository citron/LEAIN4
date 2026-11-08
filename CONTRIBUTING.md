# Contributing to LEAIN4

LEAIN4 is a Deep Learning course implemented, executed and formalized in Lean 4
**without Mathlib**. The value of the project is its honesty contract: every
claim is labelled by its status. Contributions must keep that contract intact.

## Non-negotiable invariants

1. **No Mathlib.** `lean/lakefile.toml` has zero `require` and `lean/lake-manifest.json` has `"packages": []`. Do not add dependencies.
2. **`Rat` proves, `Float` runs.** Theorems are stated over `Rat` (or an abstract ring via `Lean.Grind`); `Float` appears only in implementations and demos. Never state a theorem about `Float`.
3. **Zero `sorry` outside `Exercises.lean`**; no `axiom`, `admit`, `partial`, `native_decide` in `lean/LeanDL` (rule 4 of `scripts/check.mjs`). Analytic boundaries are declared as **named classes/hypotheses** (`LawfulLog`, `LawfulExp`, `MonotoneExp`), never as axioms.
4. **Status vocabulary**: *Démontré formellement* · *Démontré sous hypothèses nommées* · *Vérifié numériquement* · *Observé expérimentalement* · *Simplifié / non modélisé*. The word "proved/prouvé" is reserved for the first two. A single seed is **not** an evaluation.
5. **Strict EN/FR parity** for every page addition (titles, code blocks, `$$`, Lean anchors — rule 1 of `check.mjs`).
6. **Lean excerpts on pages come from compiled files** via `` ```lean file=Chap/Fichier.lean#nom `` with `-- ANCHOR: nom` / `-- ANCHOR_END: nom` markers. Never hand-paste Lean into an `.mdx`.
7. Every module under `lean/LeanDL` (except `Exercises`) is imported by `lean/LeanDL.lean` (rule 5).
8. A demo never imports an `Exercises` module (a `def` equal to `sorry` panics the executable at initialization).

## Verification loop — run before and after every change

```bash
# Lean (from lean/)
lake build            # every target in scripts/targets.txt
lake env lean ../scripts/audit_axioms.lean   # expect: using sorry: []; non-standard axioms: []
lake exe props

# Site / coherence (from the repository root)
node scripts/check.mjs
cd website && npm ci && npm run build
```

A red state at the start is to be reported, not worked around. Do not delete a
`check.mjs` rule to make a PR pass; if a rule is wrong, fix it **with** a
negative test.

## Lists that have one source of truth

- Build targets: `scripts/targets.txt` (CI reads it — do not hardcode lists in `ci.yml`).
- Demo smoke list: `scripts/smoke.txt`; demos excluded from the fast smoke loop go in `scripts/smoke-skip.txt` **with a reason** (rule 9 of `check.mjs` enforces coverage).

## Lean proof toolkit (no Mathlib)

`grind`, `omega`, `norm_cast`, `push_cast`, `decide` (cautiously — it does not
reduce `Rat.mul`), `simp [Fin.val_succ, Fin.val_zero]`, `show` (grind does not
unfold structure projections). No `ring`/`linarith`/`norm_num`/`field_simp`.
Keep denominators small under `show` (defeq timeouts). Never build a `Decidable`
on `Float` propositions — use `Float.beq`/`Float.abs`.

## PR checklist

- [ ] `lake build` green; audit line `using sorry: []; non-standard axioms: []`; `lake exe props` green
- [ ] `node scripts/check.mjs` green; `npm run build` (EN+FR) green
- [ ] New modules imported in `LeanDL.lean`; anchors placed; EN **and** FR pages at parity
- [ ] ≥ 2 exercises + proved solutions for any new concept
- [ ] Honesty boundaries updated in the chapter box **and** `ROADMAP.md §3`
- [ ] `ROADMAP.md §1` replayed; journal entry in `PROJECT_AUDIT.md`; PR description carries the command outputs
- [ ] No parasite files (`_tmp_*`, logs, local paths)

## Style

- One commit per coherent item; hygiene and proofs do not mix in one PR.
- Commit subject: short imperative (`Core/Rounding: flDot_error (Higham)`), body = **measured** results (jobs, audited declarations, pages).
- Publish no number you did not replay: every figure ships with its seed and its command.
