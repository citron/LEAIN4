import LeanDL.Core.Prob

/-!
# Chapter 16 — Mathematical tools: finite probability, entropy, KL

Everything the later chapters assume and never prove: expectations, variance,
entropy, KL divergence, and the **Gibbs inequality** (KL ≥ 0), which is why
cross-entropy training works at all.

The definitions and proofs now live in `Core/Prob.lean` — the shared
Layer-1 probability layer this chapter teaches. Every name below
(`LawfulLog`, `Dist`, `expect`, `variance`, `entropy`, `kl`,
`crossEntropy`, `ensemble_risk_decomp`, …) is that layer's, re-exported
here; the chapter's website pages include it from this file's anchors,
which moved to `Core/Prob.lean`.
-/

namespace LeanDL.Ch16

open Lean.Grind LeanDL

-- (definitions and proofs: `LeanDL/Core/Prob.lean`)

end LeanDL.Ch16
