import LeanDL.Ch09.Transformer

/-!
# Chapter 9, part 3 — the N-block stack, and why causality survives the stack

One transformer block is proved not to leak the future (`blockOut_no_leak`). A GPT is **N
blocks stacked**, and a single-block guarantee is not yet a model guarantee: the whole point
of this file is the induction that lifts it.

* `BParams` packages one block's parameters; `stack` runs a **list** of blocks (the model's
  N layers) in order over a whole sequence matrix (`Mat α T d`: static dimensions — `T`
  positions, `d` features — checked by the type).
* `stack_no_leak`: if two input sequences agree on all rows `j ≤ t`, the stacked outputs
  agree on every row `j ≤ t` — for **any number of blocks**. The induction step is
  `runBlock_no_leak` (the packaged `blockOut_no_leak`) fed by the induction hypothesis.

Honesty note: this is a **structural** guarantee about information flow (rows `> t` never
influence rows `≤ t`), proved over an exact field with ideal layer norm, attention and
residuals. It says nothing about empirical trainability, quantisation, or the Float
executable — the multi-layer GPT executable validates its gradients **numerically**
(central-difference check in the `gpt` demo) and its training curve is an **empirical**
result. Structural proof, gradient check, empirical run: three kinds of evidence, kept
apart.
-/

namespace LeanDL.Ch09

open LeanDL Lean.Grind LeanDL.Ch04

/-- The full parameter set of one transformer block, packaged for stacking. -/
structure BParams (α : Type) (d h dh hd : Nat) where
  eps : α
  σ : α → α
  Wq : Fin h → Mat α dh d
  Wk : Fin h → Mat α dh d
  Wv : Fin h → Mat α dh d
  Wo : Mat α d (dh * h)
  bo : Vec α d
  W1 : Mat α hd d
  b1 : Vec α hd
  W2 : Mat α d hd
  b2 : Vec α d

section Stack
variable {α : Type} [Field α] [HasAct α] [HasExp α]
variable {d h dh hd T : Nat}

/-- Run one block over a whole sequence. -/
def runBlock (b : BParams α d h dh hd) (xs : Mat α T d) (t : Fin T) : Vec α d :=
  blockOut b.eps b.σ b.Wq b.Wk b.Wv b.Wo b.bo b.W1 b.b1 b.W2 b.b2 xs t

/-- A single block, in `runBlock` form, does not leak: `blockOut_no_leak` restated for the
packaged parameter record. -/
theorem runBlock_no_leak {b : BParams α d h dh hd} {xs xs' : Mat α T d} (t : Fin T)
    (heq : ∀ j : Fin T, j.val ≤ t.val → xs j = xs' j) :
    runBlock b xs t = runBlock b xs' t :=
  blockOut_no_leak b.eps b.σ b.Wq b.Wk b.Wv b.Wo b.bo b.W1 b.b1 b.W2 b.b2 xs xs' t heq

-- ANCHOR: stack
/-- **The stack.** `bs` is the model's transformer blocks, run in order: `bs 0` sees the
embeddings, the last block sees everything below it. (The block count is the list length;
the feature dimensions are static — checked by the type.) -/
def stack : List (BParams α d h dh hd) → Mat α T d → Mat α T d
  | [] => fun xs => xs
  | b :: rest => fun xs => runBlock b (stack rest xs)
-- ANCHOR_END: stack

-- ANCHOR: stack_no_leak
/-- **No leakage from the future, for a stack of any depth.** If the inputs agree on every
row up to `t`, the stacked outputs agree on every row up to `t` — for **any list of
blocks**. Induction on the list: the step is `runBlock_no_leak` at position `j`, whose
hypothesis ("the two sub-stacks agree on every row `i ≤ j`") is the induction hypothesis
itself, restricted along `i ≤ j ≤ t`. **Causality composes: the stack of causal blocks is
causal.** -/
theorem stack_no_leak : ∀ (bs : List (BParams α d h dh hd)) (xs xs' : Mat α T d) (t : Fin T),
    (∀ j : Fin T, j.val ≤ t.val → xs j = xs' j) →
    ∀ j : Fin T, j.val ≤ t.val → stack bs xs j = stack bs xs' j := by
  intro bs
  induction bs with
  | nil => intro xs xs' t h j hj; simp [stack]; exact h j hj
  | cons b rest ih =>
      intro xs xs' t h j hj
      show runBlock b (stack rest xs) j = runBlock b (stack rest xs') j
      refine runBlock_no_leak j (fun i hi => ?_)
      exact ih xs xs' j (fun i' hi' => h i' (Nat.le_trans hi' hj)) i hi
-- ANCHOR_END: stack_no_leak

/-- **The full model.** The output row at position `t` of an `N`-block GPT depends on the
input rows `j ≤ t` only. This is the property an autoregressive model needs to train on
whole sequences in parallel without cheating. -/
theorem stack_full_no_leak (bs : List (BParams α d h dh hd))
    (xs xs' : Mat α T d) (t : Fin T)
    (h : ∀ j : Fin T, j.val ≤ t.val → xs j = xs' j) :
    stack bs xs t = stack bs xs' t :=
  stack_no_leak bs xs xs' t h t (Nat.le_refl _)

end Stack

end LeanDL.Ch09
