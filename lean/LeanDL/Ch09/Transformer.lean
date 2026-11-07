import LeanDL.Ch09.Attention
import LeanDL.Core.Mat

/-!
# Chapter 9 — the Transformer block, assembled and proved

A transformer block stacks four ideas — **layer norm**, **causal multi-head attention**,
**a feed-forward network**, **residual connections** — wired as

```
y = layerNorm (x + Attention(layerNorm x))     -- attention sub-layer
z = layerNorm (y + FFN(y))                     -- feed-forward sub-layer
```

This file assembles that block over a *sequence* of rows (`Mat α T d`: `T` positions,
`d` features each — shapes checked by the type) and proves the two properties the
architecture exists to guarantee, for the whole block and not just its parts:

* **No leakage from the future.** The block's output at position `t` depends only on the
  input rows at positions `j ≤ t` — the reason an autoregressive model trains on whole
  sequences in parallel without cheating. It is the block-level lift of `causal_no_leak`.
* **Shift invariance.** Adding one constant to every feature of every row leaves every
  output unchanged — the block normalises away absolute offsets. It lifts `layerNorm_shift`
  through the residuals and the feed-forward network.

The GPT executable of this chapter (`Gpt.lean`) computes exactly this structure in `Float`
(ReLU feed-forward, one head); the theorems here are over an exact field `α`.
-/

namespace LeanDL.Ch09

open LeanDL Lean.Grind LeanDL.Ch04

section Block

variable {α : Type} [Field α] [HasAct α] [HasExp α]
variable {d h hd T : Nat}

/-- Layer norm applied row by row to a sequence. -/
def seqNorm (eps : α) (xs : Mat α T d) : Mat α T d :=
  fun j => layerNorm eps (xs j)

-- ANCHOR: transformer_block
/-- One head at position `t`: queries, keys and values are linear maps (shapes in the type);
the score of query `t` against key `j` is their dot product; the causal mask hides `j > t`
(`causal`, `attendM`). -/
def headOut (eps : α) (Wq Wk Wv : Fin h → Mat α dh d) (xs : Mat α T d) (t : Fin T)
    (k : Fin h) : Vec α dh :=
  fun e => attendM (causal t.val)
    (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs t))
      (Mat.mulVec (Wk k) (seqNorm eps xs j)))
    (fun j => Mat.mulVec (Wv k) (seqNorm eps xs j) e)

/-- The `h` head outputs are concatenated (layout proved in `Attention.lean`: `concat_head`,
`head_concat`) and projected back to width `d`. -/
def attnOut (eps : α) (Wq Wk Wv : Fin h → Mat α dh d) (Wo : Mat α d (dh * h))
    (bo : Vec α d) (xs : Mat α T d) (t : Fin T) : Vec α d :=
  Vec.add (Mat.mulVec Wo (concatVec h dh (headOut eps Wq Wk Wv xs t))) bo

/-- The feed-forward network: a width-`hd` hidden layer with activation `σ`
(`Gpt.lean` uses ReLU), back to width `d`. -/
def ffn (σ : α → α) (W1 : Mat α hd d) (b1 : Vec α hd) (W2 : Mat α d hd) (b2 : Vec α d)
    (y : Vec α d) : Vec α d :=
  fun i => Mat.mulVec W2 (fun k => σ (Mat.mulVec W1 y k + b1 k)) i + b2 i

/-- **The transformer block** at position `t` of a sequence of `T` rows of width `d`:
two pre-norm sub-layers with residuals, exactly as every implementation wires them. -/
def blockOut (eps : α) (σ : α → α)
    (Wq Wk Wv : Fin h → Mat α dh d) (Wo : Mat α d (dh * h)) (bo : Vec α d)
    (W1 : Mat α hd d) (b1 : Vec α hd) (W2 : Mat α d hd) (b2 : Vec α d)
    (xs : Mat α T d) (t : Fin T) : Vec α d :=
  let y := layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t))
  layerNorm eps (Vec.add y (ffn σ W1 b1 W2 b2 y))
-- ANCHOR_END: transformer_block

-- ANCHOR: transformer_props
/-- **No leakage from the future, for the whole block.** If two input sequences agree on the
rows `j ≤ t`, the block outputs the same vector at position `t`, whatever the hidden rows
`j > t` contain. Every sub-layer is congruent, and the attention step is `causal_no_leak`. -/
theorem blockOut_no_leak (eps : α) (σ : α → α)
    (Wq Wk Wv : Fin h → Mat α dh d) (Wo : Mat α d (dh * h)) (bo : Vec α d)
    (W1 : Mat α hd d) (b1 : Vec α hd) (W2 : Mat α d hd) (b2 : Vec α d)
    (xs xs' : Mat α T d) (t : Fin T)
    (heq : ∀ j : Fin T, j.val ≤ t.val → xs j = xs' j) :
    blockOut eps σ Wq Wk Wv Wo bo W1 b1 W2 b2 xs t
      = blockOut eps σ Wq Wk Wv Wo bo W1 b1 W2 b2 xs' t := by
  have hln : ∀ j : Fin T, j.val ≤ t.val → seqNorm eps xs j = seqNorm eps xs' j :=
    fun j hj => congrArg (layerNorm eps) (heq j hj)
  have hh : ∀ k : Fin h, headOut eps Wq Wk Wv xs t k = headOut eps Wq Wk Wv xs' t k := by
    intro k
    show (fun e => attendM (causal t.val)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs t))
        (Mat.mulVec (Wk k) (seqNorm eps xs j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs j) e))
      = (fun e => attendM (causal t.val)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs' t))
        (Mat.mulVec (Wk k) (seqNorm eps xs' j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs' j) e))
    funext e
    refine causal_no_leak (α := α) t
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs t))
        (Mat.mulVec (Wk k) (seqNorm eps xs j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs j) e)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs' t))
        (Mat.mulVec (Wk k) (seqNorm eps xs' j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs' j) e) ?_
    intro j hj
    constructor
    · rw [hln t (Nat.le_refl _), hln j hj]
    · rw [hln j hj]
  have hat : attnOut eps Wq Wk Wv Wo bo xs t = attnOut eps Wq Wk Wv Wo bo xs' t :=
    congrArg (fun a => Vec.add (Mat.mulVec Wo a) bo) (congrArg (concatVec h dh) (funext hh))
  have hy : layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t))
      = layerNorm eps (Vec.add (xs' t) (attnOut eps Wq Wk Wv Wo bo xs' t)) := by
    rw [heq t (Nat.le_refl _), hat]
  show layerNorm eps (Vec.add (layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)))
      (ffn σ W1 b1 W2 b2
        (layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)))))
      = layerNorm eps (Vec.add (layerNorm eps (Vec.add (xs' t) (attnOut eps Wq Wk Wv Wo bo xs' t)))
      (ffn σ W1 b1 W2 b2
        (layerNorm eps (Vec.add (xs' t) (attnOut eps Wq Wk Wv Wo bo xs' t)))))
  rw [hy]

/-- **Shift invariance, for the whole block.** Adding the same constant to every feature of
every row leaves every output unchanged: layer norm kills offsets (`layerNorm_shift`), the
normalised inputs — hence the attention, the scores and the residuals — are untouched. -/
theorem blockOut_shift (eps c : α) (hn : (cnt d : α) ≠ 0) (σ : α → α)
    (Wq Wk Wv : Fin h → Mat α dh d) (Wo : Mat α d (dh * h)) (bo : Vec α d)
    (W1 : Mat α hd d) (b1 : Vec α hd) (W2 : Mat α d hd) (b2 : Vec α d)
    (xs : Mat α T d) (t : Fin T) :
    blockOut eps σ Wq Wk Wv Wo bo W1 b1 W2 b2 (fun j => Vec.add (xs j) (fun _ => c)) t
      = blockOut eps σ Wq Wk Wv Wo bo W1 b1 W2 b2 xs t := by
  have hln : ∀ j : Fin T, seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) j
      = seqNorm eps xs j := by
    intro j
    show layerNorm eps (fun i => xs j i + c) = layerNorm eps (xs j)
    exact layerNorm_shift eps c (xs j) hn
  have hh : ∀ k : Fin h,
      headOut eps Wq Wk Wv (fun j => Vec.add (xs j) (fun _ => c)) t k
        = headOut eps Wq Wk Wv xs t k := by
    intro k
    show (fun e => attendM (causal t.val)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) t))
        (Mat.mulVec (Wk k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) j) e))
      = (fun e => attendM (causal t.val)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs t))
        (Mat.mulVec (Wk k) (seqNorm eps xs j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs j) e))
    funext e
    refine causal_no_leak (α := α) t
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) t))
        (Mat.mulVec (Wk k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps (fun j => Vec.add (xs j) (fun _ => c)) j) e)
      (fun j => Vec.dot (Mat.mulVec (Wq k) (seqNorm eps xs t))
        (Mat.mulVec (Wk k) (seqNorm eps xs j)))
      (fun j => Mat.mulVec (Wv k) (seqNorm eps xs j) e) ?_
    intro j _
    constructor
    · rw [hln t, hln j]
    · rw [hln j]
  have hat : attnOut eps Wq Wk Wv Wo bo (fun j => Vec.add (xs j) (fun _ => c)) t
      = attnOut eps Wq Wk Wv Wo bo xs t :=
    congrArg (fun a => Vec.add (Mat.mulVec Wo a) bo) (congrArg (concatVec h dh) (funext hh))
  have hy : layerNorm eps (Vec.add (Vec.add (xs t) (fun _ => c))
        (attnOut eps Wq Wk Wv Wo bo (fun j => Vec.add (xs j) (fun _ => c)) t))
      = layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)) := by
    rw [hat]
    have heq : Vec.add (Vec.add (xs t) (fun _ => c)) (attnOut eps Wq Wk Wv Wo bo xs t)
        = (fun i => (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)) i + c) := by
      funext i
      simp only [Vec.add]
      grind
    rw [heq]
    exact layerNorm_shift eps c _ hn
  show layerNorm eps
      (Vec.add
        (layerNorm eps (Vec.add (Vec.add (xs t) (fun _ => c))
          (attnOut eps Wq Wk Wv Wo bo (fun j => Vec.add (xs j) (fun _ => c)) t)))
        (ffn σ W1 b1 W2 b2
          (layerNorm eps (Vec.add (Vec.add (xs t) (fun _ => c))
            (attnOut eps Wq Wk Wv Wo bo (fun j => Vec.add (xs j) (fun _ => c)) t)))))
      = layerNorm eps
        (Vec.add (layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)))
          (ffn σ W1 b1 W2 b2 (layerNorm eps (Vec.add (xs t) (attnOut eps Wq Wk Wv Wo bo xs t)))))
  rw [hy]
-- ANCHOR_END: transformer_props

end Block

end LeanDL.Ch09
