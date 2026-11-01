import LeanDL.Ch11.Gan
import LeanDL.Ch04.Network
import LeanDL.Core.Rng
import LeanDL.Core.Plot

/-!
# Chapter 11, part 2 — A GAN in one dimension, trained with the verified autodiff

Generator `z ↦ x`: `1 → 8 → 1`; discriminator `x ↦ D(x) ∈ (0, 1)`: `1 → 8 → 1`. Both are `Expr`s,
so every gradient comes from `backprop`, whose correctness is `Ch04.backprop_correct`.
-/

namespace LeanDL.Ch11

open LeanDL.Ch04

abbrev H : Nat := 8
abbrev P : Nat := 6 * H + 2

-- ANCHOR: gan_model
/-- Generator parameters are `0 … 3H`, discriminator parameters `3H+1 … 6H+1`. -/
def gen (z : Expr Float P) : Expr Float P :=
  let hid := denseE .tanh 0 1 H [z]
  (denseE (fun e => e) (2 * H) H 1 hid).headD (.const 0)

def disc (x : Expr Float P) : Expr Float P :=
  let hid := denseE .tanh (3 * H + 1) 1 H [x]
  .sigmoid ((denseE (fun e => e) (5 * H + 1) H 1 hid).headD (.const 0))

/-- Discriminator loss: `-log D(x) - log (1 - D(G z))`, over a batch. -/
def discLoss (reals noises : List Float) : Expr Float P :=
  let terms := (reals.zip noises).map fun (x, z) =>
    Expr.add (.sub (.const 0) (.log (disc (.const x))))
      (.sub (.const 0) (.log (.sub (.const 1) (disc (gen (.const z))))))
  .mul (.const (1.0 / reals.length.toFloat)) (Expr.sum terms)

/-- Generator loss (the "non-saturating" form): `-log D(G z)`. -/
def genLoss (noises : List Float) : Expr Float P :=
  let terms := noises.map fun z => Expr.sub (.const 0) (.log (disc (gen (.const z))))
  .mul (.const (1.0 / noises.length.toFloat)) (Expr.sum terms)
-- ANCHOR_END: gan_model

def vecOf (p : Array Float) : Vec Float P := fun i => p[i.val]!

/-- Apply the generator to a noise value. -/
def generate (p : Array Float) (z : Float) : Float := (gen (.const z) : Expr Float P).eval (vecOf p)

/-- Real data: a Gaussian (`mixture = false`) or two well-separated Gaussians. -/
def realSample (mixture : Bool) (r : Rng) : Float × Rng :=
  let (g, r) := r.normal
  if mixture then
    let (u, r) := r.uniform
    ((if u < 0.5 then -2.0 else 2.0) + 0.4 * g, r)
  else
    (2.0 + 0.5 * g, r)

end LeanDL.Ch11
