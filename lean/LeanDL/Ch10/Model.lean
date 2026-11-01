import LeanDL.Ch10.Vae
import LeanDL.Ch04.Network
import LeanDL.Core.Rng
import LeanDL.Core.Plot

/-!
# Chapter 10, part 2 — A VAE trained with the verified autodiff

Data: noisy points on a half circle (a closed circle cannot be covered continuously by a one-dimensional latent space). Latent space: one dimension. Encoder `2 → 8 → (μ, ℓ)`,
decoder `1 → 8 → 2`. The whole loss is an `Expr`, so its gradient is computed by `backprop`,
whose correctness is `Ch04.backprop_correct`.
-/

namespace LeanDL.Ch10

open LeanDL.Ch04

abbrev H : Nat := 8
abbrev P : Nat := 9 * H + 4

-- ANCHOR: model
/-- Encoder: `2 → H` tanh units → two linear read-outs, the mean `μ` and the log-variance `ℓ`. -/
def encoder (x : List (Expr Float P)) : Expr Float P × Expr Float P :=
  let hid := denseE .tanh 0 2 H x
  ((denseE (fun e => e) (3 * H) H 1 hid).headD (.const 0),
   (denseE (fun e => e) (3 * H + (H + 1)) H 1 hid).headD (.const 0))

/-- Decoder: `1 → H` tanh units → two linear outputs. -/
def decoder (z : Expr Float P) : List (Expr Float P) :=
  let hid := denseE .tanh (5 * H + 2) 1 H [z]
  denseE (fun e => e) (7 * H + 2) H 2 hid

/-- Reconstruction error (a Gaussian likelihood with variance `0.05`) plus `β` times the KL
penalty of the previous file, for one data point `(x₁, x₂)` and one noise draw `ε`. -/
def sampleLoss (beta x1 x2 eps : Float) : Expr Float P :=
  let (mu, lv) := encoder [.const x1, .const x2]
  let z := .add mu (.mul (.exp (.mul (.const 0.5) lv)) (.const eps))
  let recon := Expr.sum (((decoder z).zip [x1, x2]).map fun (o, t) =>
    .mul (.const 10.0) (sqErr o (.const t)))
  let kl := .mul (.const 0.5) (.sub (.add (.mul mu mu) (.exp lv)) (.add (.const 1) lv))
  .add recon (.mul (.const beta) kl)
-- ANCHOR_END: model

def vecOf (p : Array Float) : Vec Float P := fun i => p[i.val]!

/-- The posterior parameters `(μ, ℓ)` that the encoder assigns to a point. -/
def encode (p : Array Float) (x1 x2 : Float) : Float × Float :=
  let (mu, lv) := encoder [.const x1, .const x2]
  (mu.eval (vecOf p), lv.eval (vecOf p))

def decode (p : Array Float) (z : Float) : Float × Float :=
  match (decoder (.const z) : List (Expr Float P)).map (·.eval (vecOf p)) with
  | [a, b] => (a, b)
  | _ => (0, 0)

/-- `n` points on the upper half of the unit circle, with radial noise `0.05`. -/
def arcData (r : Rng) (n : Nat) : Array (Float × Float) × Rng := Id.run do
  let mut r := r
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let (u, r1) := r.uniform
    let (g, r2) := r1.normal
    r := r2
    let a := 3.141592653589793 * u
    let rad := 1.0 + 0.05 * g
    out := out.push (rad * Float.cos a, rad * Float.sin a)
  return (out, r)

end LeanDL.Ch10
