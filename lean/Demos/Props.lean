import LeanDL.Ch05.Optim
import LeanDL.Ch17.Contrastive
import LeanDL.Ch18.Efficiency
import LeanDL.Core.Rng
import LeanDL.Core.Algebra
import LeanDL.Core.Tensor
import LeanDL.Core.Rounding

/-!
# Property tests — the theorems, exercised on pseudorandom inputs

Every run uses a fixed seed, so the run is reproducible.

Checks against the **formal definitions** on the exact model `Rat` (comparisons on `Rat`
are decidable, so these checks are exact, not measured):

* Ch05: `sgdQuad η a w t = powN (1 − η·a) t · w` — the closed form proved by
  `sgdQuad_closed` — on 200 random exact `(η, a, w, t)`, plus the contraction
  `|w_t| ≤ |w_0|` when `η·a ≤ 1` (the content of `sgd_step_contract`).
* Ch18: the quantization bounds `|x − quant s x| < s` and `|x − roundq s x| ≤ s/2`
  (`quant_bound`, `roundq_err_le`) on 500 random exact pairs.
* Ch18: the MoE load-balance floor `Σ p² ≥ 1/E` (`balance_ge`) on 200 random routers.

The `Float` mirrors (softmax, layerNorm, causal attention) replicate the formal
definitions in floating point, exactly as every chapter demo does — the exact theorems
are proved in the chapter files; what is tested here is that the running code agrees
with them, with tolerances, using native `Float.beq`/`Float.abs` helpers (`Decidable`
instances on `Float` propositions are avoided: they can reduce to `sorry` at execution).

A failure here means an implementation drifted from the specification it proves.
-/

open LeanDL LeanDL.Ch05 LeanDL.Ch18 Tensors

/-- Native boolean comparisons for `Float` (no `Decidable` on `Float` propositions). -/
def geB (x b : Float) : Bool := Float.beq (x - b) (Float.abs (x - b))
def ltB (x b : Float) : Bool := !geB x b

section RatChecks

/-- An exact positive rational `(w % d + 1) / d` from a raw word. -/
def posRat (w d : Nat) : Rat := Rat.ofInt (Int.ofNat (w % d + 1)) / Rat.ofInt (Int.ofNat d)

def word (g : Rng) : Nat × Rng :=
  let (x, g') := Rng.next g
  (UInt64.toNat x, g')

/-- Ch05: the SGD iterate equals the proved closed form; contraction when `η·a ≤ 1`. -/
def prop_sgd (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 0x9E3779B97F4A7C15
  let mut ok := true
  for _ in [0:n] do
    let (w1, g1) := word g
    let (w2, g2) := word g1
    let (w3, g3) := word g2
    let (w4, _) := word g3
    let η : Rat := posRat w1 100
    let a : Rat := Rat.ofInt (Int.ofNat (w2 % 4 + 1))
    let t := w3 % 12
    let w0 : Rat := Rat.ofInt (Int.ofNat (w4 % 2001)) / Rat.ofInt 10
    ok := ok && decide (sgdQuad η a w0 t == powN (1 - η * a) t * w0)
    if decide (η * a ≤ 1) then
      ok := ok && decide (Rat.abs (sgdQuad η a w0 t) ≤ Rat.abs w0)
  return ok

/-- Ch18: exact quantization bounds. -/
def prop_quant (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 0x2545F4914F6CDD1D
  let mut ok := true
  for _ in [0:n] do
    let (w1, g1) := word g
    let (w2, _) := word g1
    let s : Rat := posRat w1 256
    let x : Rat := Rat.ofInt (Int.ofNat (w2 % 513)) / Rat.ofInt 16 - 16
    ok := ok && decide (Rat.abs (x - quant s x) < s)
      && decide (Rat.abs (x - roundq s x) ≤ s / 2)
  return ok

/-- Ch18: MoE load-balance floor `Σ p² ≥ 1/E` on random routers (E = 8). -/
def prop_moe (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 0x12345678
  let mut ok := true
  for _ in [0:n] do
    let mut raw : Vec Rat 8 := fun _ => 0
    for i in [0:8] do
      let (w, g') := word g
      g := g'
      raw := fun j => if j.val == i then posRat w 997 else raw j
    let z : Rat := Vec.dot (fun _ : Fin 8 => (1 : Rat)) raw
    let p : Vec Rat 8 := fun i => raw i * z⁻¹
    ok := ok && decide (Vec.dot p p ≥ (1 : Rat) / 8)
  return ok

end RatChecks

/-- Core.Tensor: the flat emulation equals the formal `Mat.mulVec`, entry for
entry, on random exact tensors (m = 3, n = 4); flatten/matricize round-trips. -/
def cells (g : Rng) (k : Nat) (acc : List Rat) : Rng × List Rat :=
  match k with
  | 0 => (g, acc)
  | k + 1 =>
      let (w, g') := word g
      cells g' k ((Rat.ofInt (Int.ofNat (w % 4001)) / Rat.ofInt 100 - 20) :: acc)

def prop_tensor (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 0xC0FFEE123456789
  let mut ok := true
  for _ in [0:n] do
    let (g1, cellsA) := cells g 12 []
    let (g2, cellsV) := cells g1 4 []
    g := g2
    let A : Tensor Rat 3 4 := fun i => cellsA.getD i.val 0
    let v : Fin 4 → Rat := fun j => cellsV.getD j.val 0
    -- the flat loop == the proved matrix product, on every output row
    ok := ok && decide (flatMulVec A v (0 : Fin 3) == Mat.mulVec (toMat A) v (0 : Fin 3))
      && decide (flatMulVec A v (1 : Fin 3) == Mat.mulVec (toMat A) v (1 : Fin 3))
      && decide (flatMulVec A v (2 : Fin 3) == Mat.mulVec (toMat A) v (2 : Fin 3))
    -- the proved round trip fromMat (toMat A) == A, exercised on every cell
    ok := ok && (List.range 12).all fun k =>
      fromMat (toMat A) (⟨k % 12, Nat.mod_lt _ (by omega)⟩ : Fin 12)
        == A (⟨k % 12, Nat.mod_lt _ (by omega)⟩ : Fin 12)
  return ok

section FloatMirrors

/-- Float mirror of the exact `softmax` (max-subtracted, as the demos run it). -/
def softmaxF (z : Array Float) : Array Float := Id.run do
  let mut mx := z[0]!
  for v in z do if ltB mx v then mx := v
  let mut Z := 0.0
  for v in z do Z := Z + Float.exp (v - mx)
  z.map fun v => Float.exp (v - mx) / Z

def sumArr (a : Array Float) : Float := a.foldl (· + ·) 0.0
def meanArr (a : Array Float) : Float := sumArr a / Float.ofInt (Int.ofNat a.size)

/-- Float mirror of the exact `layerNorm` (same formula; `HasAct` read as Float ops). -/
def layerNormF (eps : Float) (x : Array Float) : Array Float := Id.run do
  let m := meanArr x
  let v := meanArr (x.map fun a => (a - m) * (a - m))
  let s := Float.sqrt (v + eps)
  x.map fun a => (a - m) / s

/-- Float mirror of `attendM` under the causal mask `j ≤ t`. -/
def attendF (t : Nat) (s v : Array Float) : Float := Id.run do
  let mut num := 0.0
  let mut den := 0.0
  for j in [0:v.size] do
    if j ≤ t then
      let e := Float.exp s[j]!
      num := num + e * v[j]!
      den := den + e
  num / den

def prop_softmax_f (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 7
  let mut ok := true
  for _ in [0:n] do
    let (z, g') := (Rng.seed g.state).uniformArray 8 1.0
    g := g'
    let p := softmaxF z
    ok := ok && (p.toList.all fun q => geB q 0.0)
      && ltB (Float.abs (sumArr p - 1.0)) 1e-9
  return ok

def prop_layerNorm_f (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 11
  let mut ok := true
  for _ in [0:n] do
    let (x, g') := (Rng.seed g.state).uniformArray 16 1.0
    let (c, g'') := Rng.uniform g'
    g := g''
    let y := layerNormF 1e-5 x
    let ys := layerNormF 1e-5 (x.map fun a => a + (2 * c - 1))
    ok := ok
      && ltB (Float.abs (meanArr y)) 1e-9
      && ltB (Float.abs (meanArr (y.map fun a => a * a) - 1.0)) 1e-3
      && ltB (Float.abs (y[0]! - ys[0]!)) 1e-6
  return ok

def prop_causal_f (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 13
  let mut ok := true
  for _ in [0:n] do
    let (s1, g') := (Rng.seed g.state).uniformArray 8 1.0
    let (v1, g'') := g'.uniformArray 8 1.0
    g := g''
    let s2 := s1.mapIdx fun j a => if j ≤ (3 : Nat) then a else a + 9.7
    let v2 := v1.mapIdx fun j a => if j ≤ (3 : Nat) then a else a + 5.1
    ok := ok && ltB (Float.abs (attendF 3 s1 v1 - attendF 3 s2 v2)) 1e-12
  return ok

/-- Exact value of a (normal) binary64 as a `Rat`, via its raw bits:
`(man + 2^52) · 2^(exp − 1075)` with the sign. -/
def ratOfFloat (x : Float) : Rat := Id.run do
  let bits := x.toBits
  let s := UInt64.shiftRight bits 63
  let e := UInt64.toNat ((UInt64.shiftRight bits 52) &&& 0x7FF)
  let m := UInt64.toNat (bits &&& 0xFFFFFFFFFFFFF)
  let v : Rat :=
    if e == 0 then
      -- zero and subnormals: m · 2^(-1074)
      Rat.ofInt (Int.ofNat m) / Rat.ofInt (Int.ofNat (2 ^ 1074))
    else
      -- normals: (m + 2^52) · 2^(e − 1075)
      (Rat.ofInt (Int.ofNat m) + powRat 2 52) * pow2Rat (e : Int)
  if s == 1 then -v else v
where
  powRat (b : Nat) : Nat → Rat
    | 0 => 1
    | k + 1 => Rat.ofInt (Int.ofNat b) * powRat b k
  pow2Rat (e : Int) : Rat :=
    -- 2^(e − 1075): multiply by 2^(e) for e ≥ 1075, divide by 2^(1075 − e)
    if e ≥ 1075 then
      Rat.ofInt (Int.ofNat (2 ^ (e - 1075).toNat))
    else
      1 / Rat.ofInt (Int.ofNat (2 ^ (1075 - e).toNat))

/-- Core.Rounding, numerically: the sequential floating dot product
(`acc := fl(acc + fl(xᵢ·yᵢ))`, mirroring `flDot`) satisfies the **proved**
Higham bound `|acc − Σ xᵢyᵢ| ≤ γ₍₂ₙ₎ · Σ |xᵢyᵢ|` (`flDot_error`) with
`u = 2⁻⁵³`, checked EXACTLY in `Rat`: the float accumulator is converted to
its exact binary value (`ratOfFloat`) and the exact dot is accumulated over
the `Rat` mirrors of the inputs. This validates the *instantiation*
`u = 2⁻⁵³` on binary64 (a platform hypothesis, see the Rounding.lean
docstring — Lean has no IEEE-754 theory for `Float`); the bound theorem
itself is proved over `Rat`. -/
def prop_rounding_f (n : Nat) : Bool := Id.run do
  let mut g := Rng.seed 0x243F6A8885A308D3
  let mut ok := true
  for _ in [0:n] do
    let mut xs : Array Float := #[]
    let mut ys : Array Float := #[]
    let mut xsr : Array Rat := #[]
    let mut ysr : Array Rat := #[]
    for _ in [0:8] do
      let (w1, g1) := word g
      let (w2, g2) := word g1
      g := g2
      -- random dyadic values in [-8, 8): exact in binary64 and in Rat
      let mk (w : Nat) : Float × Rat :=
        (Float.ofInt (Int.ofNat (w % 512) - 256) / 32.0,
         Rat.ofInt (Int.ofNat (w % 512) - 256) / Rat.ofInt 32)
      let (x, xr) := mk w1
      let (y, yr) := mk w2
      xs := xs.push x
      ys := ys.push y
      xsr := xsr.push xr
      ysr := ysr.push yr
    let mut accF : Float := 0.0
    let mut dotR : Rat := 0
    let mut sumAbsR : Rat := 0
    for i in [0:xs.size] do
      accF := accF + (xs[i]! * ys[i]!)
      dotR := dotR + xsr[i]! * ysr[i]!
      sumAbsR := sumAbsR + Rat.abs (xsr[i]! * ysr[i]!)
    let k : Nat := 2 * xs.size
    let ku : Rat := Rat.ofInt (Int.ofNat k) / Rat.ofInt (Int.ofNat (2 ^ 53))
    let γ : Rat := ku / (1 - ku)
    let err : Rat := Rat.abs (ratOfFloat accF - dotR)
    ok := ok && decide (err ≤ γ * sumAbsR)
  return ok

end FloatMirrors

/-! ## IEEE-754 observable signatures (Ch05 — Core/Ieee754.lean)

Lean has **no IEEE-754 theory for `Float`**: that binary64 implements the
grid of `Core/Ieee754.lean` (with `roundTiesToEven`) is a platform
hypothesis. What can be *observed* is the grid's fingerprint on the
machine: -/

def prop_ieee754 : Bool :=
  -- exact dyadic constants: numerators < 2^53 divided by powers of two,
  -- so each division below is exact in binary64 (no rounding)
  let halfUlp : Float := 1.0 / 9007199254740992.0  -- 2⁻⁵³
  let ulp : Float := 1.0 / 4503599627370496.0      -- 2⁻⁵²
  -- `1 + 2⁻⁵³`: the half-ulp of binade [1,2) is 2⁻⁵³ — adding it to 1
  -- lands exactly on a tie, which `roundTiesToEven` resolves DOWN (1 is
  -- even), so the sum is exactly 1.
  (1.0 + halfUlp == (1.0 : Float)) &&
  -- `1 + 2⁻⁵²`: one full ulp — representable, the sum moves.
  (1.0 + ulp != (1.0 : Float)) &&
  -- `1 + 3·2⁻⁵³` = 1 + 1.5 ulp: exactly halfway between 1 + 2⁻⁵²
  -- (odd mantissa) and 1 + 2⁻⁵¹ (even mantissa). `roundTiesToEven`
  -- resolves UP to the even neighbour: 1 + 2⁻⁵¹.
  (1.0 + 3.0 * halfUlp == 1.0 + ulp + ulp) &&
  -- decimal fractions are not grid points: 0.1 + 0.2 ≠ 0.3 — the
  -- grid's signature on decimals (each summand is rounded; the exact
  -- sum of the two rounded values is strictly above the grid point 0.3).
  (0.1 + 0.2 != (0.3 : Float))

def main : IO UInt32 := do
  let mut fails : List String := []
  for (name, b) in
    [ ("Ch05 sgdQuad == powN closed form + contraction (200 Rat draws)", prop_sgd 200),
      ("Ch18 |x - quant s x| < s and |x - roundq s x| <= s/2 (500 Rat draws)", prop_quant 500),
      ("Ch18 MoE sum p^2 >= 1/8 (200 Rat routers)", prop_moe 200),
      ("Core.Tensor: flatMulVec == Mat.mulVec + flatten round-trip (300 Rat tensors)", prop_tensor 300),
      ("Float softmax: positive weights, sum == 1 (500 rows)", prop_softmax_f 500),
      ("Float layerNorm: mean 0, var 1, shift-invariant (500 rows)", prop_layerNorm_f 500),
      ("Float causal attention: rows j>3 invisible at t=3 (500 draws)", prop_causal_f 500),
      ("Core.Rounding |fl dot - exact dot| <= gamma_(2n) * sum |xi yi|, exact Rat check (500 dots)", prop_rounding_f 500),
      ("Core.Ieee754 binary64 grid fingerprint: 1+2^-53 == 1, 1+2^-52 != 1, ties-to-even 1+3*2^-53 == 1+2^-51, 0.1+0.2 != 0.3", prop_ieee754) ] do
    IO.println s!"{if b then "PASS" else "FAIL"}  {name}"
    if !b then fails := fails ++ [name]
  if fails.isEmpty then
    IO.println "ALL PROPERTIES PASS"
    return 0
  else
    IO.println s!"FAILED: {fails}"
    return 1
