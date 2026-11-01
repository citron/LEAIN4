/-!
# A small deterministic random number generator (xorshift64*)

Training must be reproducible, so the course never uses system randomness.
-/

namespace LeanDL

structure Rng where
  state : UInt64

namespace Rng

def seed (s : UInt64) : Rng := ⟨if s = 0 then 88172645463325252 else s⟩

def next (r : Rng) : UInt64 × Rng :=
  let x := r.state
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, ⟨x⟩)

/-- Uniform in `[0, 1)`. -/
def uniform (r : Rng) : Float × Rng :=
  let (u, r') := r.next
  ((u >>> 11).toFloat / 9007199254740992.0, r')

/-- `n` samples uniform in `[-scale, scale)`. -/
def uniformArray (r : Rng) (n : Nat) (scale : Float) : Array Float × Rng := Id.run do
  let mut r := r
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let (u, r') := r.uniform
    out := out.push ((2 * u - 1) * scale)
    r := r'
  return (out, r)

/-- Standard normal sample (Box–Muller). -/
def normal (r : Rng) : Float × Rng :=
  let (u1, r) := r.uniform
  let (u2, r) := r.uniform
  (Float.sqrt (-2.0 * Float.log (max u1 1.0e-12)) * Float.cos (6.283185307179586 * u2), r)

end Rng

end LeanDL
