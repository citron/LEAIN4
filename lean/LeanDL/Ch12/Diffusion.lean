import LeanDL.Core.Algebra

/-!
# Chapter 12 — Diffusion models: the algebra of noising and denoising

A diffusion model corrupts data with many small doses of noise, then learns to undo them.
One noising step is `x ↦ a·x + s·ε` with `a² + s² = 1` ("variance preserving"). Here we prove the
bookkeeping that makes training cheap and sampling exact, over any commutative ring or field.
(That a sum of independent Gaussians is Gaussian is *not* formalised; we prove the algebra of
the coefficients.)
-/

namespace LeanDL.Ch12

open Lean.Grind

variable {α : Type}

section Schedule

variable [CommRing α]

-- ANCHOR: schedule
/-- A schedule is a list of steps `(a, s)`, each with `a² + s² = 1`. `cumA` is the product of the
`a`s: the factor by which the original signal survives all the steps. -/
def cumA : List (α × α) → α
  | [] => 1
  | (a, _) :: rest => a * cumA rest

/-- Variance after all steps, starting from variance `v`: each step maps `v ↦ a²v + s²`. -/
def noiseVar : List (α × α) → α → α
  | [], v => v
  | (a, s) :: rest, v => noiseVar rest (a * a * v + s * s)

/-- **Closed form of the whole forward process.** After any number of steps, the variance is
`ā²·v + (1 − ā²)`: only the product `ā` of the `a`s matters. This is why training can jump to a
random time `t` in one go. -/
theorem noiseVar_closed (l : List (α × α)) (hl : ∀ p ∈ l, p.1 * p.1 + p.2 * p.2 = 1) (v : α) :
    noiseVar l v = cumA l * cumA l * v + (1 - cumA l * cumA l) := by
  induction l generalizing v with
  | nil => simp only [noiseVar, cumA]; grind
  | cons p rest ih =>
    obtain ⟨a, s⟩ := p
    have hp := hl (a, s) (by simp)
    have hr : ∀ q ∈ rest, q.1 * q.1 + q.2 * q.2 = 1 := fun q hq => hl q (by simp [hq])
    simp only [noiseVar, cumA]
    rw [ih hr]
    simp only at hp
    grind

/-- Starting from unit variance, the process stays at unit variance: it *preserves variance*. -/
theorem noiseVar_preserved (l : List (α × α)) (hl : ∀ p ∈ l, p.1 * p.1 + p.2 * p.2 = 1) :
    noiseVar l 1 = 1 := by
  rw [noiseVar_closed l hl]
  grind

/-- Starting from clean data (variance `0`), the noise variance is `1 − ā²`. -/
theorem noiseVar_from_clean (l : List (α × α)) (hl : ∀ p ∈ l, p.1 * p.1 + p.2 * p.2 = 1) :
    noiseVar l 0 = 1 - cumA l * cumA l := by
  rw [noiseVar_closed l hl]
  grind
-- ANCHOR_END: schedule

end Schedule

section Denoise

variable [Field α]

-- ANCHOR: denoise
/-- Given a noised point `xt = ā x₀ + σ ε` and a guess `ε̂` of the noise, estimate the clean point. -/
def x0Hat (ab sg xt eps : α) : α := (xt - sg * eps) / ab

/-- A deterministic (DDIM) step from noise level `(ā_t, σ_t)` to `(ā_s, σ_s)`: keep the estimate of
the clean point and the estimate of the noise, and rebuild the point at the new noise level. -/
def ddimStep (abT sgT abS sgS xt eps : α) : α := abS * x0Hat abT sgT xt eps + sgS * eps

/-- With the true noise, the clean point is recovered exactly. -/
theorem x0Hat_recovers (ab sg x0 e : α) (h : ab ≠ 0) : x0Hat ab sg (ab * x0 + sg * e) e = x0 := by
  simp only [x0Hat]
  grind

/-- **The sampler is exact when the network is.** A perfect noise predictor takes the point
`ā_t x₀ + σ_t ε` to exactly `ā_s x₀ + σ_s ε`, the point that the forward process would have
produced at the new noise level. -/
theorem ddim_exact (abT sgT abS sgS x0 e : α) (h : abT ≠ 0) :
    ddimStep abT sgT abS sgS (abT * x0 + sgT * e) e = abS * x0 + sgS * e := by
  simp only [ddimStep]
  rw [x0Hat_recovers abT sgT x0 e h]

/-- Chaining two exact steps equals one exact step: denoising can be done in any number of
stages. -/
theorem ddim_compose (a1 s1 a2 s2 a3 s3 x0 e : α) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) :
    ddimStep a2 s2 a3 s3 (ddimStep a1 s1 a2 s2 (a1 * x0 + s1 * e) e) e = a3 * x0 + s3 * e := by
  rw [ddim_exact a1 s1 a2 s2 x0 e h1, ddim_exact a2 s2 a3 s3 x0 e h2]
-- ANCHOR_END: denoise

end Denoise

end LeanDL.Ch12
