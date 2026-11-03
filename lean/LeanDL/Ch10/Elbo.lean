import LeanDL.Core.Prob

/-!
# Chapter 10 — the ELBO, proved

The VAE loss is not a heuristic: it is a **lower bound on the log-likelihood**
of the data, and the training objective (reconstruction − KL) is exactly that
bound. This section proves it over exact `Rat`, for a finite latent space,
using only the Core probability layer (`Dist`, `LawfulLog`).

Setup: `P` is the **joint** `p(z, x)` over the `n` latent states —
not normalised. With a likelihood factor `e`, the marginal
`m = ∑ᵢ P.w i · e i` is the evidence `p(x)`.
`q` is the encoder's variational distribution `q(z)`. Then

    E_q [ log e ] − KL(q ‖ p(·, x))  ≤  log p(x)      (log-marginal inequality)

The left side, rearranged, *is* the VAE objective: expected log-likelihood
(reconstruction) minus the KL penalty. Equality holds exactly when `q` is the
true posterior — the KL term in the loss is the price of the encoder's
approximation, not a regulariser pulled out of thin air.
-/

namespace LeanDL.Ch10

open Lean.Grind LeanDL

section Elbo

variable {n : Nat}

/-- Dot products respect pointwise equal products: the cancellation lemma
that moves mass from `q` to the joint. -/
theorem dot_congr {n : Nat} (w x f g : Vec Rat n)
    (h : (fun i => w i * f i) = (fun i => x i * g i)) : Vec.dot w f = Vec.dot x g := by
  induction n with
  | zero => simp only [Vec.dot]
  | succ n ih =>
      show w 0 * f 0 + Vec.dot (fun i => w (Fin.succ i)) (fun i => f (Fin.succ i))
        = x 0 * g 0 + Vec.dot (fun i => x (Fin.succ i)) (fun i => g (Fin.succ i))
      have h0 : w 0 * f 0 = x 0 * g 0 := congrFun h 0
      have ht : (fun i => w (Fin.succ i) * f (Fin.succ i))
          = (fun i => x (Fin.succ i) * g (Fin.succ i)) := by
        funext i; exact congrFun h (Fin.succ i)
      rw [ih (fun i => w (Fin.succ i)) (fun i => x (Fin.succ i))
        (fun i => f (Fin.succ i)) (fun i => g (Fin.succ i)) ht, h0]

/-- A dot product of strictly positive vectors is strictly positive
(the evidence `p(x)` really is `> 0`). -/
theorem dot_pos {n : Nat} (hn : 0 < n) (w f : Vec Rat n)
    (hw : ∀ i, 0 < w i) (hf : ∀ i, 0 < f i) : 0 < Vec.dot w f := by
  induction n with
  | zero => exact absurd hn (Nat.not_lt_zero 0)
  | succ n ih =>
      show 0 < w 0 * f 0 + Vec.dot (fun i => w (Fin.succ i)) (fun i => f (Fin.succ i))
      have h0 : 0 < w 0 * f 0 := Rat.mul_pos (hw 0) (hf 0)
      cases n with
      | zero =>
          have ht : Vec.dot (fun i => w (Fin.succ i)) (fun i => f (Fin.succ i)) = 0 := by
            simp only [Vec.dot]
          rw [ht]
          grind
      | succ n =>
          have ht : 0 < Vec.dot (fun i => w (Fin.succ i)) (fun i => f (Fin.succ i)) :=
            ih (Nat.succ_pos n) (fun i => w (Fin.succ i)) (fun i => f (Fin.succ i))
              (fun i => hw (Fin.succ i)) (fun i => hf (Fin.succ i))
          grind

/-- `∑ᵢ qᵢ · Pᵢ eᵢ / qᵢ / m = (∑ᵢ Pᵢ eᵢ) / m`: the importance weights cancel
exactly (over `Rat`, `qᵢ · qᵢ⁻¹ = 1`, no rounding). -/
theorem elbo_usum (P q : Dist n) (e : Vec Rat n) (m : Rat) :
    Vec.dot q.w (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹) = Vec.dot P.w e * m⁻¹ := by
  have hsmul : (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹)
      = (fun i => m⁻¹ * (P.w i * e i * (q.w i)⁻¹)) := by
    funext i; grind [Rat.mul_assoc, Rat.mul_comm]
  have hpt : (fun i => q.w i * (P.w i * e i * (q.w i)⁻¹)) = (fun i => P.w i * e i) := by
    funext i
    have hc : q.w i * (q.w i)⁻¹ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt (q.pos i))
    rw [show q.w i * (P.w i * e i * (q.w i)⁻¹) = (q.w i * (q.w i)⁻¹) * (P.w i * e i)
        by grind [Rat.mul_assoc, Rat.mul_comm]]
    rw [hc, Rat.one_mul]
  have hinner : Vec.dot q.w (fun i => P.w i * e i * (q.w i)⁻¹) = Vec.dot P.w e :=
    dot_congr q.w P.w (fun i => P.w i * e i * (q.w i)⁻¹) e hpt
  rw [hsmul, Vec.dot_smul_right, hinner]
  grind [Rat.mul_comm]

-- ANCHOR: elbo
/-- **The evidence bound (log-marginal inequality).** Let `P` be the joint
`p(z, x)` on `n > 0` latent states (weights `> 0`, no normalisation), `e` the
likelihood factor, and `m = ∑ᵢ p(zᵢ, x) eᵢ = p(x)` the evidence. For every
encoder distribution `q`:

    E_q [ log (p(z, x) e) ] − KL(q ‖ P) ≤ log m

*Proof, in words.* Apply the tangent inequality `log t ≤ t − 1` to the
importance weights `tᵢ = Pᵢ eᵢ / (qᵢ m) > 0`, expand the log into
`log eᵢ + log Pᵢ − log qᵢ − log m`, take the `q`-expectation, and use the
exact cancellation `∑ qᵢ · Pᵢ eᵢ / (qᵢ m) = (∑ Pᵢ eᵢ)/m = 1`. The expectation
of the left side is `E[log] − KL − log m ≤ 1 − 1 = 0`. Everything is finite
sums over `Rat`; the only analytic input is the tangent inequality, carried
by `LawfulLog` (the real logarithm obeys it; `Float` only approximately). -/
theorem evidence_bound [LawfulLog] (P q : Dist n) (e : Vec Rat n) (he : ∀ i, 0 < e i)
    (m : Rat) (hm : Vec.dot P.w e = m) :
    q.expect (fun i => LawfulLog.log (e i)) - q.kl P ≤ LawfulLog.log m := by
  have hn : 0 < n := by
    rcases n with _ | n
    · have h0 : (0 : Rat) = 1 := by rw [← P.sum1]; rfl
      exact absurd h0 (by norm_cast)
    · exact Nat.succ_pos n
  have hm0 : 0 < m := by rw [← hm]; exact dot_pos hn P.w e P.pos he
  have hminv : 0 < m⁻¹ := inv_pos' hm0
  have hu : ∀ i, 0 < P.w i * e i * (q.w i)⁻¹ * m⁻¹ := fun i =>
    Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (P.pos i) (he i)) (inv_pos' (q.pos i))) hminv
  have hsum : Vec.dot q.w (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹) = 1 := by
    rw [elbo_usum P q e m, hm]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hm0)
  have hsum1 : Vec.dot q.w (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹ - 1) = 0 := by
    have hadd : (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹ - 1)
        = (fun i => P.w i * e i * (q.w i)⁻¹ * m⁻¹ + (-1 : Rat)) := by
      funext i; exact Rat.sub_eq_add_neg _ _
    rw [hadd, Vec.dot_add_right, hsum]
    have hc : Vec.dot q.w (fun _ => (-1 : Rat)) = -1 := by
      rw [dot_smul_const, q.sum1]
      exact Rat.mul_one (-1)
    rw [hc]
    grind
  have hlog : (fun i => LawfulLog.log (P.w i * e i * (q.w i)⁻¹ * m⁻¹))
      = (fun i => LawfulLog.log (e i) + (LawfulLog.log (P.w i) - LawfulLog.log (q.w i))
          - LawfulLog.log m) := by
    funext i
    have hp : 0 < P.w i := P.pos i
    have hq : 0 < q.w i := q.pos i
    have hpe : 0 < P.w i * e i := Rat.mul_pos hp (he i)
    have hqinv : 0 < (q.w i)⁻¹ := inv_pos' hq
    have hpei : 0 < P.w i * e i * (q.w i)⁻¹ := Rat.mul_pos hpe hqinv
    rw [LawfulLog.log_mul (x := P.w i * e i * (q.w i)⁻¹) (y := m⁻¹) hpei hminv,
        LawfulLog.log_mul (x := P.w i * e i) (y := (q.w i)⁻¹) hpe hqinv,
        LawfulLog.log_mul (x := P.w i) (y := e i) hp (he i),
        LawfulLog.log_inv _ (Rat.ne_of_gt hq),
        LawfulLog.log_inv _ (Rat.ne_of_gt hm0)]
    grind
  have hj : Vec.dot q.w (fun i => LawfulLog.log (e i)
      + (LawfulLog.log (P.w i) - LawfulLog.log (q.w i)) - LawfulLog.log m) ≤ 0 := by
    rw [← hlog]
    have hle : ∀ i, LawfulLog.log (P.w i * e i * (q.w i)⁻¹ * m⁻¹)
        ≤ P.w i * e i * (q.w i)⁻¹ * m⁻¹ - 1 := fun i => LawfulLog.log_le _ (hu i)
    refine Rat.le_trans (dot_mono q.w _ _ (fun i => Rat.le_of_lt (q.pos i)) hle) ?_
    rw [hsum1]
    grind
  have hkl : q.kl P = -(Vec.dot q.w (fun i => LawfulLog.log (P.w i) - LawfulLog.log (q.w i))) := by
    have hpoint : (fun i => LawfulLog.log (q.w i) - LawfulLog.log (P.w i))
        = (fun i => -(LawfulLog.log (P.w i) - LawfulLog.log (q.w i))) := by
      funext i; grind [Rat.sub_eq_add_neg]
    calc q.kl P
        = Vec.dot q.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (P.w i)) := rfl
      _ = Vec.dot q.w (fun i => -(LawfulLog.log (P.w i) - LawfulLog.log (q.w i))) := by rw [hpoint]
      _ = -(Vec.dot q.w (fun i => LawfulLog.log (P.w i) - LawfulLog.log (q.w i))) :=
          dot_neg q.w ..
  have hexp : Vec.dot q.w (fun i => LawfulLog.log (e i)
      + (LawfulLog.log (P.w i) - LawfulLog.log (q.w i)) - LawfulLog.log m)
      = q.expect (fun i => LawfulLog.log (e i)) - q.kl P - LawfulLog.log m := by
    have hsub : (fun i => LawfulLog.log (e i) + (LawfulLog.log (P.w i) - LawfulLog.log (q.w i)) - LawfulLog.log m)
        = (fun i => (LawfulLog.log (e i) + (LawfulLog.log (P.w i) - LawfulLog.log (q.w i))) + (-(LawfulLog.log m))) := by
      funext i; grind
    rw [hsub, Vec.dot_add_right, Vec.dot_add_right, dot_neg, dot_smul_const, q.sum1, Rat.mul_one]
    have hdot : Vec.dot q.w (fun i => LawfulLog.log (P.w i) - LawfulLog.log (q.w i))
        = -(q.kl P) :=
      calc Vec.dot q.w (fun i => LawfulLog.log (P.w i) - LawfulLog.log (q.w i))
          = -(-(Vec.dot q.w (fun i => LawfulLog.log (P.w i) - LawfulLog.log (q.w i)))) :=
            (Rat.neg_neg _).symm
        _ = -(q.kl P) := by rw [hkl]
    rw [show q.expect (fun i => LawfulLog.log (e i))
        = Vec.dot q.w (fun i => LawfulLog.log (e i)) from rfl, hdot]
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  rw [hexp] at hj
  grind
-- ANCHOR_END: elbo

-- ANCHOR: elbo_gap
/-- **The gap is exactly the KL to the posterior.** Renormalising the joint
to the posterior `p(zᵢ ∣ x) = Pᵢ eᵢ / m`, the bound is tight exactly when the
encoder *is* the posterior:

    log m − (E_q [ log e ] − KL(q ‖ P)) = KL(q ‖ posterior) ≥ 0

This is the sentence the VAE chapter teaches: the KL term in the loss is the
encoder's approximation error, and the reconstruction term is the bound. -/
theorem elbo_gap [LawfulLog] (P q : Dist n) (e : Vec Rat n) (he : ∀ i, 0 < e i)
    (m : Rat) (hm : Vec.dot P.w e = m) :
    LawfulLog.log m - (q.expect (fun i => LawfulLog.log (e i)) - q.kl P)
      = Vec.dot q.w (fun i => LawfulLog.log (q.w i)
          - LawfulLog.log (P.w i * e i * m⁻¹)) := by
  have hn : 0 < n := by
    rcases n with _ | n
    · have h0 : (0 : Rat) = 1 := by rw [← P.sum1]; rfl
      exact absurd h0 (by norm_cast)
    · exact Nat.succ_pos n
  have hm0 : 0 < m := by rw [← hm]; exact dot_pos hn P.w e P.pos he
  have hpostw' : ∀ i, LawfulLog.log (P.w i * e i * m⁻¹)
      = LawfulLog.log (P.w i) + LawfulLog.log (e i) - LawfulLog.log m := by
    intro i
    have hp : 0 < P.w i := P.pos i
    have hpe : 0 < P.w i * e i := Rat.mul_pos hp (he i)
    rw [LawfulLog.log_mul (x := P.w i * e i) (y := m⁻¹) hpe (inv_pos' hm0),
        LawfulLog.log_mul (x := P.w i) (y := e i) hp (he i),
        LawfulLog.log_inv _ (Rat.ne_of_gt hm0)]
    grind
  have hpostw : (fun i => LawfulLog.log (P.w i * e i * m⁻¹))
      = (fun i => LawfulLog.log (P.w i) + LawfulLog.log (e i) - LawfulLog.log m) :=
    funext hpostw'
  rw [show (fun i => LawfulLog.log (q.w i) - LawfulLog.log (P.w i * e i * m⁻¹))
      = (fun i => LawfulLog.log (q.w i) - (LawfulLog.log (P.w i) + LawfulLog.log (e i) - LawfulLog.log m))
      by funext i; rw [hpostw' i]]
  have hpoint : (fun i => LawfulLog.log (q.w i)
      - (LawfulLog.log (P.w i) + LawfulLog.log (e i) - LawfulLog.log m))
      = (fun i => (LawfulLog.log (q.w i) - LawfulLog.log (P.w i)) - LawfulLog.log (e i)
          + LawfulLog.log m) := by
    funext i; grind
  rw [hpoint, Vec.dot_add_right, dot_sub, dot_sub, dot_smul_const, q.sum1, Rat.mul_one]
  rw [show q.expect (fun i => LawfulLog.log (e i))
      = Vec.dot q.w (fun i => LawfulLog.log (e i)) from rfl]
  rw [show Vec.dot q.w (fun i => LawfulLog.log (q.w i)) - Vec.dot q.w (fun i => LawfulLog.log (P.w i))
      = Vec.dot q.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (P.w i))
      from (dot_sub ..).symm]
  have hklp : Vec.dot q.w (fun i => LawfulLog.log (q.w i) - LawfulLog.log (P.w i))
      = q.kl P := rfl
  rw [hklp]
  grind [Rat.sub_eq_add_neg]

/-- **Non-negativity of the gap**: the KL to the posterior is `≥ 0` — an
instance of Gibbs (`Dist.kl_nonneg`) applied to `q` and the renormalised
posterior `Pᵢ eᵢ / m`. -/
theorem elbo_gap_ge_zero [LawfulLog] (P q : Dist n) (e : Vec Rat n) (he : ∀ i, 0 < e i)
    (m : Rat) (hm : Vec.dot P.w e = m) :
    0 ≤ LawfulLog.log m - (q.expect (fun i => LawfulLog.log (e i)) - q.kl P) := by
  have hn : 0 < n := by
    rcases n with _ | n
    · have h0 : (0 : Rat) = 1 := by rw [← P.sum1]; rfl
      exact absurd h0 (by norm_cast)
    · exact Nat.succ_pos n
  have hm0 : 0 < m := by rw [← hm]; exact dot_pos hn P.w e P.pos he
  -- The posterior weights P.w i * e i * m⁻¹ are positive and sum to 1.
  have hpost1 : Vec.dot (fun i => P.w i * e i * m⁻¹) (fun _ => (1 : Rat)) = 1 := by
    have hf1 : (fun i => P.w i * e i * m⁻¹) = (fun i => m⁻¹ * (P.w i * e i)) := by
      funext i; grind [Rat.mul_assoc, Rat.mul_comm]
    rw [hf1, Vec.dot_smul_left]
    have he1 : Vec.dot (fun i => P.w i * e i) (fun _ => (1 : Rat)) = Vec.dot P.w e :=
      dot_congr (fun i => P.w i * e i) P.w (fun _ => (1 : Rat)) e (by
        funext i; exact Rat.mul_one (P.w i * e i))
    rw [he1, hm]
    exact Rat.inv_mul_cancel m (Rat.ne_of_gt hm0)
  let post : Dist n :=
    ⟨fun i => P.w i * e i * m⁻¹,
      fun i => Rat.mul_pos (Rat.mul_pos (P.pos i) (he i)) (inv_pos' hm0), hpost1⟩
  rw [elbo_gap P q e he m hm]
  exact Dist.kl_nonneg q post
-- ANCHOR_END: elbo_gap

end Elbo

end LeanDL.Ch10
