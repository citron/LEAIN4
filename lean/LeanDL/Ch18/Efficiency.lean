import LeanDL.Ch16.Tools
import LeanDL.Core.Sum
import LeanDL.Ch05.Optim

/-!
# Chapter 18 — Efficiency: quantization, mixture of experts, distillation, scaling

Modern deep learning at scale is an *efficiency* problem: fit a big model into few bits,
route each input to few parameters, transfer a teacher into a student, and predict what
more data and more parameters buy. Each of the four ideas below has a theorem that is
*exact over `Rat`* — quantization error bounded by one grid step (and half a step for
round-to-nearest), a hard floor on router imbalance, distillation loss floored by the
teacher's entropy, and a strictly decreasing power law in the data budget.

Everything here is mathematics on exact rationals; the `Float` demos show the same
formulas running.
-/

namespace LeanDL.Ch18

open Lean.Grind LeanDL

section Quantization

/-- **Uniform quantization** of an exact rational: the largest grid point of step `s`
not above `x`. This is exactly what an integer quantizer stores (up to the scale). -/
-- ANCHOR: quant
def quant (s : Rat) (x : Rat) : Rat := ↑(x / s).floor * s

/-- **Round-to-nearest quantization**: the grid point closest to `x` (ties downward). -/
def roundq (s : Rat) (x : Rat) : Rat := ↑(x / s + 1 / 2).floor * s

theorem qsx {s x : Rat} (hs : s ≠ 0) : x / s * s = x := Rat.div_mul_cancel hs

/-- The floor grid point never overshoots. -/
theorem quant_le (s x : Rat) (hs : 0 < s) : quant s x ≤ x := by
  show ↑(x / s).floor * s ≤ x
  have h := Rat.mul_le_mul_of_nonneg_right (Rat.floor_le (x / s)) (Rat.le_of_lt hs)
  rw [qsx (Rat.ne_of_gt hs)] at h
  exact h

/-- The floor grid point is within one step from below. -/
theorem quant_lt (s x : Rat) (hs : 0 < s) : x < quant s x + s := by
  show x < ↑(x / s).floor * s + s
  have hs' : s ≠ 0 := Rat.ne_of_gt hs
  have hcast : (↑((x / s).floor + 1 : Int) : Rat) * s = ↑(x / s).floor * s + s := by
    push_cast
    grind [Rat.add_mul]
  have h1 : x / s < ↑((x / s).floor + 1 : Int) := Rat.lt_floor_add_one (x / s)
  have h2 := Rat.mul_lt_mul_of_pos_right h1 hs
  rw [qsx hs'] at h2
  rw [hcast] at h2
  exact h2

theorem quant_err_lt (s x : Rat) (hs : 0 < s) : Rat.abs (x - quant s x) < s := by
  have hl : quant s x ≤ x := quant_le s x hs
  have hr : x < quant s x + s := quant_lt s x hs
  have hnon : 0 ≤ x - quant s x := by grind
  rw [Rat.abs_of_nonneg hnon]
  grind

theorem abs_le_of_bounds (x M : Rat) (h1 : -M ≤ x) (h2 : x ≤ M) : Rat.abs x ≤ M := by
  grind [Rat.abs.eq_1]

theorem floor_mul_le {s y : Rat} (hs : 0 < s) : ↑y.floor * s ≤ y * s :=
  Rat.mul_le_mul_of_nonneg_right (Rat.floor_le y) (Rat.le_of_lt hs)

theorem lt_floor_mul {s y : Rat} (hs : 0 < s) : y * s - s < ↑y.floor * s := by
  have h : y - 1 < ↑y.floor := Rat.lt_floor
  have h2 : (y - 1) * s < ↑y.floor * s := Rat.mul_lt_mul_of_pos_right h hs
  rw [show y * s - s = (y - 1) * s by grind]
  exact h2

/-- **Round-to-nearest halves the worst case**: the error is at most half a grid step.
This is the theorem behind the `±s/2` quantization noise of INT8 inference. -/
theorem roundq_err_le (s x : Rat) (hs : 0 < s) : Rat.abs (x - roundq s x) ≤ s / 2 := by
  show Rat.abs (x - ↑(x / s + 1 / 2).floor * s) ≤ s / 2
  have hprod : (x / s + 1 / 2) * s = x + s / 2 := by
    rw [Rat.add_mul, qsx (Rat.ne_of_gt hs)]
    grind
  have h1 : ↑(x / s + 1 / 2).floor * s ≤ x + s / 2 := by
    rw [← hprod]
    exact floor_mul_le (s := s) hs
  have h2 : x - s / 2 < ↑(x / s + 1 / 2).floor * s := by
    have h := lt_floor_mul (s := s) hs (y := x / s + 1 / 2)
    rw [hprod] at h
    grind
  have hlo : -(s / 2) ≤ x - ↑(x / s + 1 / 2).floor * s := by grind
  have hhi : x - ↑(x / s + 1 / 2).floor * s ≤ s / 2 := by grind
  exact abs_le_of_bounds _ _ hlo hhi

/-- Quantizing the *same* grid twice is a no-op: the quantizer is idempotent on its own
lattice — stored integers stay exact integers. -/
theorem quant_quant (s x : Rat) (hs : 0 < s) : quant s (quant s x) = quant s x := by
  show ↑((↑(x / s).floor * s) / s).floor * s = ↑(x / s).floor * s
  have h : (↑(x / s).floor * s) / s = ↑(x / s).floor := by
    rw [Rat.div_def]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.inv_mul_cancel s (Rat.ne_of_gt hs)]
  rw [h, Rat.floor_intCast]

-- ANCHOR_END: quant
end Quantization

section MixtureOfExperts

/-- **Load-balance bound.** If a router spreads probability `p` over `E` experts, the
collision probability `Σᵢ pᵢ²` (used as the auxiliary load-balancing loss in Switch
Transformer and GShard) has a hard floor of `1/E`: no router, however trained, can push
this auxiliary loss below it. Equal routing attains the floor. -/
-- ANCHOR: balance
theorem balance_ge {E : Nat} (hE : 0 < E) (p : Fin E → Rat)
    (hsum : vsum p = 1) : (E : Rat)⁻¹ ≤ vsum (fun i => p i * p i) := by
  have hsq : (E : Rat) * ((E : Rat)⁻¹ * (E : Rat)⁻¹) = (E : Rat)⁻¹ := by
    rw [← Rat.mul_assoc, Rat.mul_inv_cancel (a := (E : Rat))]
    · grind
    · norm_cast; omega
  have hpt : (fun i => (p i - (E : Rat)⁻¹) * (p i - (E : Rat)⁻¹))
      = (fun i => p i * p i + (-(2 * (E : Rat)⁻¹ * p i)) + ((E : Rat)⁻¹ * (E : Rat)⁻¹)) := by
    funext i
    show (p i - (E : Rat)⁻¹) * (p i - (E : Rat)⁻¹)
        = p i * p i + (-(2 * (E : Rat)⁻¹ * p i)) + ((E : Rat)⁻¹ * (E : Rat)⁻¹)
    have e1 : (p i - (E : Rat)⁻¹) * (p i - (E : Rat)⁻¹)
        = p i * p i - p i * (E : Rat)⁻¹ - (E : Rat)⁻¹ * p i + (E : Rat)⁻¹ * (E : Rat)⁻¹ := by
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.neg_mul,
        Rat.mul_comm, Rat.mul_assoc]
    rw [e1]
    grind [Rat.mul_comm, Rat.mul_assoc, Rat.sub_eq_add_neg]
  have hdev : vsum (fun i => (p i - (E : Rat)⁻¹) * (p i - (E : Rat)⁻¹))
      = vsum (fun i => p i * p i) - 2 * (E : Rat)⁻¹ * vsum p
        + (E : Rat) * ((E : Rat)⁻¹ * (E : Rat)⁻¹) := by
    rw [hpt, vsum_add, vsum_add]
    show vsum (fun i => p i * p i) + vsum (fun i => -(2 * (E : Rat)⁻¹ * p i))
        + vsum (fun _ => (E : Rat)⁻¹ * (E : Rat)⁻¹)
        = vsum (fun i => p i * p i) - 2 * (E : Rat)⁻¹ * vsum p
          + (E : Rat) * ((E : Rat)⁻¹ * (E : Rat)⁻¹)
    have hneg : (fun i : Fin E => -(2 * (E : Rat)⁻¹ * p i))
        = (fun i => (-1 : Rat) * (2 * (E : Rat)⁻¹ * p i)) := by
      funext i; grind
    rw [hneg, vsum_smul, vsum_smul, vsum_const]
    push_cast
    have hn1 : (-1 : Rat) * (2 * (E : Rat)⁻¹ * vsum p)
        = -(2 * (E : Rat)⁻¹ * vsum p) := by
      rw [Rat.neg_mul (a := (1 : Rat))]
      grind
    rw [hn1]
    grind [Rat.sub_eq_add_neg, Rat.mul_comm, Rat.mul_assoc]
  have hnon : 0 ≤ vsum (fun i => (p i - (E : Rat)⁻¹) * (p i - (E : Rat)⁻¹)) :=
    vsum_nonneg _ _ fun i => sq_nonneg _
  rw [hdev, hsum, hsq] at hnon
  grind

/-- The uniform router attains the floor: every expert gets `1/E`, and `Σᵢ (1/E)² = 1/E`. -/
theorem balance_eq {E : Nat} (hE : 0 < E) :
    vsum (fun _ : Fin E => (E : Rat)⁻¹ * (E : Rat)⁻¹) = (E : Rat)⁻¹ := by
  rw [vsum_const]
  have hsq : (E : Rat) * ((E : Rat)⁻¹ * (E : Rat)⁻¹) = (E : Rat)⁻¹ := by
    rw [← Rat.mul_assoc, Rat.mul_inv_cancel (a := (E : Rat))]
    · grind
    · norm_cast; omega
  exact hsq

/-- A collapsed router (one expert takes everything): it is a probability vector whose
collision probability equals `1` — exactly `E` times the `1/E` floor. -/
def oneAt0 {E : Nat} : Fin E → Rat := fun i => if i.val = 0 then 1 else 0

theorem headZero {E : Nat} (hz : 0 < E) : @oneAt0 E ⟨0, hz⟩ = 1 := by
  show (if (⟨0, hz⟩ : Fin E).val = 0 then (1 : Rat) else (0 : Rat)) = 1
  simp

theorem tailZero {E : Nat} : (fun i : Fin E => @oneAt0 (E + 1) i.succ)
    = (fun _ => (0 : Rat)) := by
  funext i
  show (if (⟨i.val + 1, by omega⟩ : Fin (E + 2)).val = 0 then (1 : Rat) else (0 : Rat))
      = (0 : Rat)
  simp

theorem vsum_oneAt0 : ∀ (E : Nat), vsum (@oneAt0 (E + 1)) = 1
  | 0 => by
      rw [vsum, tailZero, vsum_zero]
      show (1 : Rat) + 0 = 1
      grind
  | E + 1 => by
      rw [vsum, tailZero, vsum_zero]
      show @oneAt0 (E + 2) ⟨0, Nat.succ_pos (E + 1)⟩ + 0 = 1
      rw [headZero (Nat.succ_pos (E + 1))]
      grind

theorem squareOneAt0 {E : Nat} : (fun i => @oneAt0 E i * @oneAt0 E i) = @oneAt0 E := by
  funext i
  show (if i.val = 0 then (1 : Rat) else 0) * (if i.val = 0 then (1 : Rat) else 0)
      = (if i.val = 0 then (1 : Rat) else 0)
  grind

/-- A collapsed router pays exactly `E` times the floor. -/
theorem balance_collapse {E : Nat} (hE : 0 < E) :
    vsum (@oneAt0 E) = 1 ∧
      vsum (fun i => @oneAt0 E i * @oneAt0 E i) = 1 := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hE)
  subst ha
  rw [squareOneAt0]
  exact ⟨vsum_oneAt0 a, vsum_oneAt0 a⟩

-- ANCHOR_END: balance

-- ANCHOR: routing
/-- A full router matrix: `w i k` is expert `i`'s weight on token `k`, normalised per token.
The fraction of tokens routed to expert `i` is `f i = (1/B) Σ_k w i k`. -/
def frac {E B : Nat} (w : Fin E → Fin B → Rat) (i : Fin E) : Rat :=
  (B : Rat)⁻¹ * vsum (fun k => w i k)

/-- The fractions sum to 1: per-token normalisation + exchanging the two finite sums
(`vsum_comm`) gives `Σᵢ fᵢ = (1/B) Σ_k 1 = 1`. -/
theorem frac_sum {E B : Nat} (hB : 0 < B) (w : Fin E → Fin B → Rat)
    (hw : ∀ k, vsum (fun i => w i k) = 1) : vsum (fun i => frac w i) = 1 := by
  unfold frac
  rw [vsum_smul]
  rw [show (fun i => vsum (fun k => w i k)) = (fun i => vsum (w i)) from rfl]
  rw [vsum_comm]
  rw [show (fun k => vsum (fun i => w i k)) = (fun k => (1 : Rat)) from by
        funext k; exact hw k]
  rw [vsum_const]
  push_cast
  rw [show (B : Rat) * 1 = (B : Rat) from Rat.mul_one (B : Rat)]
  rw [Rat.mul_comm]
  exact Rat.mul_inv_cancel (a := (B : Rat)) (by norm_cast; omega)

/-- **The load-balancing loss is at least 1 — for ANY router.** Real MoE training adds an
auxiliary loss `E · Σᵢ fᵢ²` (fraction of tokens per expert, times the expert count). The
`balance_ge` floor applies to `f` once `frac_sum` puts it in the theorem's hypotheses:
no routing strategy, however degenerate or token-dependent, escapes the floor. -/
theorem balancing_ge {E B : Nat} (hE : 0 < E) (hB : 0 < B) (w : Fin E → Fin B → Rat)
    (hw : ∀ k, vsum (fun i => w i k) = 1) :
    (1 : Rat) ≤ (E : Rat) * vsum (fun i => frac w i * frac w i) := by
  have hf := frac_sum hB w hw
  have h := balance_ge hE (fun i => frac w i) hf
  have hE0 : 0 ≤ (E : Rat) := by norm_cast; omega
  have hmul := Rat.mul_le_mul_of_nonneg_left h hE0
  rw [show (E : Rat) * (E : Rat)⁻¹ = 1 from
    Rat.mul_inv_cancel (a := (E : Rat)) (by norm_cast; omega)] at hmul
  exact hmul
-- ANCHOR_END: routing
end MixtureOfExperts

section Distillation
variable [LawfulLog]

/-- **Distillation is bounded below by the teacher's entropy.** The distillation loss is
`CE(t, s)` — cross-entropy between the teacher distribution `t` and the student `s`
(KD soft targets; temperature just rescales logits, Chapter 9). By the decomposition
`CE = H + KL` and Gibbs' inequality, no student, of any architecture and any capacity, can push the distillation loss below `H(t)`, and reaching `H(t)` forces `s = t`. -/
-- ANCHOR: distill
theorem distill_ge_entropy {n : Nat} (t s : Dist n) :
    t.entropy ≤ t.crossEntropy s := by
  have h := Dist.crossEntropy_eq_entropy_add_kl t s
  have hkl := Dist.kl_nonneg t s
  grind

/-- A perfect student (the teacher itself) attains the floor exactly: `CE(t, t) = H(t)`. -/
theorem distill_teacher (t : Dist n) : t.crossEntropy t = t.entropy := by
  have h := Dist.crossEntropy_eq_entropy_add_kl t t
  rw [Dist.kl_self] at h
  grind

-- ANCHOR_END: distill
end Distillation

section Scaling

/-- `1/a ≥ 1/b` when `0 < a < b`: inverse cost per unit of budget. -/
theorem inv_antitone {a b : Rat} (ha : 0 < a) (hab : a < b) : b⁻¹ < a⁻¹ := by
  have hb : 0 < b := by grind
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  have h1 : b⁻¹ * (a * b) = a := by
    rw [show b⁻¹ * (a * b) = b⁻¹ * (b * a) from by grind [Rat.mul_comm],
      ← Rat.mul_assoc, Rat.inv_mul_cancel b (Rat.ne_of_gt hb), Rat.one_mul]
  have h2 : a⁻¹ * (a * b) = b := by
    rw [show a⁻¹ * (a * b) = (a⁻¹ * a) * b from by grind [Rat.mul_assoc],
      Rat.inv_mul_cancel a (Rat.ne_of_gt ha), Rat.one_mul]
  have h3 : b⁻¹ * (a * b) < a⁻¹ * (a * b) := by rw [h1, h2]; exact hab
  exact Rat.lt_of_mul_lt_mul_right h3 (Rat.le_of_lt hprod)

/-- **The data scaling law is strictly decreasing.** With loss model `L(N) = Linf + C/N`
(a power law with exponent 1, the empirical form of Kaplan et al. with `Linf` as the
irreducible term), doubling the dataset `N` strictly lowers the loss — and by exactly
`C/N − C/2N = C/2N`. -/
-- ANCHOR: scaling
theorem data_scale (C : Rat) (hC : 0 < C) (N N' : Rat) (hN : 0 < N) (hNN : N < N') :
    C / N' < C / N := by
  show C * N'⁻¹ < C * N⁻¹
  exact Rat.mul_lt_mul_of_pos_left (inv_antitone hN hNN) hC

/-- Concretely: doubling the budget halves the excess loss `C/N`. -/
theorem data_scale_double (C N : Rat) (_hC : 0 < C) (hN : 0 < N) :
    C / (2 * N) = (1 / 2 : Rat) * (C / N) := by
  show C * (2 * N)⁻¹ = (1 / 2 : Rat) * (C * N⁻¹)
  have h2 : (2 : Rat) ≠ 0 := by grind
  have hN' : N ≠ 0 := Rat.ne_of_gt hN
  have hprod : (2 * N) * ((2 : Rat)⁻¹ * N⁻¹) = 1 := by
    rw [show (2 * N) * ((2 : Rat)⁻¹ * N⁻¹) = (2 * (2 : Rat)⁻¹) * (N * N⁻¹) from by
      grind [Rat.mul_assoc, Rat.mul_comm]]
    rw [Rat.mul_inv_cancel (a := (2 : Rat)) h2, Rat.mul_inv_cancel (a := N) hN']
    grind
  rw [Rat.inv_eq_of_mul_eq_one hprod]
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- **Optimization decay**: the excess loss after `t` gradient steps of a contraction
`0 ≤ c ≤ 1` is `cᵗ · (L₀ − Linf)` — exponential in `t` (this is the `powN_le_one`
machinery of Chapter 5, read as a scaling curve: training loss improves geometrically
with steps, which is why data scaling (power law) and step scaling (exponential) buy
very different amounts). -/
theorem train_decay (c L₀ Linf : Rat) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hL : Linf ≤ L₀) :
    ∀ t : Nat, 0 ≤ Ch05.powN c t * (L₀ - Linf) ∧ Ch05.powN c t * (L₀ - Linf) ≤ L₀ - Linf := by
  intro t
  have hp : Ch05.powN c t ≤ 1 := (Ch05.powN_le_one c hc0 hc1 t).1
  have hp0 : 0 ≤ Ch05.powN c t := (Ch05.powN_le_one c hc0 hc1 t).2
  have hd : 0 ≤ L₀ - Linf := by grind
  refine ⟨Rat.mul_nonneg hp0 hd, ?_⟩
  have h2 := Rat.mul_le_mul_of_nonneg_right hp hd
  rw [Rat.one_mul] at h2
  exact h2

-- ANCHOR_END: scaling
end Scaling

end LeanDL.Ch18
