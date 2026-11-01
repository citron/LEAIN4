import LeanDL.Ch03.Mlp

/-!
# Chapter 3, part 2 — Every Boolean function is a one-hidden-layer network

For each input pattern `c` on which `f` is true we create one hidden neuron that fires
exactly on `c`; the output neuron is an OR of the hidden neurons. Everything is over `Int`
with the step activation, and proved for every number of inputs `n`.
-/

namespace LeanDL.Ch03

open LeanDL.Ch01

-- Equality of Boolean patterns is only needed classically in the proofs below.
attribute [local instance] Classical.propDecidable

-- ANCHOR: detector_def
/-- Number of `true` entries. -/
def ones : {n : Nat} → (Fin n → Bool) → Int
  | 0, _ => 0
  | _ + 1, c => b2i (c 0) + ones (fun i => c i.succ)

/-- Weights `+1` where the pattern `c` is true and `-1` elsewhere. -/
def sgn {n : Nat} (c : Fin n → Bool) : Vec Int n := fun i => if c i then 1 else -1

/-- A Boolean input seen as a 0/1 vector. -/
def inVec {n : Nat} (x : Fin n → Bool) : Vec Int n := fun i => b2i (x i)
-- ANCHOR_END: detector_def

theorem eq_iff_cons {n : Nat} (x c : Fin (n + 1) → Bool) :
    x = c ↔ x 0 = c 0 ∧ (fun i : Fin n => x i.succ) = (fun i : Fin n => c i.succ) := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ j => exact congrFun h1 j

theorem head_spec (cb xb : Bool) :
    (if cb then (1 : Int) else -1) * b2i xb - b2i cb ≤ 0 ∧
      ((if cb then (1 : Int) else -1) * b2i xb - b2i cb = 0 ↔ xb = cb) := by
  cases cb <;> cases xb <;> simp [b2i]

-- ANCHOR: detector_spec
/-- `w·x - k ≤ 0` for every 0/1 input, with equality exactly when `x = c`. -/
theorem detector_spec : ∀ {n : Nat} (c x : Fin n → Bool),
    Vec.dot (sgn c) (inVec x) - ones c ≤ 0 ∧
      (Vec.dot (sgn c) (inVec x) - ones c = 0 ↔ x = c)
  | 0, c, x => by
    simp only [Vec.dot, ones]
    exact ⟨by omega, ⟨fun _ => funext fun i => i.elim0, fun _ => by omega⟩⟩
  | n + 1, c, x => by
    have ih := detector_spec (fun i => c i.succ) (fun i => x i.succ)
    have hd : Vec.dot (sgn c) (inVec x) =
        (if c 0 then (1 : Int) else -1) * b2i (x 0) +
          Vec.dot (sgn fun i => c i.succ) (inVec fun i => x i.succ) := rfl
    have ho : ones c = b2i (c 0) + ones (fun i => c i.succ) := rfl
    have hh := head_spec (c 0) (x 0)
    rw [hd, ho, eq_iff_cons]
    grind
-- ANCHOR_END: detector_spec

-- ANCHOR: net
/-- One hidden neuron per pattern in `L`; the output neuron fires when at least one fires. -/
def buildNet {n : Nat} (L : List (Fin n → Bool)) : MLP Int n 1 :=
  .cons (h := L.length)
    ⟨fun i => sgn (L.get i), fun i => -ones (L.get i)⟩
    (.last ⟨fun _ _ => 1, fun _ => -1⟩)
-- ANCHOR_END: net

theorem step_int (p : Int) : step p = if 0 ≤ p then (1 : Int) else 0 := rfl

theorem hidden_eq {n : Nat} (c x : Fin n → Bool) :
    step (Vec.dot (sgn c) (inVec x) + -ones c) = if x = c then (1 : Int) else 0 := by
  have h := detector_spec c x
  rw [step_int]
  by_cases hx : x = c <;> simp [hx] <;> grind

theorem dot_ones_list {n : Nat} (g : (Fin n → Bool) → Int) :
    ∀ L : List (Fin n → Bool),
      Vec.dot (fun _ => (1 : Int)) (fun i : Fin L.length => g (L.get i)) = (L.map g).sum
  | [] => rfl
  | a :: l => by
    have ih := dot_ones_list g l
    have : Vec.dot (fun _ => (1 : Int)) (fun i : Fin (a :: l).length => g ((a :: l).get i)) =
        1 * g a + Vec.dot (fun _ => (1 : Int)) (fun i : Fin l.length => g (l.get i)) := rfl
    rw [this, ih]
    simp

theorem sum_01 {n : Nat} (g : (Fin n → Bool) → Int) (hg : ∀ c, g c = 0 ∨ g c = 1) :
    ∀ L : List (Fin n → Bool),
      0 ≤ (L.map g).sum ∧ ((∃ c ∈ L, g c = 1) ↔ 1 ≤ (L.map g).sum)
  | [] => by simp
  | a :: l => by
    have ih := sum_01 g hg l
    have ha := hg a
    simp only [List.map_cons, List.sum_cons, List.mem_cons, exists_eq_or_imp]
    grind

-- ANCHOR: net_correct
/-- If `L` lists exactly the inputs on which `f` is true, the network computes `f`. -/
theorem buildNet_correct {n : Nat} (f : (Fin n → Bool) → Bool) (L : List (Fin n → Bool))
    (hL : ∀ c, c ∈ L ↔ f c = true) (x : Fin n → Bool) :
    (buildNet L).forward step step (inVec x) 0 = b2i (f x) := by
  let g : (Fin n → Bool) → Int := fun c => if x = c then 1 else 0
  have hg : ∀ c, g c = 0 ∨ g c = 1 := fun c => by simp only [g]; split <;> simp
  have hs := sum_01 g hg L
  have hfwd : (buildNet L).forward step step (inVec x) 0 =
      step (Vec.dot (fun _ => (1 : Int)) (fun i : Fin L.length => g (L.get i)) + -1) := by
    show step (Vec.dot (fun _ => (1 : Int)) (fun i : Fin L.length =>
        step (Vec.dot (sgn (L.get i)) (inVec x) + -ones (L.get i))) + -1) = _
    simp only [hidden_eq]
    rfl
  rw [hfwd, dot_ones_list g L, step_int]
  have hmem : (∃ c ∈ L, g c = 1) ↔ f x = true := by
    rw [← hL x]
    constructor
    · rintro ⟨c, hc, hgc⟩
      have : x = c := by simp only [g] at hgc; split at hgc <;> simp_all
      exact this ▸ hc
    · intro hx; exact ⟨x, hx, by simp [g]⟩
  cases hf : f x <;> simp [hf, b2i] at hmem ⊢ <;> grind
-- ANCHOR_END: net_correct

/-- All `2^n` Boolean inputs. -/
def allAssign : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => i.elim0]
  | n + 1 => (allAssign n).flatMap fun c =>
      [fun i => Fin.cases (motive := fun _ => Bool) false c i,
       fun i => Fin.cases (motive := fun _ => Bool) true c i]

theorem mem_allAssign : ∀ (n : Nat) (x : Fin n → Bool), x ∈ allAssign n
  | 0, x => by simp [allAssign]; funext i; exact i.elim0
  | n + 1, x => by
    have ih := mem_allAssign n (fun i => x i.succ)
    simp only [allAssign, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨fun i => x i.succ, ih, ?_⟩
    cases h : x 0
    · left; funext i; cases i using Fin.cases with
      | zero => simpa using h
      | succ j => simp
    · right; funext i; cases i using Fin.cases with
      | zero => simpa using h
      | succ j => simp

-- ANCHOR: universal
/-- **Boolean universality.** Every Boolean function of `n` inputs is computed by a
network with one hidden layer of step neurons. -/
theorem universal {n : Nat} (f : (Fin n → Bool) → Bool) :
    ∃ net : MLP Int n 1, ∀ x, net.forward step step (inVec x) 0 = b2i (f x) :=
  ⟨buildNet ((allAssign n).filter f), fun x =>
    buildNet_correct f _ (fun c => by simp [List.mem_filter, mem_allAssign]) x⟩
-- ANCHOR_END: universal

end LeanDL.Ch03
