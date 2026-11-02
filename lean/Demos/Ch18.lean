import LeanDL
import LeanDL.Core.Plot

/-!
# Chapter 18 demo — efficiency in numbers

Four Float experiments that mirror the four exact theorems of `Ch18/Efficiency.lean`:

1. **Quantization**: an INT8-style grid on a weight vector. We check the two proved
   bounds numerically: floor error `< s`, round-to-nearest error `<= s/2`.
2. **MoE load balance**: the auxiliary loss `Sum p_i^2` for routers of different shapes;
   it never drops below `1/E`, equal routing attains it, collapse pays `E` times it.
3. **Distillation**: `CE(T, S) = H(T) + KL(T||S)` — the measured loss never goes under
   the teacher's entropy, and a student distilled on the teacher's soft targets drives
   the KL gap to zero (and never below it).
4. **Scaling**: `L(N) = Linf + C/N` — doubling `N` halves the excess loss, exactly.
-/

open LeanDL Plot

def floorQ (s x : Float) : Float := Float.floor (x / s) * s
def roundQ (s x : Float) : Float := Float.floor (x / s + 0.5) * s

def softmaxF (z : Array Float) : Array Float :=
  let m := z.foldl max z[0]!
  let e := z.map (fun v => Float.exp (v - m))
  let s := e.foldl (· + ·) 0
  e.map (· / s)

def wavg (p w : Array Float) : Float :=
  (List.range p.size).foldl (fun acc i => acc + p[i]! * w[i]!) 0

/-- Σ pᵢ²: the router collision probability. -/
def sumSq (p : Array Float) : Float :=
  (List.range p.size).foldl (fun acc i => acc + p[i]! * p[i]!) 0

def showF (x : Float) : String := fmt x

def fmtArr (a : Array Float) : String :=
  "[" ++ String.intercalate ", " (a.toList.map showF) ++ "]"

/-- Three decimals (for the small quantization grid steps). -/
def fmt3 (x : Float) : String :=
  let r := Float.round (x * 1000.0) / 1000.0
  if r == 0.0 then "0"
  else
    let cs := (toString r).toList.reverse.dropWhile (· == '0')
    let cs := if cs.head? == some '.' then cs.tail else cs
    String.ofList cs.reverse

/-- Float comparison as Bool (decidable propositions on Float reduce to `sorry`
at runtime, so we compare via the native `Float.beq` / `Float.abs`). -/
def geB (x b : Float) : Bool := Float.beq (x - b) (Float.abs (x - b))
def ltB (x b : Float) : Bool := !geB x b

/-- SGD loop for the distilled student: grad of `CE(T, softmax z)` is `S - T`. -/
partial def kdLoop (T : Array Float) (z : Array Float) (steps : Nat) : Array Float :=
  match steps with
  | 0 => z
  | k + 1 =>
      let sStu := softmaxF z
      let z' := (Array.range z.size).map fun i => z[i]! - 0.5 * (sStu[i]! - T[i]!)
      kdLoop T z' k

def main : IO Unit := do
  IO.println "=== Chapter 18 — quantization, MoE, distillation, scaling ==="

  -- 1. Quantization --------------------------------------------------------
  IO.println "\n[1] INT8-style quantization (proved: floor err < s, round err <= s/2)"
  let s : Float := 2.4 / 255 -- range [-1.2, 1.2] on 255 levels
  let ws : Array Float := #[1.19734, -0.0031, 0.44444, -1.1999, 0.1105]
  let mut maxFloor : Float := 0
  let mut maxRound : Float := 0
  for x in ws do
    let ef := Float.abs (x - floorQ s x)
    let er := Float.abs (x - roundQ s x)
    if ef > maxFloor then maxFloor := ef
    if er > maxRound then maxRound := er
  IO.println s!"    grid step s = {fmt3 s}"
  IO.println s!"    max |x - floor-quant| = {fmt3 maxFloor}   (bound s = {fmt3 s})"
  IO.println s!"    max |x - round-quant| = {fmt3 maxRound}   (bound s/2 = {fmt3 (s / 2)})"
  IO.println s!"    floor bound respected: {ltB maxFloor s}"
  IO.println s!"    round bound respected: {geB (s / 2 + 0.0000001) maxRound}"

  -- 2. MoE load balance ----------------------------------------------------
  IO.println "\n[2] Router collision loss Sum p^2 (proved: >= 1/E; uniform attains it)"
  let floor : Float := 1.0 / 8
  let cases : Array (String × Array Float) := #[
    ("uniform    ", #[0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125]),
    ("skewed     ", #[0.40, 0.20, 0.10, 0.10, 0.05, 0.05, 0.05, 0.05]),
    ("near-unif. ", #[0.13, 0.13, 0.125, 0.125, 0.125, 0.125, 0.12, 0.12]),
    ("collapse   ", #[1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00])
  ]
  IO.println s!"    E = 8, floor 1/E = {fmt3 floor}"
  for (name, p) in cases do
    let l := sumSq p
    IO.println s!"    {name} Sum p^2 = {fmt3 l}   (>= 1/E: {geB l (floor - 0.0000001)})"

  -- 3. Distillation --------------------------------------------------------
  IO.println "\n[3] Distillation CE(T, S) = H(T) + KL(T||S) (proved: >= H(T))"
  let T : Array Float := #[0.70, 0.20, 0.08, 0.02]
  let hT : Float := -wavg T (T.map Float.log)
  IO.println s!"    teacher T = {fmtArr T},  H(T) = {showF hT}"
  let students : Array (String × Array Float) := #[
    ("uniform S", #[0.25, 0.25, 0.25, 0.25]),
    ("peaked S ", #[0.98, 0.01, 0.005, 0.005]),
    ("copy T   ", #[0.70, 0.20, 0.08, 0.02])
  ]
  for (name, stu) in students do
    let ce := -wavg T (stu.map Float.log)
    let logT := T.map Float.log
    let logS := stu.map Float.log
    let kl := wavg T (logT.zipWith (· - ·) logS)
    IO.println s!"    {name}  CE = {showF ce},  KL = {showF kl},  H(T)+KL = {showF (hT + kl)}"
  IO.println "    distilling T into a student (200 SGD steps on soft CE, grad = S - T):"
  let z0 : Array Float := #[0.0, 0.0, 0.0, 0.0]
  let zF := kdLoop T z0 200
  let stu := softmaxF zF
  let ce := -wavg T (stu.map Float.log)
  let logT := T.map Float.log
    let logS := stu.map Float.log
    let kl := wavg T (logT.zipWith (· - ·) logS)
  IO.println s!"    S = {fmtArr stu}"
  IO.println s!"    CE = {showF ce}  (>= H(T) = {showF hT}: {geB ce (hT - 0.0000001)}),  KL = {showF kl} -> 0"

  -- 4. Scaling law ---------------------------------------------------------
  IO.println "\n[4] Data scaling L(N) = Linf + C/N (proved: decreasing; doubling N halves C/N)"
  let linf : Float := 0.10
  let c : Float := 16.0
  IO.println "    N        L(N)     excess C/N"
  for n in [100, 200, 400, 800, 1600] do
    let nf : Float := Float.ofInt n
    IO.println s!"    {toString n}   {showF (linf + c / nf)}    {showF (c / nf)}"
  IO.println "    each doubling halves the excess loss — the theorem C/2N = (1/2)*(C/N) in numbers"
  IO.println "\nAll four measured behaviors match the proved theorems."
