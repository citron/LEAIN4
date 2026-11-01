import LeanDL.Ch14.Model
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch14

def rms (v : Array Float) : Float := Float.sqrt (v.foldl (fun s x => s + x * x) 0.0 / v.size.toFloat)

/-- Cost of a controller over `h` steps from `(x0, 0)`, in the real world or in the dream. -/
def episodeCost (p? : Option (Array Float)) (w : Array Float) (x0 : Float) (h : Nat) : Float := Id.run do
  let mut x := x0
  let mut v := 0.0
  let mut c := 0.0
  for _ in [0:h] do
    let u := policy w x v
    c := c + stepCost x v u
    let (x', v') := match p? with
      | some p => dream p x v u
      | none => envStep x v u
    x := x'
    v := v'
  return c

def meanCost (p? : Option (Array Float)) (w : Array Float) (starts : Array Float) (h : Nat) : Float :=
  (starts.foldl (fun s x0 => s + episodeCost p? w x0 h) 0.0) / starts.size.toFloat

/-- Evolution strategy with antithetic sampling and standardised fitness (the optimiser used in the
original World Models paper was CMA-ES, a close cousin). The cost is evaluated in `p?`. -/
def evolve (p? : Option (Array Float)) (gens : Nat) (seed : Nat) : Array Float := Id.run do
  let mut w := #[0.0, 0.0, 0.0]
  let mut rng := Rng.seed seed.toUInt64
  let sigma := 0.3
  for _ in [0:gens] do
    let mut starts : Array Float := #[]
    for _ in [0:6] do
      let (u, r) := rng.uniform
      rng := r
      starts := starts.push (3.0 * u - 1.5)
    let mut eps : Array (Array Float) := #[]
    for _ in [0:16] do
      let mut e : Array Float := #[]
      for _ in [0:3] do
        let (g, r) := rng.normal
        rng := r
        e := e.push g
      eps := eps.push e
    let mut cands : Array (Array Float) := #[]
    for e in eps do
      cands := cands.push (Array.zipWith (fun a b => a + sigma * b) w e)
      cands := cands.push (Array.zipWith (fun a b => a - sigma * b) w e)
    let costs := cands.map fun c => meanCost p? c starts 25
    let m := costs.foldl (· + ·) 0.0 / costs.size.toFloat
    let sd := Float.sqrt (costs.foldl (fun s c => s + (c - m) * (c - m)) 0.0 / costs.size.toFloat) + 1e-8
    let mut grad := #[0.0, 0.0, 0.0]
    for i in [0:eps.size] do
      let fPlus := -(costs[2 * i]! - m) / sd
      let fMinus := -(costs[2 * i + 1]! - m) / sd
      let e := eps[i]!
      grad := Array.zipWith (fun g x => g + (fPlus - fMinus) * x) grad e
    w := Array.zipWith (fun a g => a + 0.3 * g / (2.0 * eps.size.toFloat)) w grad
  return w

def main (args : List String) : IO Unit := do
  let steps := (args.getD 0 "4000").toNat!
  let gens := (args.getD 1 "80").toNat!
  -- 1. Collect experience with random actions.
  let mut data : Array (Float × Float × Float × Float × Float) := #[]
  let mut rng := Rng.seed 3
  for _ in [0:100] do
    let (a, r1) := rng.uniform
    let (b, r2) := r1.uniform
    rng := r2
    let mut x := 3.0 * a - 1.5
    let mut v := 2.0 * b - 1.0
    for _ in [0:25] do
      let (c, r3) := rng.uniform
      rng := r3
      let u := 2.0 * c - 1.0
      let (x', v') := envStep x v u
      data := data.push (x, v, u, 10.0 * (x' - x), 10.0 * (v' - v))
      x := x'; v := v'
  let nTrain := 2000
  let train := data.extract 0 nTrain
  let test := data.extract nTrain data.size
  IO.println s!"collected {data.size} transitions with random actions ({nTrain} train, {test.size} test)"
  -- 2. Train the world model.
  let (p0, _) := (Rng.seed 9).uniformArray PW 0.5
  let mut p := p0
  let mut st : AdamState Float := AdamState.init PW
  let mut r := Rng.seed 10
  for step in [0:steps] do
    let mut batch : List (Float × Float × Float × Float × Float) := []
    for _ in [0:64] do
      let (u, r2) := r.uniform
      r := r2
      batch := train[min (nTrain - 1) (Float.floor (u * nTrain.toFloat)).toUInt64.toNat]! :: batch
    let loss := dynLoss batch
    let (p1, st') := adamStep 0.005 0.9 0.999 1e-8 st p (loss.backprop (vecOf p))
    p := p1; st := st'
    if step % 1000 == 0 then IO.println s!"  step {step}: model loss {loss.eval (vecOf p)}"
  let errs := test.map fun (x, v, u, dx, _) =>
    let (x', _) := dream p x v u
    (x' - x - dx / 10.0)
  let verrs := test.map fun (x, v, u, _, dv) =>
    let (_, v') := dream p x v u
    (v' - v - dv / 10.0)
  IO.println s!"one-step RMSE on held-out transitions: position {rms errs}, velocity {rms verrs}"
  -- 3. Open-loop drift: imagined against real, same random actions.
  let mut drift : Array (Array Float) := Array.replicate 41 #[]
  let mut r4 := Rng.seed 55
  for _ in [0:200] do
    let (a, s1) := r4.uniform
    r4 := s1
    let mut xt := 3.0 * a - 1.5
    let mut vt := 0.0
    let mut xm := xt
    let mut vm := vt
    for k in [1:41] do
      let (c, s2) := r4.uniform
      r4 := s2
      let u := 2.0 * c - 1.0
      let (a1, b1) := envStep xt vt u
      let (a2, b2) := dream p xm vm u
      xt := a1; vt := b1; xm := a2; vm := b2
      drift := drift.modify k (·.push (xm - xt))
  IO.println "open-loop position error (RMS over 200 rollouts) after k steps:"
  for k in [1, 5, 10, 20, 40] do
    IO.println s!"  k = {k}: {rms drift[k]!}"
  -- 4. Train the controller inside the dream, and, for reference, in the real world.
  let starts := (Array.range 100).map fun i => -1.5 + 3.0 * i.toFloat / 99.0
  let wDream := evolve (some p) gens 1
  let wReal := evolve none gens 1
  IO.println s!"controller trained only in the dream ({gens} generations): w = {wDream}"
  IO.println s!"  cost in the dream: {meanCost (some p) wDream starts 40}   cost in the real world: {meanCost none wDream starts 40}"
  IO.println s!"controller trained directly in the real world: w = {wReal}"
  IO.println s!"  cost in the real world: {meanCost none wReal starts 40}"
  IO.println s!"no control (u = 0): cost in the real world: {meanCost none #[0.0, 0.0, 0.0] starts 40}"
