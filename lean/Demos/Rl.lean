import LeanDL.Ch13.Model
import LeanDL.Ch05.Optim

open LeanDL LeanDL.Ch04 LeanDL.Ch05 LeanDL.Ch13

/-- One episode under a policy `pick`: the list of `(state, action, discounted return from there)`,
whether the goal was reached, and the number of steps. -/
def rollout (pick : Nat → Rng → Nat × Rng) (r : Rng) :
    List (Nat × Nat × Float) × Bool × Nat × Rng := Id.run do
  let mut s := 1
  let mut rng := r
  let mut trace : List (Nat × Nat × Float) := []   -- (s, a, reward), newest first
  let mut reached := false
  let mut n := 0
  for _ in [0:maxLen] do
    let (a, r2) := pick s rng
    rng := r2
    let (s', rew, done) := envStep s a
    trace := (s, a, rew) :: trace
    n := n + 1
    s := s'
    if done then
      reached := rew > 0.0
      break
  -- walking back from the end gives the discounted returns
  let mut g := 0.0
  let mut out : List (Nat × Nat × Float) := []
  for (st, a, rew) in trace do
    g := rew + gamma * g
    out := (st, a, g) :: out
  return (out, reached, n, rng)

def sampler (p : Array Float) : Nat → Rng → Nat × Rng := fun s r =>
  let (u, r2) := r.uniform
  ((if u < probRight p s then 1 else 0), r2)

def evalPolicy (pick : Nat → Rng → Nat × Rng) : Float × Float := Id.run do
  let mut wins := 0
  let mut len := 0
  let mut r := Rng.seed 4242
  for _ in [0:1000] do
    let (_, reached, n, r2) := rollout pick r
    r := r2
    if reached then wins := wins + 1
    len := len + n
  return (wins.toFloat / 1000.0, len.toFloat / 1000.0)

def reinforce (iters : Nat) : IO (Array Float) := do
  let (p0, _) := (Rng.seed 8).uniformArray PR 0.5
  let mut p := p0
  let mut st : AdamState Float := AdamState.init PR
  let mut rng := Rng.seed 31
  for it in [0:iters] do
    let mut steps : List (Nat × Nat × Float) := []
    let mut total := 0.0
    let mut count := 0.0
    for _ in [0:16] do
      let (tr, _, _, r2) := rollout (sampler p) rng
      rng := r2
      for (_, _, g) in tr do
        total := total + g
        count := count + 1.0
      steps := tr ++ steps
    let baseline := total / count
    let g := (pgLoss steps baseline 16).backprop (vecOf p)
    let (p1, st') := adamStep 0.02 0.9 0.999 1e-8 st p g
    p := p1; st := st'
    if it % 100 == 0 then
      let (w, l) := evalPolicy (sampler p)
      IO.println s!"  iter {it}: goal rate {w}, mean length {l}"
  return p

def qlearning (episodes : Nat) : Array Float := Id.run do
  let mut q := Array.replicate 12 0.0   -- q[2s + a]
  let mut rng := Rng.seed 17
  for _ in [0:episodes] do
    let mut s := 1
    for _ in [0:maxLen] do
      let (u, r1) := rng.uniform
      let (v, r2) := r1.uniform
      rng := r2
      let greedy := if q[2 * s + 1]! >= q[2 * s]! then 1 else 0
      let a := if u < 0.2 then (if v < 0.5 then 0 else 1) else greedy
      let (s', rew, done) := envStep s a
      let best := if done then 0.0 else max q[2 * s' + 1]! q[2 * s']!
      let target := rew + gamma * best
      -- the TD update of Ch13/Rl.lean (`tdUpdate`), in Float
      q := q.set! (2 * s + a) (q[2 * s + a]! + 0.1 * (target - q[2 * s + a]!))
      s := s'
      if done then break
  return q

def main (args : List String) : IO Unit := do
  let iters := (args.getD 0 "400").toNat!
  let randomPick : Nat → Rng → Nat × Rng := fun _ r =>
    let (u, r2) := r.uniform
    ((if u < 0.5 then 1 else 0), r2)
  let (w0, l0) := evalPolicy randomPick
  IO.println s!"random policy: goal rate {w0} (theory 0.2), mean length {l0}"
  IO.println s!"REINFORCE with a baseline: {PR} parameters, {iters} iterations of 16 episodes"
  let p ← reinforce iters
  let (w, l) := evalPolicy (sampler p)
  IO.println s!"  final: goal rate {w}, mean length {l}; optimal length is 4"
  let q := qlearning 2000
  let greedy : Nat → Rng → Nat × Rng := fun s r => ((if q[2 * s + 1]! >= q[2 * s]! then 1 else 0), r)
  let (wq, lq) := evalPolicy greedy
  IO.println s!"Q-learning (2000 episodes, greedy policy): goal rate {wq}, mean length {lq}"
  IO.println s!"  Q(1, right) = {q[3]!}   exact optimum gamma^3 = {gamma * gamma * gamma}"
