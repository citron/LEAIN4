import LeanDL.Ch03.Train

open LeanDL LeanDL.Ch01 LeanDL.Ch03

def xorData : List (Array Float × Float) :=
  [(#[0, 0], 0), (#[0, 1], 1), (#[1, 0], 1), (#[1, 1], 0)]

def init : Net2A Float :=
  { W1 := #[#[0.5, -0.4], #[-0.6, 0.7], #[0.3, 0.8]]
    b1 := #[0.1, -0.1, 0.0]
    w2 := #[0.6, -0.5, 0.4]
    b2 := 0.0 }

def main : IO Unit := do
  let mut net := init
  for round in [0:6] do
    let loss := xorData.foldl (fun s (xy : Array Float × Float) =>
      let e := net.predict xy.1 - xy.2
      s + 0.5 * e * e) 0.0
    IO.println s!"after {round * 2000} epochs: loss = {loss}"
    net := Net2A.fit 1.0 xorData 2000 net
  let spec : Net2 Float 2 3 := net.toNet2
  for (x, y) in xorData do
    let xv : Vec Float 2 := fun i => x[i.val]!
    IO.println s!"x = ({x[0]!}, {x[1]!})  target = {y}  prediction = {net.predict x}  (Vec spec: {spec.predict xv})"
