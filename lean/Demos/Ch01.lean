import LeanDL.Ch01.Neuron

open LeanDL LeanDL.Ch01

def main : IO Unit := do
  let x : Vec Float 2 := v2 0.5 (-1.0)
  let n : Neuron Float 2 := ⟨v2 2.0 1.0, 0.25⟩
  IO.println s!"preact  = {n.preact x}"
  IO.println s!"step    = {n.fire step x}"
  IO.println s!"sigmoid = {n.fire sigmoid x}"
  IO.println s!"relu    = {n.fire relu x}"
  IO.println s!"tanh    = {n.fire tanh x}"
