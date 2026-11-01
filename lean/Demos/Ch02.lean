import LeanDL.Ch02.Train

open LeanDL LeanDL.Ch02

private def pts (f : Bool → Bool → Bool) : List (Example Float 3) :=
  [(false, false), (false, true), (true, false), (true, true)].map fun (a, b) =>
    (v3 1.0 (bit a) (bit b), if f a b then 1.0 else -1.0)

def main : IO Unit := do
  for (name, f) in [("AND", fun a b => a && b), ("OR", fun a b => a || b),
                    ("XOR", fun a b => a ^^ b)] do
    let (_, log) := train (pts f) 50 Vec.zero []
    IO.println s!"{name}: mistakes per epoch = {log}"
