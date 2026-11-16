import Examples.«system-verilog».sem2.generated_array_nested_canonical_e.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.generated_array_nested_canonical_e

def printRows (w : Nat) (rows : List String) : IO Unit := do
  for (row, i) in rows.zipIdx do
    IO.println s!"ROW W={w} i={i} y={row}"

def main : IO Unit := do
  for (w, stimulus) in [(4, stimuli4), (8, stimuli8)] do
    match outputs w stimulus with
    | .ok rows => printRows w rows
    | .timeout => throw (IO.userError s!"E timed out at W={w}")
    | .unsupported msg => throw (IO.userError s!"E refusal at W={w}: {msg}")
