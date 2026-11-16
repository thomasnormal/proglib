import Examples.«system-verilog».sem2.generated_array_nested_canonical_e.agree

open LeanModels.Sv
open Examples.«system-verilog».sem2.generated_array_nested_canonical_e

def main : IO Unit := do
  for w in [4, 8] do
    match generatedArrayNestedCanonicalE.e w with
    | .unsupported msg => IO.println s!"E REFUSAL W={w}: {msg}"
    | .timeout => throw (IO.userError s!"E timed out at W={w}")
    | .ok _ => throw (IO.userError s!"E unexpectedly admitted W={w}")
