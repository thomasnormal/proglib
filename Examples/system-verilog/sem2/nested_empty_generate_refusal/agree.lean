/-
Canonical-E receipt for a nested generate loop whose first outer iteration has
an empty inner range, under IEEE 1800-2023 §27.4. The source-shaped template
is retained for later iterations instead of being copied into the empty one.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.nested_empty_generate_refusal.agree

open LeanModels.Sv

load_design_sv2 nestedEmptyGenerateRefusal
  from "Examples/system-verilog/sem2/nested_empty_generate_refusal/nested_empty_generate_refusal.sv.json"

#guard match nestedEmptyGenerateRefusal.pdesign.generates with
  | [.genFor (some "outer") "j" _ _ _ (some 2)
      [.genFor (some "inner") "k" _ _ _ (some 1)
        [.process (.assignL (.bitSel "y" (.genvarRef "j")) (.lit _))]]] => true
  | _ => false

private def flat : Design2 := nestedEmptyGenerateRefusal.pdesign.instantiateD2 [2]

#guard match flat.processes.toList with
  | [.unsupported "AssignL" "assignment target 'y' undeclared",
      .unsupported "PortSymbol:net-z" "y"] => true
  | _ => false

end Examples.«system-verilog».sem2.nested_empty_generate_refusal.agree
