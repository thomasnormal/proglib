/-
Examples/system-verilog/sem2/xnor_sgn_wide — admitted signed widening conversion.
The source-shaped signed operands are widened before the XNOR operation.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.xnor_sgn_wide.agree

open LeanModels.Sv

load_design_sv2 xnorWide from "Examples/system-verilog/sem2/xnor_sgn_wide/xnor_sgn_wide.sv.json"

#guard !(xnorWide.sem 4).hasUnsupported
#guard match (xnorWide.sem 4).processes.toList with
  | [.assign (.ident "w") (.unary .bnot (.binary .xor (.resizeSigned 8 (.ident "ua")) (.resizeSigned 8 (.ident "ub"))))] => true
  | _ => false

end Examples.«system-verilog».sem2.xnor_sgn_wide.agree
