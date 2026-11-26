import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.untyped_width_repair.agree

/-
error: load_design_sv2: 'Examples/system-verilog/sem2/untyped_width_repair/untyped_width_repair.sv.json' REFUSED — our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):
  localparam 'L': Constant:override-type — constant expression depends on an overridden untyped parameter
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 repair
  from "Examples/system-verilog/sem2/untyped_width_repair/untyped_width_repair.sv.json"

end Examples.«system-verilog».sem2.untyped_width_repair.agree
