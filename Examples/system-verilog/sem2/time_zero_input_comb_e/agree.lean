/- Canonical-E refusal for an input edge coinciding with always_comb startup.
IEEE 1800-2023 §§4.7 and 9.2.2.2.2 leave the time-zero active ordering open. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.time_zero_input_comb_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 timeZeroInputComb
  from "Examples/system-verilog/sem2/time_zero_input_comb_e/time_zero_input_comb_e.sv.json"
#guard match timeZeroInputComb.e with
  | .unsupported msg => msg.startsWith "Event:time-zero"
  | _ => false
end Examples.«system-verilog».sem2.time_zero_input_comb_e.agree
