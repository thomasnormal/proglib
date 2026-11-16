import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary
namespace Examples.«system-verilog».sklansky_guards.nonaffine.gen
open LeanModels.Sv LeanModels.Sv.CombView
load_design_sv2 nonaffine from "Examples/system-verilog/sklansky_guards/nonaffine/nonaffine.sv.json"
-- Read now: `(i >> 1) << 1` is the literal-amount atom `shlK i 1` (it was refused as not affine before).
#guard nonaffine.pdesign.summary.toOption.isSome
end Examples.«system-verilog».sklansky_guards.nonaffine.gen
