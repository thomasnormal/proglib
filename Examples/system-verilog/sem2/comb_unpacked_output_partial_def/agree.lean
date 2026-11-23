import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.comb_unpacked_output_partial_def
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 combUnpacked from "Examples/system-verilog/sem2/comb_unpacked_output_partial_def/comb_unpacked_output_partial_def.sv.json"
#guard PDesign.instantiateE2 combUnpacked.pdesign [] (PDesign.surfaceFuel []) matches .unsupported _
end Examples.«system-verilog».sem2.comb_unpacked_output_partial_def
