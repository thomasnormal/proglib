import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.comb_chain_unpacked
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 chain from "Examples/system-verilog/sem2/comb_chain_unpacked/comb_chain_unpacked.sv.json"
#guard chain.e 8 matches .ok _
end Examples.«system-verilog».sem2.comb_chain_unpacked
