import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv
open LeanModels.Sv.CombView
namespace Examples.«system-verilog».sem2.localparam_logic
load_design_sv2 localparamLogic from "Examples/system-verilog/sem2/localparam_logic/localparam_logic.sv.json"
#guard (localparamLogic.sem).decls.size > 0
#guard (localparamLogic.sem).processes.size > 0
#guard match localparamLogic.pdesign.summary with
  | .error e => e == "site `plain#0`: expression construct outside the v1 fragment (constant, cast, width conversion or system call)"
  | .ok _ => false
#guard match localparamLogic.pdesign.paramEnv2 [] with
  | .ok e => e.nvals.lookup "OP" == some (1, 4, false)
  | _ => false
end Examples.«system-verilog».sem2.localparam_logic
