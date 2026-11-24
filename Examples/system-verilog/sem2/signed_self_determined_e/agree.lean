import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.signed_self_determined_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 signedSelf from "Examples/system-verilog/sem2/signed_self_determined_e/signed_self_determined_e.sv.json"
#guard signedSelf.pdesign.others == []
#guard match signedSelf.e with | .ok E => E.scalarWidth? "y" == some 1 | _ => false
#guard match signedSelf.e with
  | .ok E => match runCoreMemRows E E.initial [[("a", LVec.ofNat 4 15), ("b", LVec.ofNat 4 0), ("en", LVec.ofLogic .l1)]] with
    | .ok [s] => SvState.showSignal (CoreMemState.view E s) "y" == "1"
    | _ => false
  | _ => false
end Examples.«system-verilog».sem2.signed_self_determined_e
