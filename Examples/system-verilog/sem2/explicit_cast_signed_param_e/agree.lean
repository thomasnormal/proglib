import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.explicit_cast_signed_param_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 cast from "Examples/system-verilog/sem2/explicit_cast_signed_param_e/explicit_cast_signed_param_e.sv.json"
#guard cast.pdesign.others == []
#guard match cast.e 8 with | .ok E => E.scalarWidth? "ys" == some 8 | _ => false
end Examples.«system-verilog».sem2.explicit_cast_signed_param_e
