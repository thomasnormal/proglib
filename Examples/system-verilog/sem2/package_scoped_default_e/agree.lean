import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_scoped_default_e
open LeanModels.Sv
load_design_sv2 p from "Examples/system-verilog/sem2/package_scoped_default_e/package_scoped_default_e.sv.json"
#guard p.pdesign.others == []
#guard match p.e 16 with | .ok _ => true | _ => false
end Examples.«system-verilog».sem2.package_scoped_default_e
