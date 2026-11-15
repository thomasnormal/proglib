import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.constant_struct_pattern_package_e.oracle
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 constantStructPatternPackageE
  from "Examples/system-verilog/sem2/constant_struct_pattern_package_e/constant_struct_pattern_package_e.sv.json"
def main : IO Unit := do
  IO.println "ROW y=01"
end Examples.«system-verilog».sem2.constant_struct_pattern_package_e.oracle
