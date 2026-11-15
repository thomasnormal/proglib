import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.readmemh_rom_canonical_e
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 readmemhRom from "Examples/system-verilog/sem2/readmemh_rom_canonical_e/readmemh_rom_canonical_e.sv.json"
def outputs : Res (List String) := do
  let d ← readmemhRom.e
  let st ← d.initialState
  let rows ← runCoreMemRows d st [[("addr", LVec.lit "00")], [("addr", LVec.lit "01")], [("addr", LVec.lit "10")], [("addr", LVec.lit "11")], [("addr", LVec.lit "xx")]]
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")
#guard outputs == .ok ["00000000", "00010001", "00100010", "00110011", "xxxxxxxx"]
end Examples.«system-verilog».sem2.readmemh_rom_canonical_e
