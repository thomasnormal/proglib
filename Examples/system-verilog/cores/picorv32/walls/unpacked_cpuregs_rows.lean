import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unpacked_cpuregs_rows
  from "Examples/system-verilog/cores/picorv32/walls/unpacked_cpuregs.sv.json"

def rows : Res (List String) := do
  let d ← unpacked_cpuregs_rows.e 32
  let st ← d.initialState
  let rs ← runCoreMemRows d st
    [ [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 0),
        ("waddr", LVec.ofNat 5 0), ("wdata", LVec.ofNat 32 0),
        ("we", LVec.ofNat 1 0)],
      [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 0),
        ("waddr", LVec.ofNat 5 1), ("wdata", LVec.ofNat 32 0xa5),
        ("we", LVec.ofNat 1 1)],
      [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 1),
        ("waddr", LVec.ofNat 5 1), ("wdata", LVec.ofNat 32 0),
        ("we", LVec.ofNat 1 0)],
      [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 1),
        ("waddr", LVec.ofNat 5 2), ("wdata", LVec.ofNat 32 0x3c),
        ("we", LVec.ofNat 1 1)],
      [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 2),
        ("waddr", LVec.ofNat 5 2), ("wdata", LVec.ofNat 32 0),
        ("we", LVec.ofNat 1 0)],
      [("clk", LVec.ofNat 1 0), ("raddr", LVec.xVec 5),
        ("waddr", LVec.ofNat 5 2), ("wdata", LVec.ofNat 32 0),
        ("we", LVec.ofNat 1 0)] ]
  .ok (rs.map fun s => SvState.showSignal (CoreMemState.view d s) "rdata")

#guard rows == .ok ["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
  "00000000000000000000000010100101", "00000000000000000000000010100101",
  "00000000000000000000000000111100", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"]
