import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for the same source-shaped one-rank register file.

The memory remains one native `MemState`.  This receipt keeps the runtime
index, x/z index, and NBA rows on `CoreMemDesign` rather than the compatibility
MemE surface.
-/

namespace Examples.«system-verilog».sem2.unpacked_cpuregs_e.canonical

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 cpuregs
  from "Examples/system-verilog/sem2/unpacked_cpuregs_e/unpacked_cpuregs_e.sv.json"

def stimuli : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 0),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 0),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.lit "xxxxx"),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.lit "zzzzz"),
    ("waddr", LVec.ofNat 5 3), ("wdata", LVec.ofNat 32 0xa5),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.lit "xxxxx"), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.lit "xxxxx"), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 0)],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 3),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.lit "x")],
   [("clk", LVec.ofNat 1 1), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.lit "x")],
   [("clk", LVec.ofNat 1 0), ("raddr", LVec.ofNat 5 7),
    ("waddr", LVec.ofNat 5 7), ("wdata", LVec.ofNat 32 0x5a),
    ("we", LVec.ofNat 1 0)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem cpuregs.pdesign [32]
  let rows ← runCoreMemRows d d.initial stimuli
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "rdata")

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard outputs == .ok
  ["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
   "00000000000000000000000010100101", "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
   "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "00000000000000000000000010100101",
   "00000000000000000000000010100101", "00000000000000000000000010100101",
   "00000000000000000000000001011010", "00000000000000000000000001011010",
   "00000000000000000000000001011010"]

end Examples.«system-verilog».sem2.unpacked_cpuregs_e.canonical
