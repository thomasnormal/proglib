import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

set_option maxRecDepth 100000 in
load_design_sv2 initial_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/initial_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def d : MemDesign2 :=
  initial_memory_wall.pdesign.instantiateMemD2 [8, 2]

private def d32 : MemDesign2 :=
  initial_memory_wall.pdesign.instantiateMemD2 [32, 32]

-- The parser's Initial node is retained in the memory route and runs once at
-- time zero (§9.2.1), before the first sampled input.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard d.processes.length == 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard runMem2 d 32 [[("clk", LVec.lit "0")]] == .ok [[("clk", LVec.lit "0"), ("q", LVec.lit "00111100")]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#guard runMem2 d32 32 [[("clk", LVec.lit "0")]] == .ok [[("clk", LVec.lit "0"), ("q", LVec.lit "00000000000000000000000000111100")]]

#print axioms LeanModels.Sv.Kernel.runMem2
