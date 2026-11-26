import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-!
  Differential receipt for a source-shaped dynamic unpacked-memory NBA write.
  The memory is written at `REGS[DPTR]` by a posedge process.  Rows observe
  the four cells after reset, then after writes to indices 2 and 1, following
  IEEE 1800-2023 §§4.6, 10.4, and 11.5.1.
-/

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 dynamic_memory_nba_rows
  from "Examples/system-verilog/cores/darkriscv/walls/dynamic_memory_nba.sv.json"

private def stimulus (clk reset index data : Nat) : SvState :=
  [("CLK", LVec.ofNat 1 clk), ("RES", LVec.ofNat 1 reset),
   ("DPTR", LVec.ofNat 2 index), ("DATA", LVec.ofNat 32 data)]

private def cells (st : CoreMemState) : String :=
  let m := st.memory
  let cell (i : Nat) :=
    (MemState.read m "REGS" i).map LVec.toBinString |>.getD
      "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  cell 3 ++ "_" ++ cell 2 ++ "_" ++ cell 1 ++ "_" ++ cell 0

private def rows : Res (List String) := do
  let d ← PDesign.instantiateCoreMem dynamic_memory_nba_rows.pdesign []
  let st0 ← d.initialState
  let st1 ← d.step st0 (stimulus 0 1 0 0)
  let st2 ← d.step st1 (stimulus 1 0 2 0xa5)
  let st3 ← d.step st2 (stimulus 0 0 2 0xa5)
  let st4 ← d.step st3 (stimulus 1 0 1 0x5a)
  pure [cells st0, cells st1, cells st2, cells st3, cells st4]

#guard rows == .ok [
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_00000000000000000000000010100101_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_00000000000000000000000010100101_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx_00000000000000000000000010100101_00000000000000000000000001011010_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"]
