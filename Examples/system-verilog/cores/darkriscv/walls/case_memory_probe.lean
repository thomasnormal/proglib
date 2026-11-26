import LeanModels.Sv.Ingest2
import LeanModels.Sv.MemCycle

/-!
  Clean-room guard for a normal `case` selecting a one-rank unpacked memory
  cell.  The source-shaped `Case`/`ArraySel` nodes are retained by the parser;
  the memory route executes the first matching arm, queues the selected NBA,
  and publishes the cell through the continuous assignment.  Normal case
  matching follows IEEE 1800-2023 §12.5.1.
-/

set_option maxRecDepth 100000 in
load_design_sv2 dark_case_memory_wall
  from "Examples/system-verilog/cores/darkriscv/walls/case_memory.sv.json"

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def stimulus (clk : Nat) (sel : LVec) (d : Nat) : SvState :=
  [("clk", LVec.ofNat 1 clk), ("sel", sel),
   ("d", LVec.ofNat 8 d)]

private def observed (st : SvState) : Option Nat :=
  (SvState.lookup st "q").bind LVec.toNat?

private def sampled : List SvState → List SvState
  | [] => []
  | state :: rest => state :: match rest with
    | [] => []
    | _ :: tail => sampled tail

private def caseTrace : Res (List (Option Nat)) :=
  match runMem2 (dark_case_memory_wall.pdesign.instantiateMemD2 [1]) 64
      [ stimulus 0 (LVec.ofNat 2 0) 0,
        stimulus 1 (LVec.ofNat 2 0) 0x3C,
        stimulus 0 (LVec.ofNat 2 0) 0x3C,
        stimulus 1 (LVec.ofNat 2 1) 0,
        stimulus 0 (LVec.ofNat 2 1) 0,
        stimulus 1 (LVec.ofNat 2 2) 0,
        stimulus 0 (LVec.ofNat 2 2) 0,
        stimulus 1 (LVec.ofNat 2 3) 0,
        stimulus 0 (LVec.ofNat 2 3) 0,
        stimulus 1 (LVec.xVec 2) 0,
        stimulus 0 (LVec.xVec 2) 0,
        stimulus 1 (LVec.replicate 2 .lz) 0,
        stimulus 0 (LVec.replicate 2 .lz) 0 ] with
  | .ok states => .ok ((sampled states).map observed)
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout

#guard match (dark_case_memory_wall.pdesign.instantiateMemD2 [1]).processes with
  | [.alwaysPlain "clk" (.block [
      .caseStmt (.ident "sel") _ _ .normal .none]),
      .assign "q" (.arrayElem "mem" [.int 0])] => true
  | _ => false

#guard caseTrace == .ok [
  none,
  some 0x3C,
  some 0xA5,
  some 0x5A,
  some 0x5A,
  some 0x5A,
  some 0x5A]
