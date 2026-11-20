import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

/-! Canonical-E receipt for a plain event process retained inside a generate loop.
The body is substituted once per genvar value before execution, as required by
IEEE 1800-2023 §27.4. -/
namespace Examples.«system-verilog».sem2.plain_generate_edge_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 plainGenerateEdge
  from "Examples/system-verilog/sem2/plain_generate_edge_e/plain_generate_edge_e.sv.json"

def stimulus : List SvState :=
  [[("clk", LVec.ofLogic .l0), ("d", LVec.ofNat 2 0)],
   [("clk", LVec.ofLogic .l1), ("d", LVec.ofNat 2 1)],
   [("clk", LVec.ofLogic .l0), ("d", LVec.ofNat 2 2)],
   [("clk", LVec.ofLogic .l1), ("d", LVec.ofNat 2 2)],
   [("clk", LVec.ofLogic .lx), ("d", LVec.lit "xx")],
   [("clk", LVec.ofLogic .l1), ("d", LVec.lit "zz")],
   [("clk", LVec.ofLogic .l0), ("d", LVec.ofNat 2 3)],
   [("clk", LVec.ofLogic .l1), ("d", LVec.ofNat 2 3)]]

def outputs : Res (List String) := do
  let d ← PDesign.instantiateCoreMem plainGenerateEdge.pdesign [2]
  let rows ← runCoreMemRows d d.initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "q")

#guard match PDesign.instantiateCoreMem plainGenerateEdge.pdesign [2] with
  | .ok d => d.processes.size == 2 &&
      match d.processes[0]? with
      | some (CoreMemProc.event events body) =>
          (match events with | [{ signal := "clk", edge := PEventEdge.posedge }] => true | _ => false) &&
          match body with
          | .nbaAssignL (.bitSel "q" (.int 0)) (.bitSel (.ident "d") _) => true
          | _ => false
      | _ => false
  | _ => false

#guard outputs == .ok ["xx", "10", "10", "01", "01", "zz", "zz", "11"]

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.plain_generate_edge_e
