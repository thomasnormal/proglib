import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemResume

namespace Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 memoryEdgeBlocking
  from "Examples/system-verilog/sem2/memory_edge_blocking_canonical_e/memory_edge_blocking_canonical_e.sv.json"

#guard match PDesign.instantiateCoreMem memoryEdgeBlocking.pdesign [4, 2] with
  | .ok d =>
      d.memories.size == 1 &&
      d.processes.toList.any (fun p => match p with
        | .edge { style := .alwaysPlain, body := .block (_ :: _), .. } => true
        | .event (_ :: _) (.block (_ :: _)) => true
        | _ => false)
  | _ => false

private def stimulus : List SvState :=
  [[("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 3)],
   [("clk", LVec.ofNat 1 1), ("d", LVec.ofNat 4 10)]]

def outputs : Res (List (String × String × String × String)) := do
  let d ← PDesign.instantiateCoreMem memoryEdgeBlocking.pdesign [4, 2]
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view d s) "mem0",
     SvState.showSignal (CoreMemState.view d s) "mem1",
     SvState.showSignal (CoreMemState.view d s) "delayed",
     SvState.showSignal (CoreMemState.view d s) "marker"))

#guard match outputs with
  | .ok [("0001", "0010", "0000", "0000"),
        ("1010", "1010", "1010", "0000")] => true
  | _ => false

private def edgeBody? : List CoreMemProc → Option PStmt
  | [] => none
  | .edge q :: _ => some q.body
  | .event _ body :: _ => some body
  | _ :: rest => edgeBody? rest

private def firstEdgeBody (d : CoreMemDesign) : Option PStmt :=
  edgeBody? d.processes.toList

private def runEdgeCursorFuel (E : CoreMemDesign) : Nat →
    CoreMemExecResult → EdgeCursor → Res CoreMemExecResult
  | 0, _, _ => .timeout
  | n + 1, acc, cursor =>
      match cursor.work with
      | [] => .ok acc
      | _ => do
          let (step, next) ← cursor.resume E acc.state
          runEdgeCursorFuel E n (CoreMemExec.append acc step) next

private def cursorReceipt : Res (String × String × String × String × String) := do
  let d ← PDesign.instantiateCoreMem memoryEdgeBlocking.pdesign [4, 2]
  let initial ← d.initialState
  let (pre, _, _) ← d.prepareStep initial
    [("clk", LVec.ofNat 1 0), ("d", LVec.ofNat 4 10)]
  let some body := firstEdgeBody d | .unsupported "edge receipt: retained edge body missing"
  let some md := d.memories[0]? | .unsupported "edge receipt: retained memory missing"
  let seed : CoreMemExecResult :=
    { state := pre, scalarQ := [], memoryQ := [], locals := [] }
  let result ← runEdgeCursorFuel d 32 seed (EdgeCursor.start d.env body)
  let delayed := (result.scalarQ.find? (fun q => q.1 == "delayed")).map (fun q => q.2.2)
  let marker := (CoreMemState.view d result.state).lookup "marker"
  let mem0 := result.state.memory.readIndexId md.shape.id false (.ofNat 2 0)
  let mem1 := (result.memoryQ.find? (fun q => q.id == md.shape.id && q.label == 1)).map (fun q => q.value)
  .ok (SvState.showSignal (CoreMemState.view d result.state) "marker",
    delayed.map LVec.toBinString |>.getD "missing",
    mem0.map LVec.toBinString |>.getD "missing",
    mem1.map LVec.toBinString |>.getD "missing",
    marker.map LVec.toBinString |>.getD "missing")

#guard cursorReceipt == .ok ("0000", "1010", "1010", "1010", "0000")

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.memory_edge_blocking_canonical_e
