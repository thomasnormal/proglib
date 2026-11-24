import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.CombPhaseFrame
import LeanModels.Sv.Kernel.EdgePhaseConfluence
namespace Examples.«system-verilog».sem2.two_blocking_disjoint_e
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 twoBlocking from "Examples/system-verilog/sem2/two_blocking_disjoint_e/two_blocking_disjoint_e.sv.json"

def guardReceipt : Bool :=
  match twoBlocking.pdesign.processes with
  | [p, q] =>
      match coreMemHasCommonEventSourceThroughAssign [p, q] p q with
      | true =>
          (coreMemProcBlockingWrites p).contains "a" &&
          (coreMemProcBlockingWrites q).contains "b"
      | false => false
  | _ => false

#guard guardReceipt

example : CombPhaseGuard twoBlocking.pdesign := by
  constructor <;> decide

example : ∃ p q,
    twoBlocking.pdesign.processes = [p, q] ∧
    coreMemHasCommonEventSourceThroughAssign [p, q] p q = true := by
  exact ⟨twoBlocking.pdesign.processes[0]!, twoBlocking.pdesign.processes[1]!, by rfl, by decide⟩

example : ∃ p q,
    twoBlocking.pdesign.processes = [p, q] ∧
    (∀ x, x ∈ coreMemProcBlockingWrites p →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames q)) ∧
    (∀ x, x ∈ coreMemProcBlockingWrites q →
      x ∉ coreMemReadNamesThroughDrivers [p, q] 32
        (coreMemPProcessReadNames p)) := by
  obtain ⟨p, q, hprocesses, hcommon⟩ := show ∃ p q,
      twoBlocking.pdesign.processes = [p, q] ∧
      coreMemHasCommonEventSourceThroughAssign [p, q] p q = true from
    ⟨twoBlocking.pdesign.processes[0]!, twoBlocking.pdesign.processes[1]!, by rfl, by decide⟩
  have hg : CombPhaseGuard twoBlocking.pdesign := by
    constructor <;> decide
  exact ⟨p, q, hprocesses,
    (hg.two_process_read_write_exclusions hprocesses hcommon).1,
    (hg.two_process_read_write_exclusions hprocesses hcommon).2⟩

#print axioms guardReceipt
end Examples.«system-verilog».sem2.two_blocking_disjoint_e
