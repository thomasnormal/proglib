import LeanModels.Refine.RvfiUpper
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 upper-immediate class

The two RV32I upper-immediate instructions share the decoded ALU boundary but
select different first operands.  The fixed words below are checked by the
exact decoder, then threaded through the memory-preserving step and retirement
boundary for arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_upper

open LeanModels.Rv
open LeanModels.Refine

def luiWord : Word := 0x123451b7
def auipcWord : Word := 0x12345197

theorem upper_decodes :
    Fetched.decode (.word luiWord) =
      some (.alu .add 3 (.reg 0) (.imm 0x12345000)) ∧
    Fetched.decode (.word auipcWord) =
      some (.alu .add 3 .pc (.imm 0x12345000)) := by
  decide

def luiInstruction : UpperInstruction :=
  { word := luiWord
    kind := .lui 3 0x12345000
    decode := upper_decodes.1 }

def auipcInstruction : UpperInstruction :=
  { word := auipcWord
    kind := .auipc 3 0x12345000
    decode := upper_decodes.2 }

theorem picorv32_lui_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word luiWord) 0 =
      (luiNext state 3 0x12345000, memory) := by
  exact isaStepMemWith_lui cv32e40pProfile state memory luiWord 3 0x12345000
    upper_decodes.1

theorem picorv32_lui_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word luiWord, memory := memory, irq := 0 } =
      (luiNext state 3 0x12345000,
        luiRetirement state
          { fetched := .word luiWord, memory := memory, irq := 0 }
          3 0x12345000) := by
  exact rvMachineWith_lui cv32e40pProfile state memory luiWord 3 0x12345000
    upper_decodes.1

theorem picorv32_auipc_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word auipcWord) 0 =
      (auipcNext state 3 0x12345000, memory) := by
  exact isaStepMemWith_auipc cv32e40pProfile state memory auipcWord 3
    0x12345000 upper_decodes.2

theorem picorv32_auipc_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word auipcWord, memory := memory, irq := 0 } =
      (auipcNext state 3 0x12345000,
        auipcRetirement state
          { fetched := .word auipcWord, memory := memory, irq := 0 }
          3 0x12345000) := by
  exact rvMachineWith_auipc cv32e40pProfile state memory auipcWord 3
    0x12345000 upper_decodes.2

/-! These wrappers connect exact loaded-core execution and decoder premises to
    the indexed dispatcher.  The raw upper boundary remains an explicit
    premise, so neither the source step nor the RVFI observation is inferred
    from the fixed instruction word. -/

theorem picorv32_lui_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.luiBoundary arch input luiWord 3 0x12345000) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := luiNext arch 3 0x12345000, memory := input.memory }
        (luiRetirement arch input 3 0x12345000) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hupper : rvfi_core_adapter.CoreUpperBoundary d st entry arch input
      luiInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [luiInstruction, RvfiObservation.upperBoundary] using hboundary
  simpa [luiInstruction, UpperKind.next, UpperKind.retirement] using
    hupper.to_rv32i_boundary

theorem picorv32_auipc_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.auipcBoundary arch input auipcWord 3 0x12345000) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry =
      .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := auipcNext arch 3 0x12345000, memory := input.memory }
        (auipcRetirement arch input 3 0x12345000) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by
    rw [d.fastStepCanonical_eq_step]
    exact hstep
  have hupper : rvfi_core_adapter.CoreUpperBoundary d st entry arch input
      auipcInstruction := by
    refine ⟨next, observation,
      rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [auipcInstruction, RvfiObservation.upperBoundary] using hboundary
  simpa [auipcInstruction, UpperKind.next, UpperKind.retirement] using
    hupper.to_rv32i_boundary

#print axioms picorv32_lui_loaded_rv32i_boundary_of_step
#print axioms picorv32_auipc_loaded_rv32i_boundary_of_step

#print axioms picorv32_lui_class_step
#print axioms picorv32_lui_class_commit
#print axioms picorv32_auipc_class_step
#print axioms picorv32_auipc_class_commit

end Examples.«system-verilog».cores.picorv32.r1_upper
