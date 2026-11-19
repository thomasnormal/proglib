import LeanModels.Refine.RvfiAlu
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 register-register ALU class

The pinned PicoRV32 RVFI program uses the standard RV32I register-register
encodings.  This file covers the complete ten-operation ALU family.  Each
word is decoded by the exact ISA parser, then threaded through the
memory-preserving step and retirement boundary for arbitrary architectural
state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_alu

open LeanModels.Rv
open LeanModels.Refine

def addWord : Word := 0x002081b3
def subWord : Word := 0x402081b3
def sllWord : Word := 0x002091b3
def sltWord : Word := 0x0020a1b3
def sltuWord : Word := 0x0020b1b3
def xorWord : Word := 0x0020c1b3
def srlWord : Word := 0x0020d1b3
def sraWord : Word := 0x4020d1b3
def orWord : Word := 0x0020e1b3
def andWord : Word := 0x0020f1b3

theorem alu_decodes :
    Fetched.decode (.word addWord) = some (.alu .add 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word subWord) = some (.alu .sub 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sllWord) = some (.alu .sll 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sltWord) = some (.alu .slt 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sltuWord) = some (.alu .sltu 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word xorWord) = some (.alu .xor 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word srlWord) = some (.alu .srl 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word sraWord) = some (.alu .sra 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word orWord) = some (.alu .or 3 (.reg 1) (.reg 2)) ∧
    Fetched.decode (.word andWord) = some (.alu .and 3 (.reg 1) (.reg 2)) := by
  decide

def addInstruction : AluInstruction :=
  { word := addWord, op := .add, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.1 }
def subInstruction : AluInstruction :=
  { word := subWord, op := .sub, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.1 }
def sllInstruction : AluInstruction :=
  { word := sllWord, op := .sll, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.1 }
def sltInstruction : AluInstruction :=
  { word := sltWord, op := .slt, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.1 }
def sltuInstruction : AluInstruction :=
  { word := sltuWord, op := .sltu, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.1 }
def xorInstruction : AluInstruction :=
  { word := xorWord, op := .xor, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.2.1 }
def srlInstruction : AluInstruction :=
  { word := srlWord, op := .srl, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.2.2.1 }
def sraInstruction : AluInstruction :=
  { word := sraWord, op := .sra, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.2.2.2.1 }
def orInstruction : AluInstruction :=
  { word := orWord, op := .or, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.2.2.2.2.1 }
def andInstruction : AluInstruction :=
  { word := andWord, op := .and, rd := 3, src1 := .reg 1, src2 := .reg 2,
    decode := alu_decodes.2.2.2.2.2.2.2.2.2 }

/-! The generic ALU fields determine the exact memory-threaded ISA step for
    register, immediate, and pc-based source operands. -/

theorem picorv32_alu_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (hfields : observation.aluFields state input word op rd src1 src2) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (aluNext state op rd src1 src2, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.alu op rd src1 src2) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_alu profile state memory word op rd src1 src2 hdecode

#print axioms picorv32_alu_fields_isa_step

theorem alu_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (instruction : AluInstruction)
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input instruction.word instruction.op
      instruction.rd instruction.src1 instruction.src2) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := aluNext arch instruction.op instruction.rd instruction.src1 instruction.src2,
          memory := input.memory }
        (aluRetirement arch input instruction.op instruction.rd instruction.src1 instruction.src2) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  exact (rvfi_core_adapter.CoreAluBoundary.to_rv32i_boundary
    (⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreAluBoundary d st entry arch input instruction))

theorem picorv32_add_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input addWord .add 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .add 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .add 3 (.reg 1) (.reg 2)) := by
  simpa [addInstruction] using alu_loaded_rv32i_boundary_of_step addInstruction hstep hdecode hboundary

theorem picorv32_sub_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input subWord .sub 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .sub 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .sub 3 (.reg 1) (.reg 2)) := by
  simpa [subInstruction] using alu_loaded_rv32i_boundary_of_step subInstruction hstep hdecode hboundary

theorem picorv32_sll_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sllWord .sll 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .sll 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .sll 3 (.reg 1) (.reg 2)) := by
  simpa [sllInstruction] using alu_loaded_rv32i_boundary_of_step sllInstruction hstep hdecode hboundary

theorem picorv32_slt_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sltWord .slt 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .slt 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .slt 3 (.reg 1) (.reg 2)) := by
  simpa [sltInstruction] using alu_loaded_rv32i_boundary_of_step sltInstruction hstep hdecode hboundary

theorem picorv32_sltu_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sltuWord .sltu 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .sltu 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .sltu 3 (.reg 1) (.reg 2)) := by
  simpa [sltuInstruction] using alu_loaded_rv32i_boundary_of_step sltuInstruction hstep hdecode hboundary

theorem picorv32_xor_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input xorWord .xor 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .xor 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .xor 3 (.reg 1) (.reg 2)) := by
  simpa [xorInstruction] using alu_loaded_rv32i_boundary_of_step xorInstruction hstep hdecode hboundary

theorem picorv32_srl_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input srlWord .srl 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .srl 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .srl 3 (.reg 1) (.reg 2)) := by
  simpa [srlInstruction] using alu_loaded_rv32i_boundary_of_step srlInstruction hstep hdecode hboundary

theorem picorv32_sra_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sraWord .sra 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .sra 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .sra 3 (.reg 1) (.reg 2)) := by
  simpa [sraInstruction] using alu_loaded_rv32i_boundary_of_step sraInstruction hstep hdecode hboundary

theorem picorv32_or_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input orWord .or 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .or 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .or 3 (.reg 1) (.reg 2)) := by
  simpa [orInstruction] using alu_loaded_rv32i_boundary_of_step orInstruction hstep hdecode hboundary

theorem picorv32_and_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input andWord .and 3 (.reg 1) (.reg 2)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := aluNext arch .and 3 (.reg 1) (.reg 2), memory := input.memory }
        (aluRetirement arch input .and 3 (.reg 1) (.reg 2)) := by
  simpa [andInstruction] using alu_loaded_rv32i_boundary_of_step andInstruction hstep hdecode hboundary

/-! The complete ALU family has one exact-cycle mixed consumer.  Its retained
    `AluInstruction` witness carries the operation and both source forms into
    the RV32I dispatcher without selecting a separate decoded operation. -/

theorem picorv32_alu_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : AluInstruction)
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep d state (machine.encode state input) =
            .ok (next, observation) ∧
          (if observation.valid then
            input = aluProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.aluBoundary memoryState.arch input instruction.word
              instruction.op instruction.rd instruction.src1 instruction.src2 ∧
            rel next
              { arch := aluNext memoryState.arch instruction.op instruction.rd
                  instruction.src1 instruction.src2,
                memory := memoryState.memory }
          else rel next memoryState)) :
    Rv32iCycleStepRefines machine.toRvfiCycleMachine rel admit := by
  apply machine.to_rv32i_step_refines
  intro start state memoryState input hrel hadmit
  rcases hstep start state memoryState input hrel hadmit with
    ⟨next, observation, hrun, hcase⟩
  refine ⟨next, observation, hrun, ?_⟩
  cases hv : observation.valid with
  | false =>
      simpa [hv] using hcase
  | true =>
      simp only [hv, ↓reduceIte] at hcase
      rcases hcase with ⟨hinput, horder, hboundary, hnext⟩
      have hmem : input.memory = memoryState.memory := by
        rw [hinput]
        rfl
      have hrvfi : Rv32iBoundary memoryState.arch input observation
          (rv32iProgramStep memoryState (.alu instruction))
          (rv32iProgramRetirement memoryState (.alu instruction)) := by
        simpa [hmem, hinput, aluProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (Rv32iBoundary.alu instruction.word instruction.op instruction.rd
            instruction.src1 instruction.src2 hboundary)
      simp only [↓reduceIte]
      exact ⟨.alu instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, by simpa [rv32iProgramStep] using hnext⟩

#print axioms picorv32_alu_exact_cycle_step_refines

theorem picorv32_add_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word addWord) 0 =
      (aluNext state .add 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory addWord .add 3
    (.reg 1) (.reg 2) alu_decodes.1

theorem picorv32_add_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word addWord, memory := memory, irq := 0 } =
      (aluNext state .add 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word addWord, memory := memory, irq := 0 }
          .add 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory addWord .add 3
    (.reg 1) (.reg 2) alu_decodes.1

theorem picorv32_sub_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word subWord) 0 =
      (aluNext state .sub 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory subWord .sub 3
    (.reg 1) (.reg 2) alu_decodes.2.1

theorem picorv32_sub_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word subWord, memory := memory, irq := 0 } =
      (aluNext state .sub 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word subWord, memory := memory, irq := 0 }
          .sub 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory subWord .sub 3
    (.reg 1) (.reg 2) alu_decodes.2.1

theorem picorv32_sll_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sllWord) 0 =
      (aluNext state .sll 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sllWord .sll 3
    (.reg 1) (.reg 2) alu_decodes.2.2.1

theorem picorv32_sll_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sllWord, memory := memory, irq := 0 } =
      (aluNext state .sll 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sllWord, memory := memory, irq := 0 }
          .sll 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sllWord .sll 3
    (.reg 1) (.reg 2) alu_decodes.2.2.1

theorem picorv32_slt_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltWord) 0 =
      (aluNext state .slt 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltWord .slt 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.1

theorem picorv32_slt_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltWord, memory := memory, irq := 0 } =
      (aluNext state .slt 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sltWord, memory := memory, irq := 0 }
          .slt 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltWord .slt 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.1

theorem picorv32_sltu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltuWord) 0 =
      (aluNext state .sltu 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltuWord .sltu 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.1

theorem picorv32_sltu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltuWord, memory := memory, irq := 0 } =
      (aluNext state .sltu 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sltuWord, memory := memory, irq := 0 }
          .sltu 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltuWord .sltu 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.1

theorem picorv32_xor_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word xorWord) 0 =
      (aluNext state .xor 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory xorWord .xor 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.1

theorem picorv32_xor_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word xorWord, memory := memory, irq := 0 } =
      (aluNext state .xor 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word xorWord, memory := memory, irq := 0 }
          .xor 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory xorWord .xor 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.1

theorem picorv32_srl_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word srlWord) 0 =
      (aluNext state .srl 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory srlWord .srl 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.1

theorem picorv32_srl_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word srlWord, memory := memory, irq := 0 } =
      (aluNext state .srl 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word srlWord, memory := memory, irq := 0 }
          .srl 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory srlWord .srl 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.1

theorem picorv32_sra_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sraWord) 0 =
      (aluNext state .sra 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sraWord .sra 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.1

theorem picorv32_sra_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sraWord, memory := memory, irq := 0 } =
      (aluNext state .sra 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word sraWord, memory := memory, irq := 0 }
          .sra 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sraWord .sra 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.1

theorem picorv32_or_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word orWord) 0 =
      (aluNext state .or 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory orWord .or 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.1

theorem picorv32_or_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word orWord, memory := memory, irq := 0 } =
      (aluNext state .or 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word orWord, memory := memory, irq := 0 }
          .or 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory orWord .or 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.1

theorem picorv32_and_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word andWord) 0 =
      (aluNext state .and 3 (.reg 1) (.reg 2), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory andWord .and 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.2

theorem picorv32_and_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word andWord, memory := memory, irq := 0 } =
      (aluNext state .and 3 (.reg 1) (.reg 2),
        aluRetirement state
          { fetched := .word andWord, memory := memory, irq := 0 }
          .and 3 (.reg 1) (.reg 2)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory andWord .and 3
    (.reg 1) (.reg 2) alu_decodes.2.2.2.2.2.2.2.2.2

#print axioms picorv32_add_class_step
#print axioms picorv32_add_class_commit
#print axioms picorv32_sub_class_step
#print axioms picorv32_sub_class_commit
#print axioms picorv32_sll_class_step
#print axioms picorv32_sll_class_commit
#print axioms picorv32_slt_class_step
#print axioms picorv32_slt_class_commit
#print axioms picorv32_sltu_class_step
#print axioms picorv32_sltu_class_commit
#print axioms picorv32_xor_class_step
#print axioms picorv32_xor_class_commit
#print axioms picorv32_srl_class_step
#print axioms picorv32_srl_class_commit
#print axioms picorv32_sra_class_step
#print axioms picorv32_sra_class_commit
#print axioms picorv32_or_class_step
#print axioms picorv32_or_class_commit
#print axioms picorv32_and_class_step
#print axioms picorv32_and_class_commit

end Examples.«system-verilog».cores.picorv32.r1_alu
