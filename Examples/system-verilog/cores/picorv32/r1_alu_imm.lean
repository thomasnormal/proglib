import LeanModels.Refine.RvfiAlu
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 remaining immediate ALU class

The ADDI row is already recorded in `r1_addi`.  This file closes the other
nine RV32I OP-IMM forms.  Each fixed word is decoded by the exact ISA parser,
then threaded through the memory-preserving step and retirement boundary for
arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_alu_imm

open LeanModels.Rv
open LeanModels.Refine

def sltiWord : Word := 0x06422193
def sltiuWord : Word := 0x06433293
def xoriWord : Word := 0x7ff44393
def oriWord : Word := 0x80056493
def andiWord : Word := 0x0ff67593
def slliWord : Word := 0x01f71693
def srliWord : Word := 0x00185793
def sraiWord : Word := 0x40795893
def addiNegWord : Word := 0xffb10093

theorem alu_imm_decodes :
    Fetched.decode (.word sltiWord) =
      some (.alu .slt 3 (.reg 4) (.imm 100)) ∧
    Fetched.decode (.word sltiuWord) =
      some (.alu .sltu 5 (.reg 6) (.imm 100)) ∧
    Fetched.decode (.word xoriWord) =
      some (.alu .xor 7 (.reg 8) (.imm 2047)) ∧
    Fetched.decode (.word oriWord) =
      some (.alu .or 9 (.reg 10) (.imm 0xFFFFF800)) ∧
    Fetched.decode (.word andiWord) =
      some (.alu .and 11 (.reg 12) (.imm 255)) ∧
    Fetched.decode (.word slliWord) =
      some (.alu .sll 13 (.reg 14) (.imm 31)) ∧
    Fetched.decode (.word srliWord) =
      some (.alu .srl 15 (.reg 16) (.imm 1)) ∧
    Fetched.decode (.word sraiWord) =
      some (.alu .sra 17 (.reg 18) (.imm 7)) ∧
    Fetched.decode (.word addiNegWord) =
      some (.alu .add 1 (.reg 2) (.imm 0xFFFFFFFB)) := by
  decide

def sltiInstruction : AluInstruction :=
  { word := sltiWord, op := .slt, rd := 3, src1 := .reg 4, src2 := .imm 100,
    decode := alu_imm_decodes.1 }
def sltiuInstruction : AluInstruction :=
  { word := sltiuWord, op := .sltu, rd := 5, src1 := .reg 6, src2 := .imm 100,
    decode := alu_imm_decodes.2.1 }
def xoriInstruction : AluInstruction :=
  { word := xoriWord, op := .xor, rd := 7, src1 := .reg 8, src2 := .imm 2047,
    decode := alu_imm_decodes.2.2.1 }
def oriInstruction : AluInstruction :=
  { word := oriWord, op := .or, rd := 9, src1 := .reg 10, src2 := .imm 0xFFFFF800,
    decode := alu_imm_decodes.2.2.2.1 }
def andiInstruction : AluInstruction :=
  { word := andiWord, op := .and, rd := 11, src1 := .reg 12, src2 := .imm 255,
    decode := alu_imm_decodes.2.2.2.2.1 }
def slliInstruction : AluInstruction :=
  { word := slliWord, op := .sll, rd := 13, src1 := .reg 14, src2 := .imm 31,
    decode := alu_imm_decodes.2.2.2.2.2.1 }
def srliInstruction : AluInstruction :=
  { word := srliWord, op := .srl, rd := 15, src1 := .reg 16, src2 := .imm 1,
    decode := alu_imm_decodes.2.2.2.2.2.2.1 }
def sraiInstruction : AluInstruction :=
  { word := sraiWord, op := .sra, rd := 17, src1 := .reg 18, src2 := .imm 7,
    decode := alu_imm_decodes.2.2.2.2.2.2.2.1 }
def addiNegInstruction : AluInstruction :=
  { word := addiNegWord, op := .add, rd := 1, src1 := .reg 2,
    src2 := .imm 0xFFFFFFFB, decode := alu_imm_decodes.2.2.2.2.2.2.2.2 }

theorem alu_imm_loaded_rv32i_boundary_of_step
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

theorem picorv32_slti_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation}
    {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sltiWord .slt 3 (.reg 4) (.imm 100)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .slt 3 (.reg 4) (.imm 100), memory := input.memory } (aluRetirement arch input .slt 3 (.reg 4) (.imm 100)) := by
  simpa [sltiInstruction] using alu_imm_loaded_rv32i_boundary_of_step sltiInstruction hstep hdecode hboundary

theorem picorv32_sltiu_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sltiuWord .sltu 5 (.reg 6) (.imm 100)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .sltu 5 (.reg 6) (.imm 100), memory := input.memory } (aluRetirement arch input .sltu 5 (.reg 6) (.imm 100)) := by
  simpa [sltiuInstruction] using alu_imm_loaded_rv32i_boundary_of_step sltiuInstruction hstep hdecode hboundary

theorem picorv32_xori_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input xoriWord .xor 7 (.reg 8) (.imm 2047)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .xor 7 (.reg 8) (.imm 2047), memory := input.memory } (aluRetirement arch input .xor 7 (.reg 8) (.imm 2047)) := by
  simpa [xoriInstruction] using alu_imm_loaded_rv32i_boundary_of_step xoriInstruction hstep hdecode hboundary

theorem picorv32_ori_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input oriWord .or 9 (.reg 10) (.imm 0xFFFFF800)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .or 9 (.reg 10) (.imm 0xFFFFF800), memory := input.memory } (aluRetirement arch input .or 9 (.reg 10) (.imm 0xFFFFF800)) := by
  simpa [oriInstruction] using alu_imm_loaded_rv32i_boundary_of_step oriInstruction hstep hdecode hboundary

theorem picorv32_andi_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input andiWord .and 11 (.reg 12) (.imm 255)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .and 11 (.reg 12) (.imm 255), memory := input.memory } (aluRetirement arch input .and 11 (.reg 12) (.imm 255)) := by
  simpa [andiInstruction] using alu_imm_loaded_rv32i_boundary_of_step andiInstruction hstep hdecode hboundary

theorem picorv32_slli_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input slliWord .sll 13 (.reg 14) (.imm 31)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .sll 13 (.reg 14) (.imm 31), memory := input.memory } (aluRetirement arch input .sll 13 (.reg 14) (.imm 31)) := by
  simpa [slliInstruction] using alu_imm_loaded_rv32i_boundary_of_step slliInstruction hstep hdecode hboundary

theorem picorv32_srli_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input srliWord .srl 15 (.reg 16) (.imm 1)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .srl 15 (.reg 16) (.imm 1), memory := input.memory } (aluRetirement arch input .srl 15 (.reg 16) (.imm 1)) := by
  simpa [srliInstruction] using alu_imm_loaded_rv32i_boundary_of_step srliInstruction hstep hdecode hboundary

theorem picorv32_srai_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input sraiWord .sra 17 (.reg 18) (.imm 7)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .sra 17 (.reg 18) (.imm 7), memory := input.memory } (aluRetirement arch input .sra 17 (.reg 18) (.imm 7)) := by
  simpa [sraiInstruction] using alu_imm_loaded_rv32i_boundary_of_step sraiInstruction hstep hdecode hboundary

theorem picorv32_addi_neg_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.aluBoundary arch input addiNegWord .add 1 (.reg 2) (.imm 0xFFFFFFFB)) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := aluNext arch .add 1 (.reg 2) (.imm 0xFFFFFFFB), memory := input.memory } (aluRetirement arch input .add 1 (.reg 2) (.imm 0xFFFFFFFB)) := by
  simpa [addiNegInstruction] using alu_imm_loaded_rv32i_boundary_of_step addiNegInstruction hstep hdecode hboundary

theorem picorv32_slti_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltiWord) 0 =
      (aluNext state .slt 3 (.reg 4) (.imm 100), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltiWord .slt 3
    (.reg 4) (.imm 100) alu_imm_decodes.1

theorem picorv32_slti_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltiWord, memory := memory, irq := 0 } =
      (aluNext state .slt 3 (.reg 4) (.imm 100),
        aluRetirement state
          { fetched := .word sltiWord, memory := memory, irq := 0 }
          .slt 3 (.reg 4) (.imm 100)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltiWord .slt 3
    (.reg 4) (.imm 100) alu_imm_decodes.1

theorem picorv32_sltiu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sltiuWord) 0 =
      (aluNext state .sltu 5 (.reg 6) (.imm 100), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sltiuWord .sltu 5
    (.reg 6) (.imm 100) alu_imm_decodes.2.1

theorem picorv32_sltiu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sltiuWord, memory := memory, irq := 0 } =
      (aluNext state .sltu 5 (.reg 6) (.imm 100),
        aluRetirement state
          { fetched := .word sltiuWord, memory := memory, irq := 0 }
          .sltu 5 (.reg 6) (.imm 100)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sltiuWord .sltu 5
    (.reg 6) (.imm 100) alu_imm_decodes.2.1

theorem picorv32_xori_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word xoriWord) 0 =
      (aluNext state .xor 7 (.reg 8) (.imm 2047), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory xoriWord .xor 7
    (.reg 8) (.imm 2047) alu_imm_decodes.2.2.1

theorem picorv32_xori_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word xoriWord, memory := memory, irq := 0 } =
      (aluNext state .xor 7 (.reg 8) (.imm 2047),
        aluRetirement state
          { fetched := .word xoriWord, memory := memory, irq := 0 }
          .xor 7 (.reg 8) (.imm 2047)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory xoriWord .xor 7
    (.reg 8) (.imm 2047) alu_imm_decodes.2.2.1

theorem picorv32_ori_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word oriWord) 0 =
      (aluNext state .or 9 (.reg 10) (.imm 0xFFFFF800), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory oriWord .or 9
    (.reg 10) (.imm 0xFFFFF800) alu_imm_decodes.2.2.2.1

theorem picorv32_ori_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word oriWord, memory := memory, irq := 0 } =
      (aluNext state .or 9 (.reg 10) (.imm 0xFFFFF800),
        aluRetirement state
          { fetched := .word oriWord, memory := memory, irq := 0 }
          .or 9 (.reg 10) (.imm 0xFFFFF800)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory oriWord .or 9
    (.reg 10) (.imm 0xFFFFF800) alu_imm_decodes.2.2.2.1

theorem picorv32_andi_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word andiWord) 0 =
      (aluNext state .and 11 (.reg 12) (.imm 255), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory andiWord .and 11
    (.reg 12) (.imm 255) alu_imm_decodes.2.2.2.2.1

theorem picorv32_andi_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word andiWord, memory := memory, irq := 0 } =
      (aluNext state .and 11 (.reg 12) (.imm 255),
        aluRetirement state
          { fetched := .word andiWord, memory := memory, irq := 0 }
          .and 11 (.reg 12) (.imm 255)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory andiWord .and 11
    (.reg 12) (.imm 255) alu_imm_decodes.2.2.2.2.1

theorem picorv32_slli_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word slliWord) 0 =
      (aluNext state .sll 13 (.reg 14) (.imm 31), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory slliWord .sll 13
    (.reg 14) (.imm 31) alu_imm_decodes.2.2.2.2.2.1

theorem picorv32_slli_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word slliWord, memory := memory, irq := 0 } =
      (aluNext state .sll 13 (.reg 14) (.imm 31),
        aluRetirement state
          { fetched := .word slliWord, memory := memory, irq := 0 }
          .sll 13 (.reg 14) (.imm 31)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory slliWord .sll 13
    (.reg 14) (.imm 31) alu_imm_decodes.2.2.2.2.2.1

theorem picorv32_srli_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word srliWord) 0 =
      (aluNext state .srl 15 (.reg 16) (.imm 1), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory srliWord .srl 15
    (.reg 16) (.imm 1) alu_imm_decodes.2.2.2.2.2.2.1

theorem picorv32_srli_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word srliWord, memory := memory, irq := 0 } =
      (aluNext state .srl 15 (.reg 16) (.imm 1),
        aluRetirement state
          { fetched := .word srliWord, memory := memory, irq := 0 }
          .srl 15 (.reg 16) (.imm 1)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory srliWord .srl 15
    (.reg 16) (.imm 1) alu_imm_decodes.2.2.2.2.2.2.1

theorem picorv32_srai_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sraiWord) 0 =
      (aluNext state .sra 17 (.reg 18) (.imm 7), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory sraiWord .sra 17
    (.reg 18) (.imm 7) alu_imm_decodes.2.2.2.2.2.2.2.1

theorem picorv32_srai_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sraiWord, memory := memory, irq := 0 } =
      (aluNext state .sra 17 (.reg 18) (.imm 7),
        aluRetirement state
          { fetched := .word sraiWord, memory := memory, irq := 0 }
          .sra 17 (.reg 18) (.imm 7)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory sraiWord .sra 17
    (.reg 18) (.imm 7) alu_imm_decodes.2.2.2.2.2.2.2.1

theorem picorv32_addi_neg_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word addiNegWord) 0 =
      (aluNext state .add 1 (.reg 2) (.imm 0xFFFFFFFB), memory) := by
  exact isaStepMemWith_alu cv32e40pProfile state memory addiNegWord .add 1
    (.reg 2) (.imm 0xFFFFFFFB) alu_imm_decodes.2.2.2.2.2.2.2.2

theorem picorv32_addi_neg_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word addiNegWord, memory := memory, irq := 0 } =
      (aluNext state .add 1 (.reg 2) (.imm 0xFFFFFFFB),
        aluRetirement state
          { fetched := .word addiNegWord, memory := memory, irq := 0 }
          .add 1 (.reg 2) (.imm 0xFFFFFFFB)) := by
  exact rvMachineWith_alu cv32e40pProfile state memory addiNegWord .add 1
    (.reg 2) (.imm 0xFFFFFFFB) alu_imm_decodes.2.2.2.2.2.2.2.2

#print axioms picorv32_slti_class_step
#print axioms picorv32_slti_class_commit
#print axioms picorv32_sltiu_class_step
#print axioms picorv32_sltiu_class_commit
#print axioms picorv32_xori_class_step
#print axioms picorv32_xori_class_commit
#print axioms picorv32_ori_class_step
#print axioms picorv32_ori_class_commit
#print axioms picorv32_andi_class_step
#print axioms picorv32_andi_class_commit
#print axioms picorv32_slli_class_step
#print axioms picorv32_slli_class_commit
#print axioms picorv32_srli_class_step
#print axioms picorv32_srli_class_commit
#print axioms picorv32_srai_class_step
#print axioms picorv32_srai_class_commit
#print axioms picorv32_addi_neg_class_step
#print axioms picorv32_addi_neg_class_commit

end Examples.«system-verilog».cores.picorv32.r1_alu_imm
