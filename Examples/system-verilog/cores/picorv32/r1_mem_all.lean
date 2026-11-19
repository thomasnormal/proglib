import LeanModels.Refine.RvfiMemAll
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 complete memory class

The RV32I memory family has five loads and three stores across byte, halfword,
and word widths.  These fixed words are checked by the exact decoder, then
threaded through the generic byte-memory step and retirement boundary for
arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_mem_all

open LeanModels.Rv
open LeanModels.Refine

def lbWord : Word := 0x10008183
def lhWord : Word := 0x10009183
def lwWord : Word := 0x1000a183
def lbuWord : Word := 0x1000c183
def lhuWord : Word := 0x1000d183
def sbWord : Word := 0x10308023
def shWord : Word := 0x10309023
def swWord : Word := 0x1030a023

theorem lbWord_decode :
    Fetched.decode (.word lbWord) =
      some (.mem (.load true) .byte 3 1 0x100) := by
  decide

theorem lhWord_decode :
    Fetched.decode (.word lhWord) =
      some (.mem (.load true) .half 3 1 0x100) := by
  decide

theorem lwWord_decode :
    Fetched.decode (.word lwWord) =
      some (.mem (.load true) .word 3 1 0x100) := by
  decide

theorem lbuWord_decode :
    Fetched.decode (.word lbuWord) =
      some (.mem (.load false) .byte 3 1 0x100) := by
  decide

theorem lhuWord_decode :
    Fetched.decode (.word lhuWord) =
      some (.mem (.load false) .half 3 1 0x100) := by
  decide

theorem sbWord_decode :
    Fetched.decode (.word sbWord) =
      some (.mem .store .byte 3 1 0x100) := by
  decide

theorem shWord_decode :
    Fetched.decode (.word shWord) =
      some (.mem .store .half 3 1 0x100) := by
  decide

theorem swWord_decode :
    Fetched.decode (.word swWord) =
      some (.mem .store .word 3 1 0x100) := by
  decide

def lbInstruction : MemInstruction :=
  { word := lbWord, kind := .load true .byte, r := 3, rs1 := 1, imm := 0x100, decode := lbWord_decode }
def lhInstruction : MemInstruction :=
  { word := lhWord, kind := .load true .half, r := 3, rs1 := 1, imm := 0x100, decode := lhWord_decode }
def lwInstruction : MemInstruction :=
  { word := lwWord, kind := .load true .word, r := 3, rs1 := 1, imm := 0x100, decode := lwWord_decode }
def lbuInstruction : MemInstruction :=
  { word := lbuWord, kind := .load false .byte, r := 3, rs1 := 1, imm := 0x100, decode := lbuWord_decode }
def lhuInstruction : MemInstruction :=
  { word := lhuWord, kind := .load false .half, r := 3, rs1 := 1, imm := 0x100, decode := lhuWord_decode }
def sbInstruction : MemInstruction :=
  { word := sbWord, kind := .store .byte, r := 3, rs1 := 1, imm := 0x100, decode := sbWord_decode }
def shInstruction : MemInstruction :=
  { word := shWord, kind := .store .half, r := 3, rs1 := 1, imm := 0x100, decode := shWord_decode }
def swInstruction : MemInstruction :=
  { word := swWord, kind := .store .word, r := 3, rs1 := 1, imm := 0x100, decode := swWord_decode }

/-! The common raw memory fields determine the exact threaded ISA step for
    every width and load signedness.  The generic `MemOp` keeps those choices
    explicit, so this bridge does not duplicate a mini-language per row. -/

theorem picorv32_mem_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (kind : MemOp)
    (r rs1 : Reg) (imm : Word)
    (hfields : observation.memFields state input word kind r rs1 imm) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (memNext state input.memory kind r rs1 imm,
        memAfter input.memory state kind r rs1 imm) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (kind.toInstr r rs1 imm) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_mem profile state memory word kind r rs1 imm hdecode

#print axioms picorv32_mem_fields_isa_step

theorem mem_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (instruction : MemInstruction)
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.memBoundary arch input instruction.word instruction.kind
      instruction.r instruction.rs1 instruction.imm) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := memNext arch input.memory instruction.kind instruction.r instruction.rs1 instruction.imm,
          memory := memAfter input.memory arch instruction.kind instruction.r instruction.rs1 instruction.imm }
        (memRetirement arch input instruction.kind instruction.r instruction.rs1 instruction.imm) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  exact rvfi_core_adapter.CoreMemBoundary.to_rv32i_boundary
    (⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreMemBoundary d st entry arch input instruction)

/-! The complete load/store family has one exact-cycle consumer.  The
    retained `MemInstruction` carries width, signedness, registers, and the
    decoder proof into the mixed dispatcher while threading the post-memory
    state explicitly. -/

theorem picorv32_mem_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : MemInstruction)
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
            input = memProgramInput memoryState instruction ∧
            observation.order = start ∧
            observation.memBoundary memoryState.arch input instruction.word
              instruction.kind instruction.r instruction.rs1 instruction.imm ∧
            rel next (memProgramStep memoryState instruction)
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
          (rv32iProgramStep memoryState (.memory instruction))
          (rv32iProgramRetirement memoryState (.memory instruction)) := by
        simpa [hmem, hinput, memProgramInput, memProgramStep,
          rv32iProgramStep, rv32iProgramRetirement] using
          (Rv32iBoundary.mem instruction.word instruction.kind instruction.r
            instruction.rs1 instruction.imm hboundary)
      simp only [↓reduceIte]
      exact ⟨.memory instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, hnext⟩

#print axioms picorv32_mem_exact_cycle_step_refines

theorem picorv32_lb_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.memBoundary arch input lbWord (.load true .byte) 3 1 0x100) :
    ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.load true .byte) 3 1 0x100, memory := memAfter input.memory arch (.load true .byte) 3 1 0x100 } (memRetirement arch input (.load true .byte) 3 1 0x100) := by
  simpa [lbInstruction] using mem_loaded_rv32i_boundary_of_step lbInstruction hstep hdecode hboundary

theorem picorv32_lh_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input lhWord (.load true .half) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.load true .half) 3 1 0x100, memory := memAfter input.memory arch (.load true .half) 3 1 0x100 } (memRetirement arch input (.load true .half) 3 1 0x100) := by simpa [lhInstruction] using mem_loaded_rv32i_boundary_of_step lhInstruction hstep hdecode hboundary
theorem picorv32_lw_all_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input lwWord (.load true .word) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.load true .word) 3 1 0x100, memory := memAfter input.memory arch (.load true .word) 3 1 0x100 } (memRetirement arch input (.load true .word) 3 1 0x100) := by simpa [lwInstruction] using mem_loaded_rv32i_boundary_of_step lwInstruction hstep hdecode hboundary
theorem picorv32_lbu_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input lbuWord (.load false .byte) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.load false .byte) 3 1 0x100, memory := memAfter input.memory arch (.load false .byte) 3 1 0x100 } (memRetirement arch input (.load false .byte) 3 1 0x100) := by simpa [lbuInstruction] using mem_loaded_rv32i_boundary_of_step lbuInstruction hstep hdecode hboundary
theorem picorv32_lhu_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input lhuWord (.load false .half) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.load false .half) 3 1 0x100, memory := memAfter input.memory arch (.load false .half) 3 1 0x100 } (memRetirement arch input (.load false .half) 3 1 0x100) := by simpa [lhuInstruction] using mem_loaded_rv32i_boundary_of_step lhuInstruction hstep hdecode hboundary
theorem picorv32_sb_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input sbWord (.store .byte) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.store .byte) 3 1 0x100, memory := memAfter input.memory arch (.store .byte) 3 1 0x100 } (memRetirement arch input (.store .byte) 3 1 0x100) := by simpa [sbInstruction] using mem_loaded_rv32i_boundary_of_step sbInstruction hstep hdecode hboundary
theorem picorv32_sh_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input shWord (.store .half) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.store .half) 3 1 0x100, memory := memAfter input.memory arch (.store .half) 3 1 0x100 } (memRetirement arch input (.store .half) 3 1 0x100) := by simpa [shInstruction] using mem_loaded_rv32i_boundary_of_step shInstruction hstep hdecode hboundary
theorem picorv32_sw_all_loaded_rv32i_boundary_of_step {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input} (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation) (hboundary : observation.memBoundary arch input swWord (.store .word) 3 1 0x100) : ∃ n o, rvfi_core_adapter.rvfiStep d st entry = .ok (n, o) ∧ Rv32iBoundary arch input o { arch := memNext arch input.memory (.store .word) 3 1 0x100, memory := memAfter input.memory arch (.store .word) 3 1 0x100 } (memRetirement arch input (.store .word) 3 1 0x100) := by simpa [swInstruction] using mem_loaded_rv32i_boundary_of_step swInstruction hstep hdecode hboundary

theorem picorv32_lb_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lbWord) 0 =
      (memNext state memory (.load true .byte) 3 1 0x100,
        memAfter memory state (.load true .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lbWord
    (.load true .byte) 3 1 0x100 lbWord_decode

theorem picorv32_lb_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lbWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word lbWord, memory := memory, irq := 0 }
          (.load true .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lbWord
    (.load true .byte) 3 1 0x100 lbWord_decode

theorem picorv32_lh_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lhWord) 0 =
      (memNext state memory (.load true .half) 3 1 0x100,
        memAfter memory state (.load true .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lhWord
    (.load true .half) 3 1 0x100 lhWord_decode

theorem picorv32_lh_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lhWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .half) 3 1 0x100,
        memRetirement state
          { fetched := .word lhWord, memory := memory, irq := 0 }
          (.load true .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lhWord
    (.load true .half) 3 1 0x100 lhWord_decode

theorem picorv32_lw_all_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lwWord) 0 =
      (memNext state memory (.load true .word) 3 1 0x100,
        memAfter memory state (.load true .word) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lwWord
    (.load true .word) 3 1 0x100 lwWord_decode

theorem picorv32_lw_all_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lwWord, memory := memory, irq := 0 } =
      (memNext state memory (.load true .word) 3 1 0x100,
        memRetirement state
          { fetched := .word lwWord, memory := memory, irq := 0 }
          (.load true .word) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lwWord
    (.load true .word) 3 1 0x100 lwWord_decode

theorem picorv32_lbu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lbuWord) 0 =
      (memNext state memory (.load false .byte) 3 1 0x100,
        memAfter memory state (.load false .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lbuWord
    (.load false .byte) 3 1 0x100 lbuWord_decode

theorem picorv32_lbu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lbuWord, memory := memory, irq := 0 } =
      (memNext state memory (.load false .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word lbuWord, memory := memory, irq := 0 }
          (.load false .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lbuWord
    (.load false .byte) 3 1 0x100 lbuWord_decode

theorem picorv32_lhu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word lhuWord) 0 =
      (memNext state memory (.load false .half) 3 1 0x100,
        memAfter memory state (.load false .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory lhuWord
    (.load false .half) 3 1 0x100 lhuWord_decode

theorem picorv32_lhu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word lhuWord, memory := memory, irq := 0 } =
      (memNext state memory (.load false .half) 3 1 0x100,
        memRetirement state
          { fetched := .word lhuWord, memory := memory, irq := 0 }
          (.load false .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory lhuWord
    (.load false .half) 3 1 0x100 lhuWord_decode

theorem picorv32_sb_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word sbWord) 0 =
      (memNext state memory (.store .byte) 3 1 0x100,
        memAfter memory state (.store .byte) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory sbWord
    (.store .byte) 3 1 0x100 sbWord_decode

theorem picorv32_sb_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word sbWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .byte) 3 1 0x100,
        memRetirement state
          { fetched := .word sbWord, memory := memory, irq := 0 }
          (.store .byte) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory sbWord
    (.store .byte) 3 1 0x100 sbWord_decode

theorem picorv32_sh_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word shWord) 0 =
      (memNext state memory (.store .half) 3 1 0x100,
        memAfter memory state (.store .half) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory shWord
    (.store .half) 3 1 0x100 shWord_decode

theorem picorv32_sh_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word shWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .half) 3 1 0x100,
        memRetirement state
          { fetched := .word shWord, memory := memory, irq := 0 }
          (.store .half) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory shWord
    (.store .half) 3 1 0x100 shWord_decode

theorem picorv32_sw_all_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word swWord) 0 =
      (memNext state memory (.store .word) 3 1 0x100,
        memAfter memory state (.store .word) 3 1 0x100) := by
  exact isaStepMemWith_mem cv32e40pProfile state memory swWord
    (.store .word) 3 1 0x100 swWord_decode

theorem picorv32_sw_all_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word swWord, memory := memory, irq := 0 } =
      (memNext state memory (.store .word) 3 1 0x100,
        memRetirement state
          { fetched := .word swWord, memory := memory, irq := 0 }
          (.store .word) 3 1 0x100) := by
  exact rvMachineWith_mem cv32e40pProfile state memory swWord
    (.store .word) 3 1 0x100 swWord_decode

#print axioms picorv32_lb_class_step
#print axioms picorv32_lb_class_commit
#print axioms picorv32_lh_class_step
#print axioms picorv32_lh_class_commit
#print axioms picorv32_lw_all_class_step
#print axioms picorv32_lw_all_class_commit
#print axioms picorv32_lbu_class_step
#print axioms picorv32_lbu_class_commit
#print axioms picorv32_lhu_class_step
#print axioms picorv32_lhu_class_commit
#print axioms picorv32_sb_class_step
#print axioms picorv32_sb_class_commit
#print axioms picorv32_sh_class_step
#print axioms picorv32_sh_class_commit
#print axioms picorv32_sw_all_class_step
#print axioms picorv32_sw_all_class_commit

end Examples.«system-verilog».cores.picorv32.r1_mem_all
