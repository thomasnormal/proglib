import LeanModels.Refine.RvfiCsr
import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 Zicsr class

The six RV32I Zicsr operation/source forms are represented by explicit
`CsrOpKind` values.  Their fixed words are checked by the exact decoder and
their implemented CSR rows are retained as premises before the threaded step
and retirement boundaries are applied.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_csr

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

def csrrwWord : Word := 0x340312f3
def csrrsWord : Word := 0x30002073
def csrrcWord : Word := 0x341433f3
def csrrwiWord : Word := 0x340ad2f3
def csrrsiWord : Word := 0x304fe373
def csrrciWord : Word := 0x3420f3f3

def csrrwKind : CsrOpKind :=
  { op := .rw, rd := 5, src := .reg 6, addr := 0x340 }
def csrrsKind : CsrOpKind :=
  { op := .rs, rd := 0, src := .reg 0, addr := 0x300 }
def csrrcKind : CsrOpKind :=
  { op := .rc, rd := 7, src := .reg 8, addr := 0x341 }
def csrrwiKind : CsrOpKind :=
  { op := .rw, rd := 5, src := .imm 21, addr := 0x340 }
def csrrsiKind : CsrOpKind :=
  { op := .rs, rd := 6, src := .imm 31, addr := 0x304 }
def csrrciKind : CsrOpKind :=
  { op := .rc, rd := 7, src := .imm 1, addr := 0x342 }

def mscratchRow : CsrBehavior := csrTable[3]'(by decide)
def mstatusRow : CsrBehavior := csrTable[0]'(by decide)
def mieRow : CsrBehavior := csrTable[1]'(by decide)
def mepcRow : CsrBehavior := csrTable[4]'(by decide)
def mcauseRow : CsrBehavior := csrTable[5]'(by decide)

theorem csrrw_decode :
    Fetched.decode (.word csrrwWord) = some csrrwKind.toInstr := by
  decide

theorem csrrs_decode :
    Fetched.decode (.word csrrsWord) = some csrrsKind.toInstr := by
  decide

theorem csrrc_decode :
    Fetched.decode (.word csrrcWord) = some csrrcKind.toInstr := by
  decide

theorem csrrwi_decode :
    Fetched.decode (.word csrrwiWord) = some csrrwiKind.toInstr := by
  decide

theorem csrrsi_decode :
    Fetched.decode (.word csrrsiWord) = some csrrsiKind.toInstr := by
  decide

theorem csrrci_decode :
    Fetched.decode (.word csrrciWord) = some csrrciKind.toInstr := by
  decide

theorem csrrw_row : findCsr? csrrwKind.addr = some mscratchRow := by
  rfl

theorem csrrs_row : findCsr? csrrsKind.addr = some mstatusRow := by
  rfl

theorem csrrc_row : findCsr? csrrcKind.addr = some mepcRow := by
  rfl

theorem csrrwi_row : findCsr? csrrwiKind.addr = some mscratchRow := by
  rfl

theorem csrrsi_row : findCsr? csrrsiKind.addr = some mieRow := by
  rfl

theorem csrrci_row : findCsr? csrrciKind.addr = some mcauseRow := by
  rfl

def csrrwInstruction : CsrInstruction :=
  { word := csrrwWord, kind := csrrwKind, row := mscratchRow,
    decode := csrrw_decode, rowLookup := csrrw_row }
def csrrsInstruction : CsrInstruction :=
  { word := csrrsWord, kind := csrrsKind, row := mstatusRow,
    decode := csrrs_decode, rowLookup := csrrs_row }
def csrrcInstruction : CsrInstruction :=
  { word := csrrcWord, kind := csrrcKind, row := mepcRow,
    decode := csrrc_decode, rowLookup := csrrc_row }
def csrrwiInstruction : CsrInstruction :=
  { word := csrrwiWord, kind := csrrwiKind, row := mscratchRow,
    decode := csrrwi_decode, rowLookup := csrrwi_row }
def csrrsiInstruction : CsrInstruction :=
  { word := csrrsiWord, kind := csrrsiKind, row := mieRow,
    decode := csrrsi_decode, rowLookup := csrrsi_row }
def csrrciInstruction : CsrInstruction :=
  { word := csrrciWord, kind := csrrciKind, row := mcauseRow,
    decode := csrrci_decode, rowLookup := csrrci_row }

/-! The raw CSR fields determine the exact implemented-row ISA step.  The
    explicit row lookup premise keeps unimplemented addresses on the separate
    illegal-instruction path. -/

theorem picorv32_csr_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (row : CsrBehavior)
    (kind : CsrOpKind)
    (hfields : observation.csrFields state input word row kind) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (csrNext state row kind, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) = some kind.toInstr :=
    hfields.2.2.1
  have hrow : findCsr? kind.addr = some row := hfields.2.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_csr profile state memory word row kind hdecode hrow

#print axioms picorv32_csr_fields_isa_step

theorem csr_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (instruction : CsrInstruction)
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input instruction.word instruction.row instruction.kind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation'
        { arch := csrNext arch instruction.row instruction.kind, memory := input.memory }
        (csrRetirement arch input instruction.row instruction.kind) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  exact rvfi_core_adapter.CoreCsrBoundary.to_rv32i_boundary
    (⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode,
      hboundary⟩ : rvfi_core_adapter.CoreCsrBoundary d st entry arch input instruction)

/-! The implemented Zicsr family has one exact-cycle consumer.  The retained
    `CsrInstruction` carries both the operation and the checked table row into
    the mixed dispatcher, leaving absent CSR rows on the illegal path. -/

theorem picorv32_csr_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : CsrInstruction)
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
            input = csrProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.csrBoundary memoryState.arch input instruction.word
              instruction.row instruction.kind ∧
            rel next
              { arch := csrNext memoryState.arch instruction.row instruction.kind,
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
          (rv32iProgramStep memoryState (.csr instruction))
          (rv32iProgramRetirement memoryState (.csr instruction)) := by
        simpa [hmem, hinput, csrProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.csrBoundary_rv32i instruction.word instruction.row
            instruction.kind hboundary)
      simp only [↓reduceIte]
      exact ⟨.csr instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, hnext⟩

#print axioms picorv32_csr_exact_cycle_step_refines

/-! The loaded CSR consumer packages one exact implemented Zicsr operation
    into the reset-specialized all-prefix contract. -/

theorem picorv32_loaded_csr_program_refinement_of_total
    (core : PicoRV32LoadedCanonicalE)
    (profile : PlatformProfile)
    (program : Memory)
    (initialArch : ArchState)
    (hpc : initialArch.pc = 0)
    (hwf : initialArch.WF)
    (instruction : CsrInstruction)
    (encode : LeanModels.Sv.Kernel.CoreMemState → Input → SvState)
    (htotal : ∀ (state : LeanModels.Sv.Kernel.CoreMemState) (input : Input),
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core)
              state (encode state input) = .ok (next, observation))
    {rel : LeanModels.Sv.Kernel.CoreMemState → RvMemoryState → Prop}
    {admit : Input → Prop}
    (hstep : ∀ (start : Nat)
      (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      ∃ next : LeanModels.Sv.Kernel.CoreMemState,
        ∃ observation : RvfiObservation,
          rvfi_core_adapter.rvfiStep (PicoRV32LoadedCanonicalE.design core)
              state (encode state input) = .ok (next, observation) ∧
          (if observation.valid then
            input = csrProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.csrBoundary memoryState.arch input instruction.word
              instruction.row instruction.kind ∧
            rel next
              { arch := csrNext memoryState.arch instruction.row instruction.kind,
                memory := memoryState.memory }
          else rel next memoryState))
    (hrel : ∀ (state : LeanModels.Sv.Kernel.CoreMemState)
      (memoryState : RvMemoryState),
      PicoRV32ResetRelation
        (PicoRV32LoadedCanonicalE.design core) program state memoryState →
      rel state memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    (progress : Rv32iRetiresTarget
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal))
      (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine
        (rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal)).init
      schedule target) :
    ∃ machine : rvfi_core_adapter.CoreRvfiMachine
        (PicoRV32LoadedCanonicalE.design core),
      picorv32_core_mem = .ok (PicoRV32LoadedCanonicalE.design core) ∧
      Rv32iAllPrefixRefinement profile
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine machine)
        rel 0
        (rvfi_core_adapter.CoreRvfiMachine.toRvfiCycleMachine machine).init
        { arch := initialArch, memory := program } schedule target := by
  let machine := rvfi_core_adapter.CoreRvfiMachine.ofTotal encode htotal
  have hstep' := picorv32_csr_exact_cycle_step_refines machine instruction hstep
  have hinitial : rel machine.toRvfiCycleMachine.init
      { arch := initialArch, memory := program } :=
    hrel _ _ (picoRV32_reset_relation_initial
      (PicoRV32LoadedCanonicalE.design core) program initialArch hpc hwf)
  refine ⟨machine, PicoRV32LoadedCanonicalE.loaded core, ?_⟩
  exact rv32i_progress_refinement profile machine.toRvfiCycleMachine rel admit
    hstep' 0 _ _ hinitial hschedule progress

#print axioms picorv32_loaded_csr_program_refinement_of_total

theorem picorv32_csrrw_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrwWord mscratchRow csrrwKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mscratchRow csrrwKind, memory := input.memory } (csrRetirement arch input mscratchRow csrrwKind) := by
  simpa [csrrwInstruction] using csr_loaded_rv32i_boundary_of_step csrrwInstruction hstep hdecode hboundary

theorem picorv32_csrrs_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrsWord mstatusRow csrrsKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mstatusRow csrrsKind, memory := input.memory } (csrRetirement arch input mstatusRow csrrsKind) := by
  simpa [csrrsInstruction] using csr_loaded_rv32i_boundary_of_step csrrsInstruction hstep hdecode hboundary

theorem picorv32_csrrc_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrcWord mepcRow csrrcKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mepcRow csrrcKind, memory := input.memory } (csrRetirement arch input mepcRow csrrcKind) := by
  simpa [csrrcInstruction] using csr_loaded_rv32i_boundary_of_step csrrcInstruction hstep hdecode hboundary

theorem picorv32_csrrwi_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrwiWord mscratchRow csrrwiKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mscratchRow csrrwiKind, memory := input.memory } (csrRetirement arch input mscratchRow csrrwiKind) := by
  simpa [csrrwiInstruction] using csr_loaded_rv32i_boundary_of_step csrrwiInstruction hstep hdecode hboundary

theorem picorv32_csrrsi_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrsiWord mieRow csrrsiKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mieRow csrrsiKind, memory := input.memory } (csrRetirement arch input mieRow csrrsiKind) := by
  simpa [csrrsiInstruction] using csr_loaded_rv32i_boundary_of_step csrrsiInstruction hstep hdecode hboundary

theorem picorv32_csrrci_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.csrBoundary arch input csrrciWord mcauseRow csrrciKind) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := csrNext arch mcauseRow csrrciKind, memory := input.memory } (csrRetirement arch input mcauseRow csrrciKind) := by
  simpa [csrrciInstruction] using csr_loaded_rv32i_boundary_of_step csrrciInstruction hstep hdecode hboundary

#print axioms picorv32_csrrw_loaded_rv32i_boundary_of_step
#print axioms picorv32_csrrs_loaded_rv32i_boundary_of_step
#print axioms picorv32_csrrc_loaded_rv32i_boundary_of_step
#print axioms picorv32_csrrwi_loaded_rv32i_boundary_of_step
#print axioms picorv32_csrrsi_loaded_rv32i_boundary_of_step
#print axioms picorv32_csrrci_loaded_rv32i_boundary_of_step

theorem picorv32_csrrw_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrwWord) 0 =
      (csrNext state mscratchRow csrrwKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrwWord
    mscratchRow csrrwKind csrrw_decode csrrw_row

theorem picorv32_csrrw_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrwWord, memory := memory, irq := 0 } =
      (csrNext state mscratchRow csrrwKind,
        csrRetirement state
          { fetched := .word csrrwWord, memory := memory, irq := 0 }
          mscratchRow csrrwKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrwWord
    mscratchRow csrrwKind csrrw_decode csrrw_row

theorem picorv32_csrrs_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrsWord) 0 =
      (csrNext state mstatusRow csrrsKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrsWord
    mstatusRow csrrsKind csrrs_decode csrrs_row

theorem picorv32_csrrs_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrsWord, memory := memory, irq := 0 } =
      (csrNext state mstatusRow csrrsKind,
        csrRetirement state
          { fetched := .word csrrsWord, memory := memory, irq := 0 }
          mstatusRow csrrsKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrsWord
    mstatusRow csrrsKind csrrs_decode csrrs_row

theorem picorv32_csrrc_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrcWord) 0 =
      (csrNext state mepcRow csrrcKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrcWord
    mepcRow csrrcKind csrrc_decode csrrc_row

theorem picorv32_csrrc_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrcWord, memory := memory, irq := 0 } =
      (csrNext state mepcRow csrrcKind,
        csrRetirement state
          { fetched := .word csrrcWord, memory := memory, irq := 0 }
          mepcRow csrrcKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrcWord
    mepcRow csrrcKind csrrc_decode csrrc_row

theorem picorv32_csrrwi_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrwiWord) 0 =
      (csrNext state mscratchRow csrrwiKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrwiWord
    mscratchRow csrrwiKind csrrwi_decode csrrwi_row

theorem picorv32_csrrwi_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrwiWord, memory := memory, irq := 0 } =
      (csrNext state mscratchRow csrrwiKind,
        csrRetirement state
          { fetched := .word csrrwiWord, memory := memory, irq := 0 }
          mscratchRow csrrwiKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrwiWord
    mscratchRow csrrwiKind csrrwi_decode csrrwi_row

theorem picorv32_csrrsi_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrsiWord) 0 =
      (csrNext state mieRow csrrsiKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrsiWord
    mieRow csrrsiKind csrrsi_decode csrrsi_row

theorem picorv32_csrrsi_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrsiWord, memory := memory, irq := 0 } =
      (csrNext state mieRow csrrsiKind,
        csrRetirement state
          { fetched := .word csrrsiWord, memory := memory, irq := 0 }
          mieRow csrrsiKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrsiWord
    mieRow csrrsiKind csrrsi_decode csrrsi_row

theorem picorv32_csrrci_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word csrrciWord) 0 =
      (csrNext state mcauseRow csrrciKind, memory) := by
  exact isaStepMemWith_csr cv32e40pProfile state memory csrrciWord
    mcauseRow csrrciKind csrrci_decode csrrci_row

theorem picorv32_csrrci_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word csrrciWord, memory := memory, irq := 0 } =
      (csrNext state mcauseRow csrrciKind,
        csrRetirement state
          { fetched := .word csrrciWord, memory := memory, irq := 0 }
          mcauseRow csrrciKind) := by
  exact rvMachineWith_csr cv32e40pProfile state memory csrrciWord
    mcauseRow csrrciKind csrrci_decode csrrci_row

#print axioms picorv32_csrrw_class_step
#print axioms picorv32_csrrw_class_commit
#print axioms picorv32_csrrs_class_step
#print axioms picorv32_csrrs_class_commit
#print axioms picorv32_csrrc_class_step
#print axioms picorv32_csrrc_class_commit
#print axioms picorv32_csrrwi_class_step
#print axioms picorv32_csrrwi_class_commit
#print axioms picorv32_csrrsi_class_step
#print axioms picorv32_csrrsi_class_commit
#print axioms picorv32_csrrci_class_step
#print axioms picorv32_csrrci_class_commit

end Examples.«system-verilog».cores.picorv32.r1_csr
