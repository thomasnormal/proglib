import LeanModels.Refine.RvfiSystem
import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 system-transfer class

The no-interrupt machine-mode system family contains ECALL, EBREAK, MRET,
and WFI.  Their fixed words are checked by the exact decoder, then threaded
through the memory-preserving step and retirement boundary for arbitrary
architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_system

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

def ecallWord : Word := 0x00000073
def ebreakWord : Word := 0x00100073
def mretWord : Word := 0x30200073
def wfiWord : Word := 0x10500073

theorem system_decodes :
    Fetched.decode (.word ecallWord) = some (.system .ecall) ∧
    Fetched.decode (.word ebreakWord) = some (.system .ebreak) ∧
    Fetched.decode (.word mretWord) = some (.system .mret) ∧
    Fetched.decode (.word wfiWord) = some (.system .wfi) := by
  decide

def ecallInstruction : SystemInstruction :=
  { word := ecallWord, kind := .ecall, decode := system_decodes.1 }
def ebreakInstruction : SystemInstruction :=
  { word := ebreakWord, kind := .ebreak, decode := system_decodes.2.1 }
def mretInstruction : SystemInstruction :=
  { word := mretWord, kind := .mret, decode := system_decodes.2.2.1 }
def wfiInstruction : SystemInstruction :=
  { word := wfiWord, kind := .wfi, decode := system_decodes.2.2.2 }

theorem picorv32_ecall_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word ecallWord) 0 =
      (systemNext state .ecall, memory) := by
  exact isaStepMemWith_system cv32e40pProfile state memory ecallWord .ecall
    system_decodes.1

theorem picorv32_ecall_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word ecallWord, memory := memory, irq := 0 } =
      (systemNext state .ecall,
        systemRetirement state
          { fetched := .word ecallWord, memory := memory, irq := 0 }
          .ecall) := by
  exact rvMachineWith_system cv32e40pProfile state memory ecallWord .ecall
    system_decodes.1

theorem picorv32_ebreak_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word ebreakWord) 0 =
      (systemNext state .ebreak, memory) := by
  exact isaStepMemWith_system cv32e40pProfile state memory ebreakWord .ebreak
    system_decodes.2.1

theorem picorv32_ebreak_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word ebreakWord, memory := memory, irq := 0 } =
      (systemNext state .ebreak,
        systemRetirement state
          { fetched := .word ebreakWord, memory := memory, irq := 0 }
          .ebreak) := by
  exact rvMachineWith_system cv32e40pProfile state memory ebreakWord .ebreak
    system_decodes.2.1

theorem picorv32_mret_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word mretWord) 0 =
      (systemNext state .mret, memory) := by
  exact isaStepMemWith_system cv32e40pProfile state memory mretWord .mret
    system_decodes.2.2.1

theorem picorv32_mret_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word mretWord, memory := memory, irq := 0 } =
      (systemNext state .mret,
        systemRetirement state
          { fetched := .word mretWord, memory := memory, irq := 0 }
          .mret) := by
  exact rvMachineWith_system cv32e40pProfile state memory mretWord .mret
    system_decodes.2.2.1

theorem picorv32_wfi_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word wfiWord) 0 =
      (systemNext state .wfi, memory) := by
  exact isaStepMemWith_system cv32e40pProfile state memory wfiWord .wfi
    system_decodes.2.2.2

theorem picorv32_wfi_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word wfiWord, memory := memory, irq := 0 } =
      (systemNext state .wfi,
        systemRetirement state
          { fetched := .word wfiWord, memory := memory, irq := 0 }
          .wfi) := by
  exact rvMachineWith_system cv32e40pProfile state memory wfiWord .wfi
    system_decodes.2.2.2

/-! The raw system fields determine the exact architectural system step for
    ECALL, EBREAK, MRET, and WFI, including trap and wake behavior. -/

theorem picorv32_system_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (kind : SysKind)
    (hfields : observation.systemFields state input word kind) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (systemNext state kind, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.system kind.toSysOp) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_system profile state memory word kind hdecode

#print axioms picorv32_system_fields_isa_step

theorem picorv32_ecall_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.systemBoundary arch input ecallWord .ecall) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := systemNext arch .ecall, memory := input.memory }
        (systemRetirement arch input .ecall) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreSystemBoundary d st entry arch input ecallInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [ecallInstruction] using hboundary
  simpa [ecallInstruction] using h.to_rv32i_boundary

theorem picorv32_ebreak_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.systemBoundary arch input ebreakWord .ebreak) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := systemNext arch .ebreak, memory := input.memory } (systemRetirement arch input .ebreak) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreSystemBoundary d st entry arch input ebreakInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [ebreakInstruction] using hboundary
  simpa [ebreakInstruction] using h.to_rv32i_boundary

theorem picorv32_mret_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.systemBoundary arch input mretWord .mret) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := systemNext arch .mret, memory := input.memory } (systemRetirement arch input .mret) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreSystemBoundary d st entry arch input mretInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [mretInstruction] using hboundary
  simpa [mretInstruction] using h.to_rv32i_boundary

theorem picorv32_wfi_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState} {entry : LeanModels.Sv.SvState}
    {next : LeanModels.Sv.Kernel.CoreMemState} {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next) (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.systemBoundary arch input wfiWord .wfi) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧ Rv32iBoundary arch input observation'
      { arch := systemNext arch .wfi, memory := input.memory } (systemRetirement arch input .wfi) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreSystemBoundary d st entry arch input wfiInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [wfiInstruction] using hboundary
  simpa [wfiInstruction] using h.to_rv32i_boundary

/-! One exact-cycle consumer covers ECALL, EBREAK, MRET, and WFI.  The
    retained `SystemInstruction` keeps each trap or wake operation's precise
    semantic kind in the mixed dispatcher. -/

theorem picorv32_system_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : SystemInstruction)
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
            input = systemProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.systemBoundary memoryState.arch input instruction.word
              instruction.kind ∧
            rel next
              { arch := systemNext memoryState.arch instruction.kind,
                memory := memoryState.memory }
          else rel next memoryState)) :
    Rv32iLegacyCycleStepRefines machine.toRvfiCycleMachine rel admit := by
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
          (rv32iProgramStep memoryState (.system instruction))
          (rv32iProgramRetirement memoryState (.system instruction)) := by
        simpa [hmem, hinput, systemProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.systemBoundary_rv32i instruction.word
            instruction.kind hboundary)
      simp only [↓reduceIte]
      exact ⟨.system instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, hnext⟩

#print axioms picorv32_system_exact_cycle_step_refines

/-! The loaded system consumer packages one exact ECALL, EBREAK, MRET, or
    WFI instruction into the reset-specialized all-prefix contract. -/

end Examples.«system-verilog».cores.picorv32.r1_system
