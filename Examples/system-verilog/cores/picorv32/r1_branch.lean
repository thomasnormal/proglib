import LeanModels.Refine.RvfiBranch
import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

/-!
# PicoRV32 R1 conditional-branch class

The six RV32I conditional-branch encodings use the pinned core's 32-bit
instruction width and a common offset.  Each theorem quantifies over the
architectural state and byte memory, so the loaded-core proof only needs to
establish the corresponding raw RVFI boundary.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_branch

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32

def beqWord : Word := 0x00000463
def bneWord : Word := 0x00001463
def bltWord : Word := 0x00004463
def bgeWord : Word := 0x00005463
def bltuWord : Word := 0x00006463
def bgeuWord : Word := 0x00007463

theorem branch_decodes :
    Fetched.decode (.word beqWord) = some (.branch .eq 0 0 8) ∧
    Fetched.decode (.word bneWord) = some (.branch .ne 0 0 8) ∧
    Fetched.decode (.word bltWord) = some (.branch .lt 0 0 8) ∧
    Fetched.decode (.word bgeWord) = some (.branch .ge 0 0 8) ∧
    Fetched.decode (.word bltuWord) = some (.branch .ltu 0 0 8) ∧
    Fetched.decode (.word bgeuWord) = some (.branch .geu 0 0 8) := by
  decide

def beqInstruction : BranchInstruction :=
  { word := beqWord, cond := .eq, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.1 }
def bneInstruction : BranchInstruction :=
  { word := bneWord, cond := .ne, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.2.1 }
def bltInstruction : BranchInstruction :=
  { word := bltWord, cond := .lt, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.2.2.1 }
def bgeInstruction : BranchInstruction :=
  { word := bgeWord, cond := .ge, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.2.2.2.1 }
def bltuInstruction : BranchInstruction :=
  { word := bltuWord, cond := .ltu, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.2.2.2.2.1 }
def bgeuInstruction : BranchInstruction :=
  { word := bgeuWord, cond := .geu, rs1 := 0, rs2 := 0, offset := 8,
    decode := branch_decodes.2.2.2.2.2 }

theorem picorv32_beq_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word beqWord) 0 =
      (branchNext state .eq 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory beqWord .eq 0 0 8
    branch_decodes.1

theorem picorv32_bne_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bneWord) 0 =
      (branchNext state .ne 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bneWord .ne 0 0 8
    branch_decodes.2.1

theorem picorv32_blt_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bltWord) 0 =
      (branchNext state .lt 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bltWord .lt 0 0 8
    branch_decodes.2.2.1

theorem picorv32_bge_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bgeWord) 0 =
      (branchNext state .ge 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bgeWord .ge 0 0 8
    branch_decodes.2.2.2.1

theorem picorv32_bltu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bltuWord) 0 =
      (branchNext state .ltu 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bltuWord .ltu 0 0 8
    branch_decodes.2.2.2.2.1

theorem picorv32_bgeu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word bgeuWord) 0 =
      (branchNext state .geu 0 0 8, memory) := by
  exact isaStepMemWith_branch cv32e40pProfile state memory bgeuWord .geu 0 0 8
    branch_decodes.2.2.2.2.2

theorem picorv32_beq_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word beqWord, memory := memory, irq := 0 } =
      (branchNext state .eq 0 0 8,
        branchRetirement state
          { fetched := .word beqWord, memory := memory, irq := 0 } .eq 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory beqWord .eq 0 0 8
    branch_decodes.1

theorem picorv32_bne_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bneWord, memory := memory, irq := 0 } =
      (branchNext state .ne 0 0 8,
        branchRetirement state
          { fetched := .word bneWord, memory := memory, irq := 0 } .ne 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bneWord .ne 0 0 8
    branch_decodes.2.1

theorem picorv32_blt_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bltWord, memory := memory, irq := 0 } =
      (branchNext state .lt 0 0 8,
        branchRetirement state
          { fetched := .word bltWord, memory := memory, irq := 0 } .lt 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bltWord .lt 0 0 8
    branch_decodes.2.2.1

theorem picorv32_bge_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bgeWord, memory := memory, irq := 0 } =
      (branchNext state .ge 0 0 8,
        branchRetirement state
          { fetched := .word bgeWord, memory := memory, irq := 0 } .ge 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bgeWord .ge 0 0 8
    branch_decodes.2.2.2.1

theorem picorv32_bltu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bltuWord, memory := memory, irq := 0 } =
      (branchNext state .ltu 0 0 8,
        branchRetirement state
          { fetched := .word bltuWord, memory := memory, irq := 0 } .ltu 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bltuWord .ltu 0 0 8
    branch_decodes.2.2.2.2.1

theorem picorv32_bgeu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word bgeuWord, memory := memory, irq := 0 } =
      (branchNext state .geu 0 0 8,
        branchRetirement state
          { fetched := .word bgeuWord, memory := memory, irq := 0 } .geu 0 0 8) := by
  exact rvMachineWith_branch cv32e40pProfile state memory bgeuWord .geu 0 0 8
    branch_decodes.2.2.2.2.2

/-! The raw branch row fields determine the exact architectural branch step.
    This bridge is independent of the retirement changed-write list because a
    conditional branch has no register write. -/

theorem picorv32_branch_fields_isa_step
    (profile : PlatformProfile) (state : ArchState) (input : Input)
    (observation : RvfiObservation) (word : Word) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word)
    (hfields : observation.branchFields state input word cond rs1 rs2 offset) :
    isaStepMemWith profile state input.memory input.fetched input.irq =
      (branchNext state cond rs1 rs2 offset, input.memory) := by
  have hirq : input.irq = 0 := hfields.1
  have hfetched : input.fetched = .word word := hfields.2.1
  have hdecode : Fetched.decode (.word word) =
      some (.branch cond rs1 rs2 offset) := hfields.2.2.1
  cases input with
  | mk fetched memory irq =>
      rw [hfetched, hirq]
      exact isaStepMemWith_branch profile state memory word cond rs1 rs2 offset hdecode

#print axioms picorv32_branch_fields_isa_step

/-! The six fixed branch rows share one loaded-core adapter.  Each wrapper
    retains the exact source transition, decoded observation, and condition-
    specific raw boundary before entering the indexed dispatcher. -/

theorem picorv32_beq_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input beqWord .eq 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .eq 0 0 8, memory := input.memory }
        (branchRetirement arch input .eq 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input beqInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [beqInstruction] using hboundary
  simpa [beqInstruction] using h.to_rv32i_boundary

theorem picorv32_bne_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input bneWord .ne 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .ne 0 0 8, memory := input.memory }
        (branchRetirement arch input .ne 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input bneInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [bneInstruction] using hboundary
  simpa [bneInstruction] using h.to_rv32i_boundary

theorem picorv32_blt_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input bltWord .lt 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .lt 0 0 8, memory := input.memory }
        (branchRetirement arch input .lt 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input bltInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [bltInstruction] using hboundary
  simpa [bltInstruction] using h.to_rv32i_boundary

theorem picorv32_bge_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input bgeWord .ge 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .ge 0 0 8, memory := input.memory }
        (branchRetirement arch input .ge 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input bgeInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [bgeInstruction] using hboundary
  simpa [bgeInstruction] using h.to_rv32i_boundary

theorem picorv32_bltu_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input bltuWord .ltu 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .ltu 0 0 8, memory := input.memory }
        (branchRetirement arch input .ltu 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input bltuInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [bltuInstruction] using hboundary
  simpa [bltuInstruction] using h.to_rv32i_boundary

theorem picorv32_bgeu_loaded_rv32i_boundary_of_step
    {d : LeanModels.Sv.Kernel.CoreMemDesign} {st : LeanModels.Sv.Kernel.CoreMemState}
    {entry : LeanModels.Sv.SvState} {next : LeanModels.Sv.Kernel.CoreMemState}
    {observation : RvfiObservation} {arch : ArchState} {input : Input}
    (hstep : d.step st entry = .ok next)
    (hdecode : rvfi_core_adapter.rvfiObservation d next = some observation)
    (hboundary : observation.branchBoundary arch input bgeuWord .geu 0 0 8) :
    ∃ next' observation', rvfi_core_adapter.rvfiStep d st entry = .ok (next', observation') ∧
      Rv32iBoundary arch input observation' { arch := branchNext arch .geu 0 0 8, memory := input.memory }
        (branchRetirement arch input .geu 0 0 8) := by
  have hfast : d.fastStepCanonical st entry = .ok next := by rw [d.fastStepCanonical_eq_step]; exact hstep
  have h : rvfi_core_adapter.CoreBranchBoundary d st entry arch input bgeuInstruction := by
    refine ⟨next, observation, rvfi_core_adapter.rvfiStep_ok_of_fast_and_decode hfast hdecode, ?_⟩
    simpa [bgeuInstruction] using hboundary
  simpa [bgeuInstruction] using h.to_rv32i_boundary

#print axioms picorv32_beq_loaded_rv32i_boundary_of_step
#print axioms picorv32_bne_loaded_rv32i_boundary_of_step
#print axioms picorv32_blt_loaded_rv32i_boundary_of_step
#print axioms picorv32_bge_loaded_rv32i_boundary_of_step
#print axioms picorv32_bltu_loaded_rv32i_boundary_of_step
#print axioms picorv32_bgeu_loaded_rv32i_boundary_of_step

/-! A loaded machine can consume the common branch boundary directly.  The
    instruction witness stays the retained `BranchInstruction`, so the mixed
    dispatcher receives the source word, decode proof, order, and relation
    continuation together. -/

theorem picorv32_branch_exact_cycle_step_refines
    {d : LeanModels.Sv.Kernel.CoreMemDesign}
    (machine : rvfi_core_adapter.CoreRvfiMachine d)
    (instruction : BranchInstruction)
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
            input = branchProgramInput memoryState.memory instruction ∧
            observation.order = start ∧
            observation.branchBoundary memoryState.arch input
              instruction.word instruction.cond instruction.rs1 instruction.rs2
              instruction.offset ∧
            rel next
              { arch := branchNext memoryState.arch instruction.cond
                  instruction.rs1 instruction.rs2 instruction.offset,
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
          (rv32iProgramStep memoryState (.branch instruction))
          (rv32iProgramRetirement memoryState (.branch instruction)) := by
        simpa [hmem, hinput, branchProgramInput, rv32iProgramStep,
          rv32iProgramRetirement] using
          (RvfiObservation.branchBoundary_rv32i instruction.word
            instruction.cond instruction.rs1 instruction.rs2 instruction.offset
            hboundary)
      simp only [↓reduceIte]
      exact ⟨.branch instruction, by simpa [rv32iProgramInput] using hinput,
        horder, hrvfi, by simpa [rv32iProgramStep] using hnext⟩

#print axioms picorv32_branch_exact_cycle_step_refines

/-! The loaded branch consumer packages one exact `BranchInstruction` into the
    reset-specialized all-prefix contract. -/

end Examples.«system-verilog».cores.picorv32.r1_branch
