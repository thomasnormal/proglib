import LeanModels.Refine.RvfiAddi
import LeanModels.Refine.RvfiPorts
import Examples.«system-verilog».cores.picorv32.rvfi_proof
import Examples.«system-verilog».cores.picorv32.trace_proof

/-!
# PicoRV32 raw RVFI ADDI boundary witness

`addi1` is the first non-trapping row from the pinned PicoRV32 RVFI probe.
This theorem checks the raw wire predicate against the reset architectural
state, including the exact fetched word and decode, source and destination
values, the no-trap/no-memory boundary, and the semantic `addiRetirement`
equality.  It is a measured boundary witness, not a theorem about the
currently blocked symbolic RTL load.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary

open LeanModels.Rv
open LeanModels.Refine
open LeanModels.Sv.Observe
open LeanModels.Refine.RvfiPorts
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.trace_proof

def addiInput : Input :=
  { fetched := .word 0x00500093, memory := fun _ => 0, irq := 0 }

/-- The measured second ADDI row with the source fields retained.  The older
compact `rvfi_proof` row intentionally omitted those fields because its
normalization theorem does not consume them. -/
def addi2Raw : RvfiObservation :=
  { addi2 with rs1Addr := 2, rs1Rdata := 5 }

def addi2Input : Input :=
  { fetched := .word 0x00110193, memory := memFive, irq := 0 }

def addi2State : ArchState :=
  machineStateAfter rvMachine (ArchState.init 0) (nontrapInputs.take 3)

/-! The first ADDI row as a concrete, fully-known RVFI port sample.  The
    projection keeps every declared field, including fields unused by ADDI,
    so the decoder theorem cannot obtain its result by filling omitted ports
    with defaults. -/

def addi1Payload : Payload :=
  { order := .ofNat 64 0
    insn := .ofNat 32 0x00500093
    trap := .ofNat 1 0
    halt := .ofNat 1 0
    intr := .ofNat 1 0
    mode := .ofNat 2 3
    ixl := .ofNat 2 1
    rs1Addr := .ofNat 5 0
    rs2Addr := .ofNat 5 0
    rs1Rdata := .ofNat 32 0
    rs2Rdata := .ofNat 32 0
    rdAddr := .ofNat 5 1
    rdWdata := .ofNat 32 5
    pcRdata := .ofNat 32 0
    pcWdata := .ofNat 32 4
    memAddr := .ofNat 32 0
    memRmask := .ofNat 4 0
    memWmask := .ofNat 4 0
    memRdata := .ofNat 32 0
    memWdata := .ofNat 32 0 }

def addi1PortSample : PortSample :=
  ⟨[ ("rvfi_valid", .ofBitVec (.ofNat 1 1))
    , ("rvfi_order", .ofBitVec (.ofNat 64 0))
    , ("rvfi_insn", .ofBitVec (.ofNat 32 0x00500093))
    , ("rvfi_trap", .ofBitVec (.ofNat 1 0))
    , ("rvfi_halt", .ofBitVec (.ofNat 1 0))
    , ("rvfi_intr", .ofBitVec (.ofNat 1 0))
    , ("rvfi_mode", .ofBitVec (.ofNat 2 3))
    , ("rvfi_ixl", .ofBitVec (.ofNat 2 1))
    , ("rvfi_rs1_addr", .ofBitVec (.ofNat 5 0))
    , ("rvfi_rs2_addr", .ofBitVec (.ofNat 5 0))
    , ("rvfi_rs1_rdata", .ofBitVec (.ofNat 32 0))
    , ("rvfi_rs2_rdata", .ofBitVec (.ofNat 32 0))
    , ("rvfi_rd_addr", .ofBitVec (.ofNat 5 1))
    , ("rvfi_rd_wdata", .ofBitVec (.ofNat 32 5))
    , ("rvfi_pc_rdata", .ofBitVec (.ofNat 32 0))
    , ("rvfi_pc_wdata", .ofBitVec (.ofNat 32 4))
    , ("rvfi_mem_addr", .ofBitVec (.ofNat 32 0))
    , ("rvfi_mem_rmask", .ofBitVec (.ofNat 4 0))
    , ("rvfi_mem_wmask", .ofBitVec (.ofNat 4 0))
    , ("rvfi_mem_rdata", .ofBitVec (.ofNat 32 0))
    , ("rvfi_mem_wdata", .ofBitVec (.ofNat 32 0)) ]⟩

theorem pinned_addi1_port_projection :
    RvfiPorts.PayloadProjection "rvfi_" addi1PortSample addi1Payload := by
  constructor <;>
    apply readBits_ofBitVec <;>
    simp [PortSample.read, LeanModels.Sv.SvState.lookup, addi1PortSample,
      addi1Payload, LeanModels.Sv.LVec.ofBitVec]

theorem pinned_addi1_port_decode :
    decode "rvfi_" addi1PortSample = some addi1 := by
  apply RvfiPorts.decode_of_projection pinned_addi1_port_projection
  decide

#guard decode "rvfi_" addi1PortSample == some addi1

theorem pinned_addi_boundary :
    RvfiObservation.addiBoundary (ArchState.init 0) addiInput addi1
      0x00500093 1 0 5 := by
  unfold RvfiObservation.addiBoundary RvfiObservation.addiFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_addi_boundary_fields :
    addi1.addiFields (ArchState.init 0) addiInput 0x00500093 1 0 5 := by
  exact pinned_addi_boundary.1

theorem pinned_addi_boundary_semantic :
    addi1.toRetirement? = some
      (addiRetirement (ArchState.init 0) addiInput 1 0 5) := by
  exact pinned_addi_boundary.2

theorem pinned_addi_boundary_no_trap :
    addi1.trap = false ∧ addi1.intr = false ∧ addi1.cause = none := by
  exact RvfiObservation.addiBoundary_no_trap
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi_boundary_no_memory :
    addi1.memRmask = 0 ∧ addi1.memWmask = 0 ∧
      (addiRetirement (ArchState.init 0) addiInput 1 0 5).memory = none := by
  have hm := RvfiObservation.addiBoundary_no_memory_masks
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  have he := RvfiObservation.addiBoundary_memory_none
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  exact ⟨hm.1, hm.2, he⟩

theorem pinned_addi_x0_preserved :
    (addiNext (ArchState.init 0) 1 0 5).readReg 0 = 0 := by
  have hx := RvfiObservation.addiBoundary_x0
    addi1 (ArchState.init 0) addiInput 0x00500093 1 0 5 pinned_addi_boundary
  rw [hx]
  rfl

theorem pinned_addi_isa_step :
    isaStepMemWith cv32e40pProfile (ArchState.init 0) addiInput.memory
      addiInput.fetched addiInput.irq =
      (addiNext (ArchState.init 0) 1 0 5, addiInput.memory) := by
  exact RvfiObservation.addiBoundary_isaStepMemWith
    cv32e40pProfile addi1 (ArchState.init 0) addiInput
      0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi_machine_commit :
    (rvMachineWith cv32e40pProfile).step (ArchState.init 0) addiInput =
      (addiNext (ArchState.init 0) 1 0 5,
        addiRetirement (ArchState.init 0) addiInput 1 0 5) := by
  exact RvfiObservation.addiBoundary_rvMachineWith
    cv32e40pProfile addi1 (ArchState.init 0) addiInput
      0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi_stateful_machine_commit :
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := ArchState.init 0, memory := addiInput.memory } addiInput =
      ({ arch := addiNext (ArchState.init 0) 1 0 5,
          memory := addiInput.memory },
        addiRetirement (ArchState.init 0) addiInput 1 0 5) := by
  exact RvfiObservation.addiBoundary_rvMemoryMachineWith
    cv32e40pProfile addi1 (ArchState.init 0) addiInput
      0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_addi2_state :
    addi2State.pc = 12 ∧ addi2State.readReg 2 = 5 ∧
      addi2State.readReg 0 = 0 := by
  decide

theorem pinned_addi2_boundary :
    RvfiObservation.addiBoundary addi2State addi2Input addi2Raw
      0x00110193 3 2 1 := by
  unfold RvfiObservation.addiBoundary RvfiObservation.addiFields
  unfold RvfiObservation.wellFormed RvfiObservation.toRetirement?
  decide

theorem pinned_addi2_isa_step :
    isaStepMemWith cv32e40pProfile addi2State addi2Input.memory
      addi2Input.fetched addi2Input.irq =
      (addiNext addi2State 3 2 1, addi2Input.memory) := by
  exact RvfiObservation.addiBoundary_isaStepMemWith
    cv32e40pProfile addi2Raw addi2State addi2Input
      0x00110193 3 2 1 pinned_addi2_boundary

theorem pinned_addi2_stateful_machine_commit :
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := addi2State, memory := addi2Input.memory } addi2Input =
      ({ arch := addiNext addi2State 3 2 1,
          memory := addi2Input.memory },
        addiRetirement addi2State addi2Input 3 2 1) := by
  exact RvfiObservation.addiBoundary_rvMemoryMachineWith
    cv32e40pProfile addi2Raw addi2State addi2Input
      0x00110193 3 2 1 pinned_addi2_boundary

#guard addiInput.fetched = .word 0x00500093
#guard addi1.toRetirement? == some
  (addiRetirement (ArchState.init 0) addiInput 1 0 5)

#print axioms pinned_addi_boundary
#print axioms pinned_addi_boundary_fields
#print axioms pinned_addi_boundary_semantic
#print axioms pinned_addi_boundary_no_trap
#print axioms pinned_addi_boundary_no_memory
#print axioms pinned_addi_x0_preserved
#print axioms pinned_addi_isa_step
#print axioms pinned_addi_machine_commit
#print axioms pinned_addi_stateful_machine_commit
#print axioms pinned_addi2_state
#print axioms pinned_addi2_boundary
#print axioms pinned_addi2_isa_step
#print axioms pinned_addi2_stateful_machine_commit

end Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
