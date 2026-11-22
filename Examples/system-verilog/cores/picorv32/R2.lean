import Examples.«system-verilog».cores.picorv32.input_drive_core
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter
import LeanModels.Refine.Rv32i

/-! # PicoRV32 ADDI refinement at registered retirement

The obligation starts with successful loading and initialization of the actual
core. At the pinned parameters, the loader currently refuses with
`Schedule:preemptive` before reset. The executable reference and the protected
byte preservation theorem below can be checked independently of core admission.
-/

namespace Examples.«system-verilog».cores.picorv32.AddiRefinement

open LeanModels.Sv LeanModels.Sv.Kernel LeanModels.Sv.Observe
open LeanModels.Rv LeanModels.Refine LeanModels.Refine.RvfiPorts

set_option autoImplicit false

/-- The byte addresses protected by the program. A store is admissible only
if every byte it actually writes is outside the region, including at wraparound. -/
def storeOutside (code : Word → Bool) (addr : Word) (w : MemW) : Bool :=
  (List.range w.bytes).all fun i => !(code (addr + BitVec.ofNat 32 i))

def codeWord (code : Word → Bool) (pc : Word) : Bool :=
  code pc && code (pc + 1) && code (pc + 2) && code (pc + 3)

/-- A store outside the region preserves each protected byte. -/
theorem storeVal_preserves_code (image : Memory) (code : Word → Bool) (addr data a : Word)
    (w : MemW) (h : storeOutside code addr w) (ha : code a) :
    storeVal image w addr data a = image a := by
  dsimp only [storeVal]
  split <;> rename_i hoff
  · simp [storeOutside, List.all_eq_true] at h
    have hh := h (a - addr).toNat hoff
    have he : addr + BitVec.ofNat 32 (a - addr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [he, ha] at hh
    contradiction
  · rfl

/-- Reference state at a retirement boundary. Only x0 is defined by reset
at the pinned parameters (STACKADDR is all ones, REGS_INIT_ZERO is zero). -/
structure ReferenceState where
  arch : ArchState
  ram : Memory
  initialized : List Reg

def ReferenceState.reset (image : Memory) (regs : Reg → Word) : ReferenceState :=
  ⟨{ pc := 0, regs := fun r => if r == 0 then 0 else regs r }, image, [0]⟩

/-- Register operands mentioned by the existing decoder. The first R2 fragment
admits the base integer arithmetic, branch, jump and aligned memory families. -/
private def regAccess (i : Instr) : Option (List Reg × Option Reg) :=
  let left : Src1 → List Reg := fun | .reg r => [r] | .pc => []
  let right : Src2 → List Reg := fun | .reg r => [r] | .imm _ => []
  match i with
  | .alu _ rd a b => some (left a ++ right b, some rd)
  | .jump rd base _ => some (left base, some rd)
  | .branch _ r1 r2 _ => some ([r1, r2], none)
  | .mem (.load _) _ rd r1 _ => some ([r1], some rd)
  | .mem .store _ r2 r1 _ => some ([r1, r2], none)
  | .mulDiv .. | .system .. => none

private def allowedAccess (code : Word → Bool) : Option MemEffect → Bool
  | some (.read a w) => a.toNat % w.bytes == 0
  | some (.write a w _) => a.toNat % w.bytes == 0 && storeOutside code a w
  | none => true

/-- Fetch and execute the reference from its own byte memory. The ISA determines
its instruction, operands, branch outcome, and next PC independently of the core. -/
def referenceStep (profile : PlatformProfile) (code : Word → Bool)
    (s : ReferenceState) : Option ReferenceState := do
  let pc := s.arch.pc
  guard (pc.toNat % 4 == 0 && codeWord code pc)
  let word := loadVal s.ram .word false pc
  let inst ← Fetched.decode (.word word)
  let (reads, rd) ← regAccess inst
  guard (reads.all (s.initialized.contains ·))
  let (arch, eff) := isaStepWith profile s.arch s.ram (.word word) 0
  guard (eff.trap.isNone && arch.pc.toNat % 4 == 0)
  guard (allowedAccess code eff.mem)
  return { arch, ram := applyMemEffect s.ram eff.mem,
           initialized := rd.elim s.initialized (fun r => s.initialized.insert r) }

def referenceAt (profile : PlatformProfile) (code : Word → Bool)
    (s : ReferenceState) : Nat → Option ReferenceState
  | 0 => some s
  | n+1 => (referenceAt profile code s n).bind (referenceStep profile code)

private theorem apply_access_preserves (code : Word → Bool) (mem : Memory)
    (effect : Option MemEffect) (h : allowedAccess code effect = true) (a : Word) (ha : code a) :
    applyMemEffect mem effect a = mem a := by
  cases effect with
  | none => rfl
  | some e =>
    cases e with
    | read => rfl
    | write addr w data =>
      exact storeVal_preserves_code mem code addr data a w (Bool.and_eq_true_iff.mp h).2 ha

theorem referenceStep_preserves_code (profile : PlatformProfile) (code : Word → Bool)
    {s t : ReferenceState} (hs : referenceStep profile code s = some t) (a : Word) (ha : code a) :
    t.ram a = s.ram a := by
  simp [referenceStep, Option.bind_eq_some_iff, guard] at hs
  obtain ⟨_, _, _, _, _, _, _, _, hallowed, rfl⟩ := hs
  exact apply_access_preserves code s.ram _ hallowed a ha

/-- Every protected byte keeps its original value throughout an arbitrary
admitted prefix, including stores whose byte offsets wrap at 32 bits. -/
theorem referenceAt_preserves_code (profile : PlatformProfile) (code : Word → Bool)
    (initial : ReferenceState) {n : Nat} {s : ReferenceState}
    (hs : referenceAt profile code initial n = some s) (a : Word) (ha : code a) :
    s.ram a = initial.ram a := by
  induction n generalizing s with
  | zero =>
    cases hs
    rfl
  | succ n ih =>
    obtain ⟨mid, hp, ht⟩ := Option.bind_eq_some_iff.mp hs
    exact (referenceStep_preserves_code profile code ht a ha).trans (ih hp)

#print axioms referenceAt_preserves_code

-- A protected byte at zero is reached by a word store from the last byte.
#guard !storeOutside (· == 0) 0xffffffff .word
#guard storeOutside (· == 0) 0xffffffff .byte

-- The first ADDI writes its previously uninitialized destination with -1.
-- This inhabited reference prefix protects all four instruction bytes.
#guard (referenceStep ⟨.retireFirst⟩ (fun a => a.toNat < 4)
  (ReferenceState.reset (storeVal (fun _ => 0) .word 0 0xfff00593) (fun _ => 13))).any
  (fun post => post.arch.pc == 4 && post.arch.readReg 11 == 0xffffffff && post.initialized.contains 11)

/-- LUI and ADDI x?,x0 share a semantic ALU node. Identify the
instruction class with the ISA decoder's encoding table. -/
def isAddi (word : Word) : Bool :=
  (decodeTable.find? (·.matches word)).any (·.mnemonic == "addi")

-- LUI's semantic node also uses add with x0 and an immediate.
#guard !isAddi 0x123455b7

-- ADDI x11,x1,-1 has an uninitialized source even if the arbitrary
-- representative at reset happens to equal a known integer.
#guard (referenceStep ⟨.retireFirst⟩ (fun a => a.toNat < 4)
  (ReferenceState.reset (storeVal (fun _ => 0) .word 0 0xfff08593) (fun _ => 13))).isNone

/-- Compare every retirement's order, instruction and PCs against the image
and the independent ISA step. For ADDI, the exact port decoder must succeed.
RVFI reports a nonzero rd even on idempotent writes, and reports zero at x0
even when the discarded sum was nonzero. -/
def retirementAgrees (image : Memory) (before after : ReferenceState)
    (order : Nat) (ports : PortSample) : Bool := Id.run do
  let pc := before.arch.pc
  let word := loadVal image .word false pc
  unless readBits 1 ports "rvfi_valid" == some 1 &&
      readBits 64 ports "rvfi_order" == some (BitVec.ofNat 64 order) &&
      readBits 1 ports "rvfi_trap" == some 0 && readBits 1 ports "rvfi_halt" == some 0 &&
      readBits 1 ports "rvfi_intr" == some 0 &&
      readBits 32 ports "rvfi_insn" == some word &&
      readBits 32 ports "rvfi_pc_rdata" == some pc &&
      readBits 32 ports "rvfi_pc_wdata" == some after.arch.pc do return false
  unless isAddi word do return true
  match Fetched.decode (.word word), RvfiPorts.decode "rvfi_" ports with
  | some (.alu .add rd (.reg rs1) (.imm _)), some row =>
      return row.rs1Addr == rs1 && row.rs1Rdata == before.arch.readReg rs1 &&
        row.rdAddr == rd && row.rdWdata == after.arch.readReg rd &&
        row.memRmask == 0 && row.memWmask == 0
  | _, _ => return false

/-- Free input pins on each clock. While the memory bus is idle the environment
may put any word on the read-data pins. Reset is active low for four clocks. -/
structure Inputs where
  pcpiWr : BitVec 1
  pcpiRd : Word
  pcpiWait : BitVec 1
  idleRdata : Word

structure CycleState where
  core : CoreMemState
  ram : Memory
  clocks : Nat

private def sample (d : CoreMemDesign) (s : CoreMemState) : PortSample :=
  let view := s.view d
  ⟨d.scalar.toDesign2.outputNames.toList.filterMap fun name =>
    (SvState.lookup view name).map fun value => (name, value)⟩

private def busAddress (ports : PortSample) : Option (Option Word) := do
  if (← readBits 1 ports "mem_valid") == 0 then return none
  let addr ← readBits 32 ports "mem_addr"
  -- The native memory port issues aligned addresses and four byte strobes.
  guard (addr.toNat % 4 == 0)
  return some addr

/-- Apply exactly the acknowledged byte lanes. Disabled lanes can contain x/z. -/
private def storeLanes (ports : PortSample) (mem : Memory) (addr : Word) : Option Memory := do
  let mask ← readBits 4 ports "mem_wstrb"
  if mask == 0 then return mem
  let data ← ports.read "mem_wdata"
  guard (data.width == 32)
  (List.range 4).foldlM (init := mem) fun m lane => do
    if !mask.getLsbD lane then return m
    let byte ← (data.extract (8 * lane) 8).known?
    return storeVal m .byte (addr + BitVec.ofNat 32 lane) (BitVec.ofNat 32 byte.toNat)

/-- The registered request supplies the response at the next rising edge.
Check the request again after the low-phase input drive. Take strobes/data
from that settled pre-edge state and sample RVFI only after the high edge. -/
private def cycle (d : CoreMemDesign) (inputs : Nat → Inputs) (s : CycleState) :
    Option CycleState := do
  let pins := inputs s.clocks
  let active := decide (4 ≤ s.clocks)
  let request ← if active then busAddress (sample d s.core) else some none
  let rdata := request.elim pins.idleRdata (loadVal s.ram .word false)
  let low ← (d.step s.core [("clk", .ofNat 1 0), ("resetn", .ofBitVec (.ofBool active)),
    ("mem_ready", .ofNat 1 1), ("mem_rdata", .ofBitVec rdata), ("irq", .ofNat 32 0),
    ("pcpi_ready", .ofNat 1 0), ("pcpi_wr", .ofBitVec pins.pcpiWr),
    ("pcpi_rd", .ofBitVec pins.pcpiRd), ("pcpi_wait", .ofBitVec pins.pcpiWait)]).toOption
  let pre := sample d low
  if active then guard ((← busAddress pre) == request)
  let ram ← request.elim (some s.ram) (storeLanes pre s.ram)
  let high ← (d.step low [("clk", .ofNat 1 1)]).toOption
  return ⟨high, ram, s.clocks + 1⟩

private def afterReset (d : CoreMemDesign) (pins : Nat → Inputs)
    (initial : CoreMemState) (image : Memory) : Option CycleState :=
  (List.range 4).foldlM (init := ⟨initial, image, 0⟩) fun s _ => do
    let next ← cycle d pins s
    guard ((← readBits 1 (sample d next.core) "rvfi_valid") == 0)
    return next

/-- Stop at the first valid row, counting elapsed clocks even for bubbles.
Unknown valid, a failed step, or exhaustion of the bound refuses the run. -/
private def nextRetirement (d : CoreMemDesign) (pins : Nat → Inputs) :
    Nat → CycleState → Option CycleState
  | 0, _ => none
  | n+1, s => do
    let next ← cycle d pins s
    if (← readBits 1 (sample d next.core) "rvfi_valid") == 1 then return next
    nextRetirement d pins n next

private def boundaryAt (d : CoreMemDesign) (pins : Nat → Inputs) (bound : Nat)
    (resetState : CycleState) : Nat → Option CycleState
  | 0 => some resetState
  | n+1 => (boundaryAt d pins bound resetState n).bind (nextRetirement d pins bound)

/-- Only initialized nonzero cells have a physical register-file obligation.
The RTL reads x0 through a mux that bypasses cpuregs[0]. -/
private def registersAgree (s : CoreMemState) (ref : ReferenceState) : Prop :=
  ∀ r ∈ ref.initialized, r ≠ 0 →
    s.memory.read "cpuregs" r.val = some (.ofBitVec (ref.arch.readReg r))

/-- One ISA-specified retirement in a mixed base-integer prefix. Read order,
PC and word even on preceding non-ADDI instructions. Use the full decoder on
ADDI, and check its architectural post-state against the real cpuregs and
external byte memory. -/
private def boundaryAgrees (d : CoreMemDesign)
    (image : Memory) (order : Nat) (before after : ReferenceState) (actual : CycleState) : Prop :=
  retirementAgrees image before after order (rvfi_core_adapter.rvfiPortSample d actual.core) = true ∧
  (isAddi (loadVal image .word false before.arch.pc) = true →
    registersAgree actual.core after ∧ actual.ram = after.ram)

/-- R1 obligation for the default RISCV_FORMAL build. Loading and initialization
are conclusions. Every admissible ISA prefix demands a bounded real retirement,
including the first instruction after reset. Instruction selection, code-region
protection and initialization of source operands consult only the hand-written
LeanModels/Rv ISA (its independent Sail validation is R0). -/
def PicoRV32AddiRefines : Prop :=
  ∃ d initial bound, picorv32_core_mem = .ok d ∧ d.initialState = .ok initial ∧ 0 < bound ∧
  ∀ (profile : PlatformProfile) (image : Memory) (code : Word → Bool)
      (pins : Nat → Inputs) (initialRegs : Reg → Word),
    ∃ resetState, afterReset d pins initial image = some resetState ∧
    ∀ n before after,
      referenceAt profile code (ReferenceState.reset image initialRegs) n = some before →
      referenceStep profile code before = some after →
      ∃ actual, boundaryAt d pins bound resetState (n + 1) = some actual ∧
        boundaryAgrees d image n before after actual

end Examples.«system-verilog».cores.picorv32.AddiRefinement
