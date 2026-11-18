import LeanModels.Refine.Commit
import LeanModels.Rv.Exec

/-!
# PicoRV32 R1 RV32M class

The eight RV32M register-register operations share one exact execution shape.
The fixed words are checked by the ISA decoder, then threaded through the
memory-preserving step and machine commit equations for arbitrary state and
byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_muldiv

open LeanModels.Rv
open LeanModels.Refine

def mulWord : Word := 0x022081b3
def mulhWord : Word := 0x022091b3
def mulhsuWord : Word := 0x0220a1b3
def mulhuWord : Word := 0x0220b1b3
def divWord : Word := 0x0220c1b3
def divuWord : Word := 0x0220d1b3
def remWord : Word := 0x0220e1b3
def remuWord : Word := 0x0220f1b3

def mulDivNext (s : ArchState) (op : MulDivOp) : ArchState :=
  { s.writeReg 3 (mulDivSem op (s.readReg 1) (s.readReg 2)) with pc := s.pc + 4 }

def mulDivEffects (s : ArchState) : StepEffects := { pcTarget := s.pc + 4 }

def mulDivRetirement (s : ArchState) (input : Input) (op : MulDivOp) : Retirement :=
  Retirement.ofRvStep s input (mulDivNext s op) (mulDivEffects s)

def mulDivKind (op : MulDivOp) : Instr := .mulDiv op 3 1 2

theorem mulDiv_isa (profile : PlatformProfile) (state : ArchState)
    (memory : Memory) (word : Word) (op : MulDivOp)
    (hdecode : Fetched.decode (.word word) = some (mulDivKind op)) :
    isaStepWith profile state memory (.word word) 0 =
      (mulDivNext state op, mulDivEffects state) := by
  have hirq : takeInterrupt? state.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode, mulDivKind]
  simp [mulDivNext, mulDivEffects, execInstr, Fetched.size]

theorem mulDiv_step (profile : PlatformProfile) (state : ArchState)
    (memory : Memory) (word : Word) (op : MulDivOp)
    (hdecode : Fetched.decode (.word word) = some (mulDivKind op)) :
    isaStepMemWith profile state memory (.word word) 0 =
      (mulDivNext state op, memory) := by
  unfold isaStepMemWith
  rw [mulDiv_isa profile state memory word op hdecode]
  rfl

theorem mulDiv_commit (profile : PlatformProfile) (state : ArchState)
    (memory : Memory) (word : Word) (op : MulDivOp)
    (hdecode : Fetched.decode (.word word) = some (mulDivKind op)) :
    (rvMachineWith profile).step state
        { fetched := .word word, memory := memory, irq := 0 } =
      (mulDivNext state op,
        mulDivRetirement state
          { fetched := .word word, memory := memory, irq := 0 } op) := by
  simp only [rvMachineWith]
  rw [mulDiv_isa profile state memory word op hdecode]
  rfl

theorem muldiv_decodes :
    Fetched.decode (.word mulWord) = some (mulDivKind .mul) ∧
    Fetched.decode (.word mulhWord) = some (mulDivKind .mulh) ∧
    Fetched.decode (.word mulhsuWord) = some (mulDivKind .mulhsu) ∧
    Fetched.decode (.word mulhuWord) = some (mulDivKind .mulhu) ∧
    Fetched.decode (.word divWord) = some (mulDivKind .div) ∧
    Fetched.decode (.word divuWord) = some (mulDivKind .divu) ∧
    Fetched.decode (.word remWord) = some (mulDivKind .rem) ∧
    Fetched.decode (.word remuWord) = some (mulDivKind .remu) := by
  decide

theorem picorv32_mul_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word mulWord) 0 =
      (mulDivNext state .mul, memory) := by
  exact mulDiv_step cv32e40pProfile state memory mulWord .mul muldiv_decodes.1

theorem picorv32_mul_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word mulWord, memory := memory, irq := 0 } =
      (mulDivNext state .mul,
        mulDivRetirement state
          { fetched := .word mulWord, memory := memory, irq := 0 } .mul) := by
  exact mulDiv_commit cv32e40pProfile state memory mulWord .mul muldiv_decodes.1

theorem picorv32_mulh_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word mulhWord) 0 =
      (mulDivNext state .mulh, memory) := by
  exact mulDiv_step cv32e40pProfile state memory mulhWord .mulh muldiv_decodes.2.1

theorem picorv32_mulh_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word mulhWord, memory := memory, irq := 0 } =
      (mulDivNext state .mulh,
        mulDivRetirement state
          { fetched := .word mulhWord, memory := memory, irq := 0 } .mulh) := by
  exact mulDiv_commit cv32e40pProfile state memory mulhWord .mulh muldiv_decodes.2.1

theorem picorv32_mulhsu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word mulhsuWord) 0 =
      (mulDivNext state .mulhsu, memory) := by
  exact mulDiv_step cv32e40pProfile state memory mulhsuWord .mulhsu muldiv_decodes.2.2.1

theorem picorv32_mulhsu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word mulhsuWord, memory := memory, irq := 0 } =
      (mulDivNext state .mulhsu,
        mulDivRetirement state
          { fetched := .word mulhsuWord, memory := memory, irq := 0 } .mulhsu) := by
  exact mulDiv_commit cv32e40pProfile state memory mulhsuWord .mulhsu muldiv_decodes.2.2.1

theorem picorv32_mulhu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word mulhuWord) 0 =
      (mulDivNext state .mulhu, memory) := by
  exact mulDiv_step cv32e40pProfile state memory mulhuWord .mulhu muldiv_decodes.2.2.2.1

theorem picorv32_mulhu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word mulhuWord, memory := memory, irq := 0 } =
      (mulDivNext state .mulhu,
        mulDivRetirement state
          { fetched := .word mulhuWord, memory := memory, irq := 0 } .mulhu) := by
  exact mulDiv_commit cv32e40pProfile state memory mulhuWord .mulhu muldiv_decodes.2.2.2.1

theorem picorv32_div_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word divWord) 0 =
      (mulDivNext state .div, memory) := by
  exact mulDiv_step cv32e40pProfile state memory divWord .div muldiv_decodes.2.2.2.2.1

theorem picorv32_div_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word divWord, memory := memory, irq := 0 } =
      (mulDivNext state .div,
        mulDivRetirement state
          { fetched := .word divWord, memory := memory, irq := 0 } .div) := by
  exact mulDiv_commit cv32e40pProfile state memory divWord .div muldiv_decodes.2.2.2.2.1

theorem picorv32_divu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word divuWord) 0 =
      (mulDivNext state .divu, memory) := by
  exact mulDiv_step cv32e40pProfile state memory divuWord .divu muldiv_decodes.2.2.2.2.2.1

theorem picorv32_divu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word divuWord, memory := memory, irq := 0 } =
      (mulDivNext state .divu,
        mulDivRetirement state
          { fetched := .word divuWord, memory := memory, irq := 0 } .divu) := by
  exact mulDiv_commit cv32e40pProfile state memory divuWord .divu muldiv_decodes.2.2.2.2.2.1

theorem picorv32_rem_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word remWord) 0 =
      (mulDivNext state .rem, memory) := by
  exact mulDiv_step cv32e40pProfile state memory remWord .rem muldiv_decodes.2.2.2.2.2.2.1

theorem picorv32_rem_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word remWord, memory := memory, irq := 0 } =
      (mulDivNext state .rem,
        mulDivRetirement state
          { fetched := .word remWord, memory := memory, irq := 0 } .rem) := by
  exact mulDiv_commit cv32e40pProfile state memory remWord .rem muldiv_decodes.2.2.2.2.2.2.1

theorem picorv32_remu_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word remuWord) 0 =
      (mulDivNext state .remu, memory) := by
  exact mulDiv_step cv32e40pProfile state memory remuWord .remu muldiv_decodes.2.2.2.2.2.2.2

theorem picorv32_remu_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word remuWord, memory := memory, irq := 0 } =
      (mulDivNext state .remu,
        mulDivRetirement state
          { fetched := .word remuWord, memory := memory, irq := 0 } .remu) := by
  exact mulDiv_commit cv32e40pProfile state memory remuWord .remu muldiv_decodes.2.2.2.2.2.2.2

#print axioms picorv32_mul_class_step
#print axioms picorv32_mul_class_commit
#print axioms picorv32_mulh_class_step
#print axioms picorv32_mulh_class_commit
#print axioms picorv32_mulhsu_class_step
#print axioms picorv32_mulhsu_class_commit
#print axioms picorv32_mulhu_class_step
#print axioms picorv32_mulhu_class_commit
#print axioms picorv32_div_class_step
#print axioms picorv32_div_class_commit
#print axioms picorv32_divu_class_step
#print axioms picorv32_divu_class_commit
#print axioms picorv32_rem_class_step
#print axioms picorv32_rem_class_commit
#print axioms picorv32_remu_class_step
#print axioms picorv32_remu_class_commit

end Examples.«system-verilog».cores.picorv32.r1_muldiv
