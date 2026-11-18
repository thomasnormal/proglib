import LeanModels.Refine.RvfiCsr

/-!
# PicoRV32 R1 Zicsr class

The six RV32I Zicsr operation/source forms are represented by explicit
`CsrOpKind` values.  Their fixed words are checked by the exact decoder and
their implemented CSR rows are retained as premises before the threaded step
and retirement boundaries are applied.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_csr

open LeanModels.Rv
open LeanModels.Refine

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
