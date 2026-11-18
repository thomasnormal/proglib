import LeanModels.Refine.RvfiTrap

/-!
# PicoRV32 R1 illegal-instruction class

The trap family has two distinct parser outcomes.  An undecodable word enters
the illegal-instruction trap directly, while a decoded Zicsr word with an
unimplemented address takes the separate illegal-CSR path.  Both fixed words
are checked by the exact decoder and threaded through the precise trap
boundary for arbitrary architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_illegal

open LeanModels.Rv
open LeanModels.Refine

def illegalWord : Word := 0x00000000
def illegalCsrWord : Word := 0x7ff110f3

def illegalCsrKind : CsrOpKind :=
  { op := .rw, rd := 1, src := .reg 2, addr := 0x7ff }

theorem illegal_decode :
    Fetched.decode (.word illegalWord) = none := by
  decide

theorem illegal_csr_decode :
    Fetched.decode (.word illegalCsrWord) = some illegalCsrKind.toInstr := by
  decide

theorem illegal_csr_row : findCsr? illegalCsrKind.addr = none := by
  decide

theorem picorv32_illegal_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word illegalWord) 0 =
      (illegalNext state, memory) := by
  exact isaStepMemWith_illegal cv32e40pProfile state memory illegalWord
    illegal_decode

theorem picorv32_illegal_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word illegalWord, memory := memory, irq := 0 } =
      (illegalNext state,
        illegalRetirement state
          { fetched := .word illegalWord, memory := memory, irq := 0 }) := by
  exact rvMachineWith_illegal cv32e40pProfile state memory illegalWord
    illegal_decode

theorem picorv32_illegal_csr_class_step (state : ArchState) (memory : Memory) :
    isaStepMemWith cv32e40pProfile state memory (.word illegalCsrWord) 0 =
      (illegalNext state, memory) := by
  exact isaStepMemWith_illegal_csr cv32e40pProfile state memory
    illegalCsrWord illegalCsrKind illegal_csr_decode illegal_csr_row

theorem picorv32_illegal_csr_class_commit (state : ArchState) (memory : Memory) :
    (rvMachineWith cv32e40pProfile).step state
        { fetched := .word illegalCsrWord, memory := memory, irq := 0 } =
      (illegalNext state,
        illegalRetirement state
          { fetched := .word illegalCsrWord, memory := memory, irq := 0 }) := by
  exact rvMachineWith_illegal_csr cv32e40pProfile state memory
    illegalCsrWord illegalCsrKind illegal_csr_decode illegal_csr_row

#print axioms picorv32_illegal_class_step
#print axioms picorv32_illegal_class_commit
#print axioms picorv32_illegal_csr_class_step
#print axioms picorv32_illegal_csr_class_commit

end Examples.«system-verilog».cores.picorv32.r1_illegal
