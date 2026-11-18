import LeanModels.Refine.RvfiSystem

/-!
# PicoRV32 R1 system-transfer class

The no-interrupt machine-mode system family contains ECALL, EBREAK, MRET,
and WFI.  Their fixed words are checked by the exact decoder, then threaded
through the memory-preserving step and retirement boundary for arbitrary
architectural state and byte memory.
-/

namespace Examples.«system-verilog».cores.picorv32.r1_system

open LeanModels.Rv
open LeanModels.Refine

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

#print axioms picorv32_ecall_class_step
#print axioms picorv32_ecall_class_commit
#print axioms picorv32_ebreak_class_step
#print axioms picorv32_ebreak_class_commit
#print axioms picorv32_mret_class_step
#print axioms picorv32_mret_class_commit
#print axioms picorv32_wfi_class_step
#print axioms picorv32_wfi_class_commit

end Examples.«system-verilog».cores.picorv32.r1_system
