import Examples.«system-verilog».cores.picorv32.R2
import LeanModels.Sv.Kernel.CoreMemFast

/-!
# PicoRV32 canonical-E RVFI state adapter

This adapter restricts a canonical `CoreMemState` view to the declared RVFI
ports before applying the exact `RvfiPorts.decode` function.  It has no
defaults and does not reinterpret internal signals.  A future loaded-core
invariant can use this function at the post-edge cut point while retaining
the canonical fast-cycle refinement theorem.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

open LeanModels.Sv
open LeanModels.Sv.Kernel
open LeanModels.Sv.Observe
open LeanModels.Refine
open LeanModels.Refine.RvfiPorts

def rvfiPortNames : List String :=
  ["rvfi_valid", "rvfi_order", "rvfi_insn", "rvfi_trap", "rvfi_halt",
   "rvfi_intr", "rvfi_mode", "rvfi_ixl", "rvfi_rs1_addr", "rvfi_rs2_addr",
   "rvfi_rs1_rdata", "rvfi_rs2_rdata", "rvfi_rd_addr", "rvfi_rd_wdata",
   "rvfi_pc_rdata", "rvfi_pc_wdata", "rvfi_mem_addr", "rvfi_mem_rmask",
   "rvfi_mem_wmask", "rvfi_mem_rdata", "rvfi_mem_wdata"]

def rvfiPortSample (d : CoreMemDesign) (st : CoreMemState) : PortSample :=
  ⟨rvfiPortNames.filterMap fun name =>
    (SvState.lookup (CoreMemState.view d st) name).map fun value => (name, value)⟩

theorem rvfiPortSample_read (d : CoreMemDesign) (st : CoreMemState)
    (name : String) :
    (rvfiPortSample d st).read name =
      if name ∈ rvfiPortNames then
        SvState.lookup (CoreMemState.view d st) name
      else none := by
  exact lookup_filterMap
    (fun n => SvState.lookup (CoreMemState.view d st) n) name rvfiPortNames

def rvfiObservation (d : CoreMemDesign) (st : CoreMemState) :
    Option RvfiObservation :=
  decode "rvfi_" (rvfiPortSample d st)

theorem rvfiObservation_eq_decode (d : CoreMemDesign) (st : CoreMemState) :
    rvfiObservation d st = decode "rvfi_" (rvfiPortSample d st) := rfl

#print axioms rvfiPortSample_read
#print axioms rvfiObservation_eq_decode

end Examples.«system-verilog».cores.picorv32.rvfi_core_adapter
