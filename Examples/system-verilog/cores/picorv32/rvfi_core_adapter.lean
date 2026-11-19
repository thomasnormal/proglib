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

/-! A failed canonical cycle or a refused RVFI decode remains a `Res` failure.
    The wrapper is intentionally not a total `RvfiCycleMachine`: an invariant
    must first prove that both execution and observation decoding succeed. -/

def rvfiStep (d : CoreMemDesign) (st : CoreMemState) (entry : SvState) :
    Res (CoreMemState × RvfiObservation) := do
  let next ← d.fastStepCanonical st entry
  let row ← match rvfiObservation d next with
    | some row => .ok row
    | none => .unsupported "RVFI decode refused canonical post-state"
  pure (next, row)

theorem rvfiStep_ok_of_fast_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation}
    (hstep : d.fastStepCanonical st entry = .ok next)
    (hdecode : rvfiObservation d next = some row) :
    rvfiStep d st entry = .ok (next, row) := by
  simp [rvfiStep, hstep, hdecode]

theorem rvfiStep_ok_iff_fast_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation} :
    rvfiStep d st entry = .ok (next, row) ↔
      d.fastStepCanonical st entry = .ok next ∧
        rvfiObservation d next = some row := by
  constructor
  · intro h
    unfold rvfiStep at h
    cases hs : d.fastStepCanonical st entry with
    | timeout => simp [hs] at h
    | unsupported msg => simp [hs] at h
    | ok a =>
        simp only [hs, Res.ok_bind] at h
        cases hd : rvfiObservation d a with
        | none => simp [hd] at h
        | some b =>
            simp only [hd, pure] at h
            cases h
            exact ⟨rfl, hd⟩
  · rintro ⟨hstep, hdecode⟩
    exact rvfiStep_ok_of_fast_and_decode hstep hdecode

theorem rvfiStep_ok_iff_step_and_decode
    {d : CoreMemDesign} {st next : CoreMemState} {entry : SvState}
    {row : RvfiObservation} :
    rvfiStep d st entry = .ok (next, row) ↔
      d.step st entry = .ok next ∧
        rvfiObservation d next = some row := by
  rw [rvfiStep_ok_iff_fast_and_decode]
  rw [d.fastStepCanonical_eq_step]

#print axioms rvfiPortSample_read
#print axioms rvfiObservation_eq_decode
#print axioms rvfiStep_ok_of_fast_and_decode
#print axioms rvfiStep_ok_iff_fast_and_decode
#print axioms rvfiStep_ok_iff_step_and_decode

end Examples.«system-verilog».cores.picorv32.rvfi_core_adapter
