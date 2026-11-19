import Examples.«system-verilog».cores.picorv32.R2
import LeanModels.Sv.Kernel.CoreMemFast
import Examples.«system-verilog».cores.picorv32.rvfi_core_adapter

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Sv LeanModels.Sv.Kernel

/- The loaded design is compiled once so the input-driven receipt can execute
the source-shaped E route without re-elaborating the multi-megabyte envelope
for every temporary probe. -/
opaque picorv32_core_mem : Res CoreMemDesign :=
  picorv32_r2.e 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 4294967295

/-! A loaded canonical-E design is useful to an invariant only when its
    source-shaped design identity is retained alongside the machine adapter.
    The equality is a certificate supplied by the loader result.  It does not
    assert that the adapter's exact-step field has been proved. -/

structure PicoRV32LoadedCanonicalE where
  design : CoreMemDesign
  loaded : picorv32_core_mem = .ok design
  machine : rvfi_core_adapter.CoreRvfiMachine design

end Examples.«system-verilog».cores.picorv32
