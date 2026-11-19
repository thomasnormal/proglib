import Examples.«system-verilog».cores.picorv32.R2
import LeanModels.Sv.Kernel.CoreMemFast

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Sv LeanModels.Sv.Kernel

/- The loaded design is compiled once so the input-driven receipt can execute
the source-shaped E route without re-elaborating the multi-megabyte envelope
for every temporary probe. -/
opaque picorv32_core_mem : Res CoreMemDesign :=
  picorv32_r2.e 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 4294967295

end Examples.«system-verilog».cores.picorv32
