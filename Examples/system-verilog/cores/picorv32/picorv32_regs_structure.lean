import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».cores.picorv32.picorv32_regs_structure

/-! The leaf is the unmodified `picorv32_regs` module from the pinned PicoRV32
source.  Its envelope is generated from that source with the approved Slang
frontend.  This theorem records that the real register-file leaf reaches the
clocked instant profile. -/

set_option maxRecDepth 100000 in
load_design_sv2 regs from "Examples/system-verilog/cores/picorv32/picorv32_regs.sv.json"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem picorv32_regs_structure : SeqDesignI regs.e := by
  sv_structure

#print axioms picorv32_regs_structure

end Examples.«system-verilog».cores.picorv32.picorv32_regs_structure
