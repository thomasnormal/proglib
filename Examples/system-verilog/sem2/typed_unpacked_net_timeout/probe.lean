import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv
open LeanModels.Sv.Kernel
load_design_sv2 typedUnpackedNet
  from "Examples/system-verilog/sem2/typed_unpacked_net_timeout/typed_unpacked_net.sv.json"
#check typedUnpackedNet.e
