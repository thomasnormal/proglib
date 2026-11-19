/- Clean-room loudness receipt for the mixed negative-edge clock/reset event list.
   The source parser retains the construct, while the ordinary loader refuses
   the unsupported timed statement instead of selecting a different edge form. -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.loader_refuse_negedge_reset.agree
open LeanModels.Sv
#guard_msgs (drop error) in
load_design_sv2 loaderRefuseNegedgeReset from
  "Examples/system-verilog/sem2/loader_refuse_negedge_reset/loader_refuse_negedge_reset.sv.json"
end Examples.«system-verilog».sem2.loader_refuse_negedge_reset.agree
