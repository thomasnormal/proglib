import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.port_connection_target_struct_array.agree

/- The structured output connection target is intentionally outside the
current §23.2.2 admission slice. -/
#guard_msgs (whitespace := lax) in
load_design_sv2 registerParent from
  "Examples/system-verilog/sem2/port_connection_target_struct_array/port_connection_target_struct_array.sv.json"

end Examples.«system-verilog».sem2.port_connection_target_struct_array.agree
