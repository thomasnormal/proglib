import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.port_connection_target_struct_array.agree
open LeanModels.Sv

/- The whole unpacked aggregate target is retained as a parser-native
`AggregateMember` target.  The source-shaped process then reaches the
canonical scheduler refusal for the multi-write `always_comb` body. -/
#guard_msgs (whitespace := lax) in
load_design_sv2 registerParent from
  "Examples/system-verilog/sem2/port_connection_target_struct_array/port_connection_target_struct_array.sv.json"

#guard match registerParent.pdesign.generates with
  | [GenItem.inst
      { name := _, module := _, path := _, params := _,
        conns := [PConn.input _ (some (.ident "d")) false,
          PConn.output _ (some (.aggregateMember "state" []))] }] => true
  | _ => false

end Examples.«system-verilog».sem2.port_connection_target_struct_array.agree
