import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.port_connection_target_struct_array.agree
open LeanModels.Sv

/- The whole unpacked aggregate target is retained as a parser-native
`PortConnection:target` refusal.  The canonical aggregate store currently
has member-path reads and writes, but no whole-aggregate port-copy relation. -/
#guard_msgs (whitespace := lax) in
load_design_sv2 registerParent from
  "Examples/system-verilog/sem2/port_connection_target_struct_array/port_connection_target_struct_array.sv.json"

#guard match registerParent.pdesign.generates with
  | [GenItem.inst
      { name := _, module := _, path := _, params := _,
        conns := [PConn.input _ (some (.ident "d")) false,
          PConn.unsupported _ "PortConnection:target" "hwif_out"] }] => true
  | _ => false

end Examples.«system-verilog».sem2.port_connection_target_struct_array.agree
