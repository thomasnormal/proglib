// Dynamic indexed part select through a packed struct member.
module member_indexed_range(
  input logic [33:0] p_i,
  input logic [1:0] base,
  output logic [15:0] y
);
  typedef struct packed { logic [3:0][7:0] bytes; logic [1:0] tag; } pkt_t;
  pkt_t p;
  assign p = p_i;
  assign y = p.bytes[base +: 2];
endmodule
