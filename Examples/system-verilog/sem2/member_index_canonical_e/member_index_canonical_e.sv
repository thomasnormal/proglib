typedef struct packed { logic [3:0] out_dis; } ctrl_t;
module member_index_canonical_e(input logic [3:0] bits, output logic result);
  ctrl_t state;
  assign state.out_dis = bits;
  generate
    for (genvar i = 0; i < 1; i++) begin : g
      always_comb result = state.out_dis[i];
    end
  endgenerate
endmodule
