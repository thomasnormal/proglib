typedef struct packed { logic [7:0] value; } word_t;
module member_range_canonical_e(input logic [7:0] bits, output logic [1:0] result);
  word_t state;
  assign state.value = bits;
  generate
    for (genvar i = 0; i < 1; i++) begin : g
      always_comb result = state.value[i+1:i];
    end
  endgenerate
endmodule
