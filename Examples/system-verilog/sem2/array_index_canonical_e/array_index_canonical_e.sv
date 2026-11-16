module array_index_canonical_e (input logic [1:0] i, output logic [7:0] y);
  logic [7:0] values [0:3];
  always_comb y = values[i];
endmodule
