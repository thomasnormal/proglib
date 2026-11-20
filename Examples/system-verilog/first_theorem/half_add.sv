// A W-bit array of half adders, written with continuous assignments: the combinational example of README.md.
module half_add #(parameter int W = 4)
  (input logic [W-1:0] a, b, output logic [W-1:0] s, c);
  assign s = a ^ b;
  assign c = a & b;
endmodule
