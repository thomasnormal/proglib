module backreg_e(input logic clk, input logic [3:0] x, output logic [3:0] a);
  logic [3:0] b, c, q;
  assign a = b;
  assign b = c;
  assign c = q;
  always_ff @(posedge clk) q <= x;
endmodule
