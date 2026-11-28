// Clean-room F1 witness for sampled $countbits.
module sva_countbits (
  input logic clk,
  input logic [3:0] a,
  output logic q
);
  assign q = 1'b0;
  assert property (@(posedge clk) $countbits(a, 1'b1) == 32'd1);
endmodule
