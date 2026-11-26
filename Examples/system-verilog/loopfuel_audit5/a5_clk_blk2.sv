// loopfuel-audit5: a5_clk_blk1 with the writers swapped in source order
module a5_clk_blk2 (input logic clk, input logic d, input logic d2, output logic b);
  logic g, x;
  always @(posedge clk) x = d;
  always @(posedge clk) g = d2;
  always @(posedge g) b <= x;
endmodule
