// loopfuel-audit5: reader first in source order
module a5_clk_blk3 (input logic clk, input logic d, input logic d2, output logic b);
  logic g, x;
  always @(posedge g) b <= x;
  always @(posedge clk) g = d2;
  always @(posedge clk) x = d;
endmodule
