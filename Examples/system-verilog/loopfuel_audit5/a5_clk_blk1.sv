// loopfuel-audit5: clock made by a blocking write in a same-edge process: the posedge-g reader races the x writer (4.7)
module a5_clk_blk1 (input logic clk, input logic d, input logic d2, output logic b);
  logic g, x;
  always @(posedge clk) g = d2;
  always @(posedge clk) x = d;
  always @(posedge g) b <= x;
endmodule
