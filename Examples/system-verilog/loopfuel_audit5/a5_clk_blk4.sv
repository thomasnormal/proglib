// loopfuel-audit5: x written by an always_ff blocking assignment
module a5_clk_blk4 (input logic clk, input logic d, input logic d2, output logic b);
  logic g, x;
  always @(posedge clk) begin g = d2; end
  always @(posedge g) b <= x;
  always_ff @(posedge clk) x = d;
endmodule
