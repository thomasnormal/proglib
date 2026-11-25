module a4_rg_evt1 (input logic clk, input logic d, output logic b);
  logic x, w;
  always @(x) w = x;
  always @(posedge clk) x = d;
  always @(posedge clk) b <= w;
endmodule
