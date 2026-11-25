module a4_rg_evt_clk (input logic clk, input logic [7:0] d, output logic [7:0] b);
  logic [7:0] x;
  logic gclk;
  always @(clk) gclk = clk;
  always @(posedge clk) x = d;
  always @(posedge gclk) b <= x;
endmodule
