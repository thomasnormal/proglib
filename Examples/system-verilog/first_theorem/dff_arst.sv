// A W-bit D register with an active-low asynchronous reset: the clocked example of README.md.
module dff_arst #(parameter int W = 4)
  (input logic clk, rst_n, input logic [W-1:0] d, output logic [W-1:0] q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else q <= d;
endmodule
