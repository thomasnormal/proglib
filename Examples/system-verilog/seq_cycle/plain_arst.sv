// A register with an asynchronous active-low reset and an enable, in Verilog-2001 style: a plain `always` on the
// clock's rise and the reset's fall (IEEE 1800-2017 9.2.2.1). Its `always_ff` twin is sem2/clk_arst.
module plain_arst #(parameter N = 4) (input clk, input rst_n, input en, input [N-1:0] d, output reg [N-1:0] q);
  always @(posedge clk or negedge rst_n)
    if (!rst_n) q <= {N{1'b0}};
    else if (en) q <= d;
endmodule
