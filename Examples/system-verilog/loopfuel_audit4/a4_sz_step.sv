// 2'(3) is signed 2'b11 = -1: i counts down to -2^31 and wraps above 10: 2^31 + 1 trips in SV
module a4_sz_step (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < 10; i += 2'(3)) c = c + 32'd1;
    q <= c;
  end
endmodule
