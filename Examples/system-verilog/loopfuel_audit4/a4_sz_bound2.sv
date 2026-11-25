// 2'(5) is signed 2'b01 = 1: 1 trip in SV
module a4_sz_bound2 (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < 2'(5); i++) c = c + 32'd1;
    q <= c;
  end
endmodule
