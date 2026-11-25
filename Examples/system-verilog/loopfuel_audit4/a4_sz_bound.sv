// 4'(10) is signed 4'b1010 = -6: 0 trips in SV
module a4_sz_bound (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < 4'(10); i++) c = c + 32'd1;
    q <= c;
  end
endmodule
