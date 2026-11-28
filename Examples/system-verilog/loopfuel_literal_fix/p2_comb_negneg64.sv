// p2audit: always_comb, bound +2^31 (64-bit): 0 trips; q = 0 0 0
module p2_comb_negneg64 (input logic clk, input logic [7:0] a, output logic [31:0] q);
  always_comb begin
    q = {24'b0, a} & 32'd0;
    for (int i = -2147483641; i > -(-64'sd2147483648); i--) q = q + 32'd1;
  end
endmodule
