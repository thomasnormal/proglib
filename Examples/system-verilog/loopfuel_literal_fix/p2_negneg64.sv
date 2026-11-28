// p2audit: bound -(-64'sd2147483648) = +2^31 (64-bit); i > 2^31 never holds: 0 trips; q = 0 0 0
module p2_negneg64 (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = -2147483641; i > -(-64'sd2147483648); i--) c = c + 32'd1;
    q <= c;
  end
endmodule
