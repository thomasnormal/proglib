// p2audit: bound -(-33'sd2147483648) = +2^31 (33-bit signed); 0 trips; q = 0 0 0
module p2_negneg33 (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = -2147483641; i > -(-33'sd2147483648); i--) c = c + 32'd1;
    q <= c;
  end
endmodule
