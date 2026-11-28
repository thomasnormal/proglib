// p2audit: 64'shFFFFFFFF80000000 = -2^31 (64-bit); negated = +2^31; 0 trips; q = 0 0 0
module p2_neg_wide_hex (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = -2147483641; i > -64'shFFFFFFFF80000000; i--) c = c + 32'd1;
    q <= c;
  end
endmodule
