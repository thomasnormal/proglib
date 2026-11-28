// loopfuel-audit6: exact p1_near_min_ok default-envelope regression
module a6_near_min_ff (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = -2147483641; i > -2147483648; i--) c = c + 32'd1;
    q <= c;
  end
endmodule
