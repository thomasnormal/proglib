// loopfuel-audit6: signed int bound at INT_MIN, seven iterations, q = 7
module a6_near_min (output logic [31:0] q);
  always_comb begin
    q = 32'd0;
    for (int i = -2147483641; i > -2147483648; i--) q = q + 32'd1;
  end
endmodule
