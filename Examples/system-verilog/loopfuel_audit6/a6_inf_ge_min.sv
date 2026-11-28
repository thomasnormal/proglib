// loopfuel-audit6: signed int >= INT_MIN wraps and never terminates, so refuse
module a6_inf_ge_min (output logic [31:0] q);
  always_comb begin
    q = 32'd0;
    for (int i = -2147483646; i >= -2147483648; i--) q = q + 32'd1;
  end
endmodule
