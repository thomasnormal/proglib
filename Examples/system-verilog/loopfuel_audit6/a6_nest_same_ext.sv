// loopfuel-audit6: nested loops reuse a module-scope integer iterator and do not terminate
module a6_nest_same_ext (output logic [31:0] q);
  integer i;
  always_comb begin
    q = 32'd0;
    for (i = 0; i < 4; i = i + 1)
      for (i = 0; i < 2; i = i + 1) q = q + 32'd1;
  end
endmodule
