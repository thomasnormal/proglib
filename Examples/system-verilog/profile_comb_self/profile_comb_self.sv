module profile_comb_self(input logic clk, input logic [3:0] a,
           output logic [3:0] comb, output logic [3:0] q);
  always_comb comb = comb ^ a;
  always_ff @(posedge clk) q <= comb;
endmodule
