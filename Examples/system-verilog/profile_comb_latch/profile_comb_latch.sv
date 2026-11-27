module profile_comb_latch(input logic clk, input logic en, input logic [3:0] d,
           output logic [3:0] comb, output logic [3:0] q);
  always_comb begin
    if (en) comb = d;
  end
  always_ff @(posedge clk) q <= comb;
endmodule
