module profile_comb_chain3(input logic clk, input logic [3:0] a,
           output logic [3:0] c1, output logic [3:0] c2,
           output logic [3:0] comb, output logic [3:0] q);
  always_comb begin
    c1 = a;
    c2 = c1;
    comb = c2;
  end
  always_ff @(posedge clk) q <= a;
endmodule
