module profile_comb_defaults(input logic clk, input logic sel, input logic [3:0] a, input logic [3:0] b,
           output logic [3:0] comb, output logic [3:0] q);
  always_comb begin
    comb = a;
    if (sel) comb = b;
    else comb = a;
  end
  always_ff @(posedge clk) q <= a;
endmodule
