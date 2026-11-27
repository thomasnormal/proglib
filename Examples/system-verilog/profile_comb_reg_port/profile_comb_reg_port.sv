module profile_comb_reg_port(input logic clk, input logic [3:0] a, input logic [3:0] d,
           output logic [3:0] comb, output logic [3:0] q);
  logic [3:0] r;
  always_comb comb = r ^ a;
  always_ff @(posedge clk) begin
    r <= d;
    q <= d;
  end
endmodule
