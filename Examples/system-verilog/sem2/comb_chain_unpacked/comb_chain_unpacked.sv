module comb_chain_unpacked #(parameter int W = 8) (
  input logic clk,
  output logic [W-1:0] q
);
  logic [W-1:0] s [0:2];
  assign s[0] = q;
  genvar i;
  for (i = 0; i < 2; i++) begin : step
    assign s[i+1] = s[i] >> 1;
  end
  always_ff @(posedge clk) q <= s[2];
endmodule
