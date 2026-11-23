module comb_unpacked_output_partial_def #(parameter int W = 4) (
  input logic [W-1:0] a,
  output logic [W-1:0] y [0:W-1]
);
  genvar i;
  for (i = 0; i < W; i++) begin : g
    always_comb y[i] = a;
  end
endmodule
