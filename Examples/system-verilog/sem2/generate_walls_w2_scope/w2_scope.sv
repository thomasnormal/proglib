// W2s: direct declarations in a generate-for need per-instance scope names.
module w2_scope #(parameter int unsigned N = 2) (
  input logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    logic t;
    assign t = a[k];
    assign q[k] = t;
  end
endmodule
