// W2f: a generate block declares t, which shadows a module-scope t
// (27.4: inside g[k] the name t is the block's own variable).
module m #(parameter int unsigned N = 1) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q,
  output logic         z
);
  logic t;
  assign t = a[0];
  assign z = t;
  for (genvar k = 0; k < N; k++) begin : g
    logic t;
    assign t    = ~a[k];
    assign q[k] = t;
  end
endmodule
