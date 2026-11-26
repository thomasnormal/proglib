// W2e: two sibling generate-for loops each declare t (distinct scopes g[k].t
// and h[k].t), one iteration each at N = 1.
module m #(parameter int unsigned N = 1) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q,
  output logic [N-1:0] p
);
  for (genvar k = 0; k < N; k++) begin : g
    logic t;
    assign t    = a[k];
    assign q[k] = t;
  end
  for (genvar k = 0; k < N; k++) begin : h
    logic t;
    assign t    = ~a[k];
    assign p[k] = t;
  end
endmodule
