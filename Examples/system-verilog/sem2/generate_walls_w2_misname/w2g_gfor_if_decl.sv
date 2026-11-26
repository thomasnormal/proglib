// W2g: a generate-if inside a generate-for; each arm declares t.
// At N = 2 the active blocks are g[0].a0.t and g[1].a1.t.
module m #(parameter int unsigned N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    if (k == 0) begin : a0
      logic t;
      assign t    = a[k];
      assign q[k] = t;
    end else begin : a1
      logic t;
      assign t    = ~a[k];
      assign q[k] = t;
    end
  end
endmodule
