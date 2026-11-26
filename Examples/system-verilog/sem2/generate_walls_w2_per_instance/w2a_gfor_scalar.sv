// W2a: every iteration of a generate-for declares a scalar variable t.
// IEEE 1800-2023 27.4/27.6: these are N distinct variables g[0].t ... g[N-1].t.
module m #(parameter int unsigned N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    logic t;
    assign t    = ~a[k];
    assign q[k] = t;
  end
endmodule
