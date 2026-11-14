// `3 ** (l + 1)`: a power whose exponent is a sum is not an atom; the bound is refused.
module gen_tern_sum #(parameter int N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer T = 3 ** N;
  logic [N-1:0][3*T-1:0] w;
  genvar l, t;
  generate
    for (l = 0; l < N; l++) begin : g_lvl
      for (t = 0; t < 3**(l + 1); t++) begin : g_node
        assign w[l][t] = a[l];
      end
      assign y[l] = w[l][0];
    end
  endgenerate
endmodule
