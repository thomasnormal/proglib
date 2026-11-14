// Shift and power atoms of the genvars (IEEE 1800-2023 §11.4.10, §27.4) in generate conditions, loop bounds and
// indices: `x` is a Kogge-Stone-style OR prefix whose node `i` of level `l` combines with node `i - (1 << l)` where
// `i >= (1 << l)` (a condition and an index with `1 << l`), and row `l` of `t` holds the first `1 << l` bits of `b`
// (a loop bound `1 << l`). `L = $clog2(N)` levels, so `1 << l < N` at every level.
module gen_pow #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  localparam integer L = $clog2(N);
  logic [L:0][N-1:0] x;
  logic [L:0][N-1:0] t;
  genvar i, l;
  generate
    for (i = 0; i < N; i++) begin : g_in
      assign x[0][i] = a[i];
    end
    for (l = 0; l < L; l++) begin : g_lvl
      for (i = 0; i < N; i++) begin : g_node
        if (i >= (1 << l)) begin : g_op
          assign x[l+1][i] = x[l][i] | x[l][i - (1 << l)];
        end else begin : g_pass
          assign x[l+1][i] = x[l][i];
        end
      end
      for (i = 0; i < (1 << l); i++) begin : g_tri
        assign t[l][i] = b[i];
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      assign y[i] = x[L][i];
    end
  endgenerate
endmodule
