// The bit test `((i >> l) & 1) == 1` of two genvars (IEEE 1800-2023 §11.4.8, §11.4.10, §27.5) in a generate condition
// and `((i >> l) << l) - 1` in an index: a Sklansky-style OR prefix whose node `i` of level `l`, where bit `l` of `i` is
// set, combines with the top node of the block below it. `L = $clog2(N)` levels.
module gen_bit #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer L = $clog2(N);
  logic [L:0][N-1:0] x;
  genvar i, l;
  generate
    for (i = 0; i < N; i++) begin : g_in
      assign x[0][i] = a[i];
    end
    for (l = 0; l < L; l++) begin : g_lvl
      for (i = 0; i < N; i++) begin : g_node
        if (((i >> l) & 1) == 1) begin : g_op
          assign x[l+1][i] = x[l][i] | x[l][((i >> l) << l) - 1];
        end else begin : g_pass
          assign x[l+1][i] = x[l][i];
        end
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      assign y[i] = x[L][i];
    end
  endgenerate
endmodule
