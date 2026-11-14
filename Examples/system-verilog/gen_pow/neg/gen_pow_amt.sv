// A shift by a sum (`1 << (l + 1)`) is not an atom: the condition is refused.
module gen_pow_amt #(parameter int N = 4) (
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
        if (i >= (1 << (l + 1))) begin : g_op
          assign x[l+1][i] = x[l][i];
        end else begin : g_pass
          assign x[l+1][i] = ~x[l][i];
        end
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      assign y[i] = x[L][i];
    end
  endgenerate
endmodule
