// Generate loops whose start is not an integer literal (tac9; IEEE 1800-2023 §27.4: the initialization of a loop
// generate scheme is a constant expression, evaluated once): a parameter expression (`y[i]` is `a[i] ^ b[i - h]` from
// `i = h = N - N / 2` on, `a[i] & b[i]` below), the enclosing genvar plus one (`t`: row `j` is `a[j] & b[k]` right of
// the diagonal, `a[k] ^ b[j]` on and left of it), and a `?:` in a one-iteration loop (`z`: bit `j` is `a[k]`, `k` the
// start, the mirror of `j` in the lower half).
module gen_start #(parameter int N = 4) (
  input  logic [N-1:0]          a, b,
  output logic [N-1:0]          y,
  output logic [N-1:0][N-1:0]   t,
  output logic [N-1:0]          z
);
  genvar i, j, k;
  generate
    for (i = N - N / 2; i < N; i++) begin : g_hi
      assign y[i] = a[i] ^ b[i - (N - N / 2)];
    end
    for (i = 0; i < N - N / 2; i++) begin : g_lo
      assign y[i] = a[i] & b[i];
    end
    for (j = 0; j < N; j++) begin : g_row
      for (k = j + 1; k < N; k++) begin : g_up
        assign t[j][k] = a[j] & b[k];
      end
      for (k = 0; k < j + 1; k++) begin : g_dn
        assign t[j][k] = a[k] ^ b[j];
      end
    end
    for (j = 0; j < N; j++) begin : g_mir
      for (k = (j < (N >> 1)) ? N - 1 - j : j; k < ((j < (N >> 1)) ? N - 1 - j : j) + 1; k++) begin : g_k
        assign z[j] = a[k];
      end
    end
  endgenerate
endmodule
