// `?:` operands of generate-if conditions (tac8, IEEE 1800-2023 §11.4.11, §27.5): the condition `k < ((N > 2) ? N - 2 : 0)`
// compares a genvar with a `?:` of the parameter, and `k >= ((k < 2) ? k : N - 1)` has a `?:` of a genvar on the right.
// `y[k]` is `a[k + 1]` below `N - 2` (none at N <= 2) and `a[k]` above; `z[k]` is `b[k]` at the top bit and below 2, and
// its complement elsewhere.
module gen_tercg #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y, z
);
  genvar k;
  generate
    for (k = 0; k < N; k++) begin : g_y
      if (k < ((N > 2) ? N - 2 : 0)) begin : g_lo
        assign y[k] = a[k + 1];
      end else begin : g_hi
        assign y[k] = a[k];
      end
      if (k >= ((k < 2) ? k : N - 1)) begin : g_keep
        assign z[k] = b[k];
      end else begin : g_flip
        assign z[k] = ~b[k];
      end
    end
  endgenerate
endmodule
