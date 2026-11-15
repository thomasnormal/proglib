// A localparam that sums many `?:` (the form of the Dadda record's stage count, which has 51), and localparams built
// from it with `*` by a literal, `-` and a `?:`, read node by node by the parameter stage (tac10, `closeParamEnvComp`):
// `S` is the number of the thresholds 2, 3, 4, 6, 9, ... (24 of them, the Dadda heights) below `N`, `D = 2 * S - S` is
// `S` again, `NP = (N < 2) ? 2 : N` (bound by the parameter stage, read nowhere); `y[i]` is `a[0]` for `i < D` and
// `a[N - 1]` from `D` on (`y` has `N + 24` bits, so that `D` is a bound below its width at every `N`).
module gen_lpsum #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N+23:0] y
);
  localparam int S = ((N > 2) ? 1 : 0) + ((N > 3) ? 1 : 0) + ((N > 4) ? 1 : 0) + ((N > 6) ? 1 : 0) +
                     ((N > 9) ? 1 : 0) + ((N > 13) ? 1 : 0) + ((N > 19) ? 1 : 0) + ((N > 28) ? 1 : 0) +
                     ((N > 42) ? 1 : 0) + ((N > 63) ? 1 : 0) + ((N > 94) ? 1 : 0) + ((N > 141) ? 1 : 0) +
                     ((N > 211) ? 1 : 0) + ((N > 316) ? 1 : 0) + ((N > 474) ? 1 : 0) + ((N > 711) ? 1 : 0) +
                     ((N > 1066) ? 1 : 0) + ((N > 1599) ? 1 : 0) + ((N > 2398) ? 1 : 0) + ((N > 3597) ? 1 : 0) +
                     ((N > 5395) ? 1 : 0) + ((N > 8092) ? 1 : 0) + ((N > 12138) ? 1 : 0) + ((N > 18207) ? 1 : 0);
  localparam int D = 2 * S - S;
  localparam int NP = (N < 2) ? 2 : N;
  genvar i;
  generate
    for (i = 0; i < D; i++) begin : g_lo
      assign y[i] = a[0];
    end
    for (i = D; i < N + 24; i++) begin : g_hi
      assign y[i] = a[N - 1];
    end
  endgenerate
endmodule
