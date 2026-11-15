// A localparam that sums `?:` (the form of the Dadda record's stage count) read as a variable of the obligations
// (tac9, `sv_comb.lp_atoms`), and used as a loop bound and as a loop start: `S` is the number of the thresholds 2, 4, 6
// below `N`; `y[i]` is `a[N - 1 - i]` for `i < S` and `a[i]` from `S` on.
module gen_lpat #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam int S = ((N > 2) ? 1 : 0) + ((N > 4) ? 1 : 0) + ((N > 6) ? 1 : 0);
  genvar i;
  generate
    for (i = 0; i < S; i++) begin : g_rev
      assign y[i] = a[N - 1 - i];
    end
    for (i = S; i < N; i++) begin : g_id
      assign y[i] = a[i];
    end
  endgenerate
endmodule
