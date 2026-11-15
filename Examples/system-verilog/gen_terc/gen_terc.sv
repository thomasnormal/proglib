// `?:` of the parameters and genvars where an affine form is read (tac8, IEEE 1800-2023 §11.4.11 over `int` operands):
// an index, `a[(k == 0) ? N - 1 : k - 1]` (`y` is `a` rotated up by one), and a loop bound, `j < ((N > 1) ? N - 1 : 0)`
// (`z` is `a` rotated down by one; at `N = 1` the loop runs no iteration).
module gen_terc #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y,
  output logic [N-1:0] z
);
  genvar k, j;
  generate
    for (k = 0; k < N; k++) begin : g_y
      assign y[k] = a[(k == 0) ? N - 1 : k - 1];
    end
    for (j = 0; j < ((N > 1) ? N - 1 : 0); j++) begin : g_z
      assign z[j] = a[j + 1];
    end
  endgenerate
  assign z[N-1] = a[0];
endmodule
