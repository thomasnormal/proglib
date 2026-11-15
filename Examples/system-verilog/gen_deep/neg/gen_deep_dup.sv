// Two blocks with the same label at the same depth (`g_b` under `g_x` and under `g_y`, each holding one site): distinct
// scopes (IEEE 1800-2023 §27.6), named by their label paths `g_x.g_b` and `g_y.g_b` (tac7; refused before).
module gen_deep_dup #(parameter int N = 4) (
  input  logic [N-1:0]        a,
  output logic [1:0][N-1:0]   z
);
  genvar i, j;
  generate
    for (i = 0; i < 1; i++) begin : g_x
      for (j = 0; j < N; j++) begin : g_b
        assign z[0][j] = a[j];
      end
    end
    for (i = 0; i < 1; i++) begin : g_y
      for (j = 0; j < N; j++) begin : g_b
        assign z[1][j] = a[j];
      end
    end
  endgenerate
endmodule
