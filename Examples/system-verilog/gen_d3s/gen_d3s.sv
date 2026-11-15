// Selects of a three-dimensional packed array (tac8): a plane, rows, cells and parts of rows, over the nested
// row-major geometry `T[s][k][i]` = bit `(s * 3 + k) * 4 + i`.
//
// T[0] is the low plane of `a`; plane `s` of `T` is plane `s - 1` XOR plane `s` of `a`, row by row; `U[s][k]` is row
// `k` of `T[s]` with its two halves swapped, part by part; `z` is the last plane of `U` XOR the first of `T`, cell by
// cell, and `q` is the last plane of `U`.
module gen_d3s #(parameter int N = 2) (
  input  logic [12*N-1:0] a,
  output logic [11:0]     z,
  output logic [11:0]     q
);
  logic [N-1:0][2:0][3:0] T, U;
  assign T[0] = a[11:0];
  genvar s, k, i;
  generate
    for (s = 1; s < N; s++) begin : g_s
      for (k = 0; k < 3; k++) begin : g_row
        assign T[s][k] = T[s-1][k] ^ a[12*s + 4*k +: 4];
      end
    end
    for (s = 0; s < N; s++) begin : g_u
      for (k = 0; k < 3; k++) begin : g_part
        assign U[s][k][1:0] = T[s][k][3:2];
        assign U[s][k][3:2] = T[s][k][1:0];
      end
    end
    for (k = 0; k < 3; k++) begin : g_k
      for (i = 0; i < 4; i++) begin : g_cell
        assign z[4*k + i] = U[N-1][k][i] ^ T[0][k][i];
      end
    end
  endgenerate
  assign q = U[N-1];
endmodule
