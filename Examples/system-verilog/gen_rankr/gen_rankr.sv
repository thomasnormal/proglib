// Rank obligations stated with the windows in range (tac8, `set_option sv_comb.rank_ranged true`): two levels of a
// 2-D array, each level the halves of the one before it swapped, the halves at the slot bases `t*(P >> j)` (products of
// a genvar and a shift atom). A rank goal reads the overlap of two row-major windows; its columns lie inside their rows
// by the in-range facts of the two windows, which the ranged form states as premises. The one-iteration loop `j`
// names the shift amount (`P >> j`, an atom: a shift by a literal amount would simplify to `N`).
module gen_rankr #(parameter int N = 4) (
  input  logic [2*N-1:0] a,
  output logic [2*N-1:0] y
);
  localparam int P = 2 * N;
  logic [2:0][P-1:0] v;
  assign v[0] = a;
  genvar l, j, t;
  generate
    for (l = 0; l < 2; l++) begin : g_l
      for (j = 1; j < 2; j++) begin : g_j
        for (t = 0; t < 2; t++) begin : g_t
          assign v[l+1][t*(P >> j) +: (P >> j)] = v[l][(1-t)*(P >> j) +: (P >> j)];
        end
      end
    end
  endgenerate
  assign y = v[2];
endmodule
