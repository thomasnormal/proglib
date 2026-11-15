// Replication counts with a shift atom (IEEE 1800-2023 §11.4.12.1: the count of a replication is a non-negative
// constant expression): `{(P >> l){a[0]}}` and `{(P - (P >> l)){a[N-1]}}`, a localparam shifted by a genvar (the
// Karatsuba slot widths `P >> l`). Row l-1 of `v` takes `P >> l` copies of `a[0]` (2N, then N bits) and the rest of the
// row copies of `a[N-1]`.
module gen_repa #(parameter int N = 2) (
  input  logic [N-1:0]        a,
  output logic [1:0][4*N-1:0] v
);
  localparam int P = 4 * N;
  genvar l;
  generate
    for (l = 1; l < 3; l++) begin : g_l
      assign v[l-1][0 +: (P >> l)] = {(P >> l){a[0]}};
      assign v[l-1][(P >> l) +: (P - (P >> l))] = {(P - (P >> l)){a[N-1]}};
    end
  endgenerate
endmodule
