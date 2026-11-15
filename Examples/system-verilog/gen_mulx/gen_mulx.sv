// Products of a genvar and a shift of a localparam by an affine amount (IEEE 1800-2023 §11.4.2, §11.4.10; the
// Karatsuba slot bases `(3*t)*(P >> (l+1))`): the halves of `a` (P = 2N bits) at the slot bases `t*(P >> (l+1))`,
// swapped into `y`; `z` takes one arm of a condition on `N >> (l + 1)`; `q` reads the top bit through `P >> (j - 1)`.
module gen_mulx #(parameter int N = 4) (
  input  logic [2*N-1:0] a, b,
  output logic [2*N-1:0] y, z,
  output logic           q
);
  localparam int P = 2 * N;
  genvar l, t, j;
  generate
    for (l = 0; l < 1; l++) begin : g_l
      for (t = 0; t < 2; t++) begin : g_t
        assign y[t*(P >> (l+1)) +: (P >> (l+1))] = a[(1-t)*(P >> (l+1)) +: (P >> (l+1))];
        if ((N >> (l + 1)) == 0) begin : g_one
          assign z[t*(P >> (l+1)) +: (P >> (l+1))] = b[t*(P >> (l+1)) +: (P >> (l+1))];
        end else begin : g_more
          assign z[t*(P >> (l+1)) +: (P >> (l+1))] = a[(2*t)*(P >> (l+2)) +: (P >> (l+1))] ^ b[(1-t)*(P >> (l+1)) +: (P >> (l+1))];
        end
      end
    end
    for (j = 1; j < 2; j++) begin : g_j
      assign q = a[(P >> (j - 1)) - 1];
    end
  endgenerate
endmodule
