// A ternary XOR tree of depth L = $clog2((N + 3) / 4), the level structure of a Karatsuba multiplier: level l holds
// 3 ** l nodes (a loop bound that is a power of the enclosing genvar, IEEE 1800-2023 §11.4.3), node t the XOR of nodes
// 3t, 3t + 1, 3t + 2 of level l + 1, and the T = 3 ** L leaves copy a[0]. T is a power of a `$clog2` of a quotient: the
// parameter stage evaluates both at a symbolic N.
module gen_ktree #(parameter int N = 16) (
  input  logic [N-1:0] a,
  output logic         y
);
  localparam integer L = $clog2((N + 3) / 4);
  localparam integer T = 3 ** L;
  logic [L:0][T-1:0] v;
  genvar l, t;
  generate
    for (t = 0; t < T; t++) begin : g_leaf
      assign v[L][t] = a[0];
    end
    for (l = 0; l < L; l++) begin : g_lvl
      for (t = 0; t < 3**l; t++) begin : g_node
        assign v[l][t] = (v[l+1][3*t] ^ v[l+1][3*t+1]) ^ v[l+1][3*t+2];
      end
    end
  endgenerate
  assign y = v[0][0];
endmodule
