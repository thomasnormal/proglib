// A power `3 ** l` of a genvar (IEEE 1800-2023 §11.4.3) in a loop bound: a ternary XOR tree whose level `l` holds
// `3 ** l` nodes, each the XOR of its three children at level `l + 1`; the `T = 3 ** N` leaves copy `a[0]`.
module gen_tern #(parameter int N = 2) (
  input  logic [N-1:0] a,
  output logic         y
);
  localparam integer T = 3 ** N;
  logic [N:0][T-1:0] v;
  genvar l, t;
  generate
    for (t = 0; t < T; t++) begin : g_leaf
      assign v[N][t] = a[0];
    end
    for (l = 0; l < N; l++) begin : g_lvl
      for (t = 0; t < 3**l; t++) begin : g_node
        assign v[l][t] = (v[l+1][3*t] ^ v[l+1][3*t+1]) ^ v[l+1][3*t+2];
      end
    end
  endgenerate
  assign y = v[0][0];
endmodule
