// A Kogge-Stone parallel-prefix adder (Kogge and Stone, 1973), written for this example from the textbook
// construction. Column 0 carries the carry in (generate `cin`, propagate 0) and column k + 1 is bit k (generate
// `a & b`, propagate `a ^ b`). Round r joins column k with column k - 2^r where that column exists and copies it
// otherwise, so after R = $clog2(N + 1) rounds G[R][k] is the carry into bit k. Every index is computed at
// elaboration time from the genvars and the parameter.
module prefix_ks #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int R = $clog2(N + 1);
  logic [R:0][N:0] G, P;
  genvar r, k;
  assign G[0][0] = cin;
  assign P[0][0] = 1'b0;
  generate
    for (k = 0; k < N; k++) begin : g_col
      assign G[0][k+1] = a[k] & b[k];
      assign P[0][k+1] = a[k] ^ b[k];
    end
    for (r = 0; r < R; r++) begin : g_round
      for (k = 0; k < N + 1; k++) begin : g_node
        if (k >= (1 << r)) begin : g_join
          assign G[r+1][k] = G[r][k] | (P[r][k] & G[r][k - (1 << r)]);
          assign P[r+1][k] = P[r][k] & P[r][k - (1 << r)];
        end else begin : g_copy
          assign G[r+1][k] = G[r][k];
          assign P[r+1][k] = P[r][k];
        end
      end
    end
    for (k = 0; k < N; k++) begin : g_sum
      assign s[k] = P[0][k+1] ^ G[R][k];
    end
  endgenerate
  assign cout = G[R][N];
endmodule
