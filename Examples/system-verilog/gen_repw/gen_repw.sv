// Replications of a whole signal (tac8, W9's restriction): `{(P >> l){cin}}` replicates a 1-bit port with a shift atom
// as the count, `{(P >> 2){d}}` a 2-bit signal, `{2{a}}` a whole N-bit port with a literal count. Until tac8 the
// fragment replicated a sized literal, a bit select or a part select only.
module gen_repw #(parameter int N = 4) (
  input  logic [N-1:0]   a,
  input  logic           cin,
  input  logic [1:0]     d,
  output logic [4*N-1:0] y0, y1,
  output logic [2*N-1:0] y2
);
  localparam int P = 4 * N;
  logic [1:0][P-1:0] g;
  genvar l;
  generate
    for (l = 0; l < 2; l++) begin : g_lvl
      assign g[l][0 +: (P >> l)] = {(P >> l){cin}};
    end
  endgenerate
  assign g[1][P-1 -: (P >> 1)] = {(P >> 2){d}};
  assign y0 = g[0];
  assign y1 = g[1];
  assign y2 = {2{a}};
endmodule
