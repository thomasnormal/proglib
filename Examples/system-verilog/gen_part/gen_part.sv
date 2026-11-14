// Indexed part selects `+:` and `-:` (IEEE 1800-2023 §11.5.1) with affine bases and constant widths, as `sv_comb` test
// subjects: the targets `g[l][2*i +: 2]` (a part of a row of a 2-D array), `w[2*i +: 2]` and `y[2*i+1 -: 2]` (parts
// of vectors), and the reads `g[1][2*i +: 2]` and `w[i*2 +: 2]`. Bit 2i+1 of row l of `g` is a[i], bit 2i is b[i];
// `y` gets the rows' pairs back, `z[i] = a[i] ^ b[i]`.
module gen_part #(parameter int N = 4) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] y,
  output logic [N-1:0]   z
);
  logic [1:0][2*N-1:0] g;
  logic [2*N-1:0] w;
  genvar l, i;
  generate
    for (l = 0; l < 2; l++) begin : g_lvl
      for (i = 0; i < N; i++) begin : g_node
        assign g[l][2*i +: 2] = {a[i], b[i]};
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      assign w[2*i +: 2] = g[1][2*i +: 2];
      assign y[2*i+1 -: 2] = w[i*2 +: 2];
      assign z[i] = g[0][2*i+1] ^ w[2*i];
    end
  endgenerate
endmodule
