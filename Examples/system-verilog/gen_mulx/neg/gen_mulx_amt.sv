// A shift by the sum of two genvars (`P >> (l + t)`): an affine shift amount is ONE name plus or minus a literal
// (`affAmt?`), so the index is not affine: refused, naming the site.
module gen_mulx_amt #(parameter int N = 4) (
  input  logic [2*N-1:0] a,
  output logic [2*N-1:0] y
);
  localparam int P = 2 * N;
  genvar l, t;
  generate
    for (l = 0; l < 1; l++) begin : g_l
      for (t = 0; t < 2; t++) begin : g_t
        assign y[t] = a[P >> (l + t)];
      end
    end
  endgenerate
endmodule
