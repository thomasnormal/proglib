// A genvar times a QUOTIENT (`t * (P / 2)`): the product reading takes a form of names times an atom form of shifts and
// powers; a quotient atom is not one, so the index is not affine: refused, naming the site.
module gen_mulx_quot #(parameter int N = 4) (
  input  logic [2*N-1:0] a,
  output logic [2*N-1:0] y
);
  localparam int P = 2 * N;
  genvar t;
  generate
    for (t = 0; t < 2; t++) begin : g_t
      assign y[t*(P / 2) +: (P / 2)] = a[t*(P / 2) +: (P / 2)];
    end
  endgenerate
endmodule
