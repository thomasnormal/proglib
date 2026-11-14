// `2 << l` is not one of the atoms (`1 << n`, `b ** n`, `m >> n`, `(m >> n) << n`, `(m >> n) & 1`): the index is refused.
module gen_pow_two #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer L = $clog2(N);
  genvar l;
  generate
    for (l = 0; l < L; l++) begin : g_lvl
      assign y[l] = a[(2 << l) - 2];
    end
  endgenerate
endmodule
