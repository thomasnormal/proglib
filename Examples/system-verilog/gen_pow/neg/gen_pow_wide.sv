// `1 << l` over every `l < N`: the atom is in range (a 32-bit `int`, IEEE 1800-2023 §11.4.10) only while `l <= 30`, an
// obligation that holds under `N <= 31` and is false under `N < 2^31 - 1` alone.
module gen_pow_wide #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  genvar l;
  generate
    for (l = 0; l < N; l++) begin : g_lvl
      if ((1 << l) > 0) begin : g_pos
        assign y[l] = a[l];
      end else begin : g_neg
        assign y[l] = ~a[l];
      end
    end
  endgenerate
endmodule
