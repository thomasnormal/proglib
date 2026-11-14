// Shifts of a genvar by a literal amount (IEEE 1800-2023 §11.4.10, the amount an unsigned constant): `(i >> 1) << 1`
// clears bit 0 of `i` (the Sklansky partner column), `i >> 2` is a quarter of it; in an index and in a generate
// condition.
module gen_shk #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] s, t
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i] = a[(i >> 1) << 1] ^ b[i];
      if ((i >> 2) == 0) begin : g_lo
        assign t[i] = a[i];
      end else begin : g_hi
        assign t[i] = b[i >> 2];
      end
    end
  endgenerate
endmodule
