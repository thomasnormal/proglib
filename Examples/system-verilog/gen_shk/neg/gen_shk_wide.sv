// A shift of a genvar by a literal amount of 32 or more: every bit is shifted out (IEEE 1800-2023 §11.4.10), not an
// atom of the affine reading.
module gen_shk_wide #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] s
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign s[i] = a[i >> 40];
    end
  endgenerate
endmodule
