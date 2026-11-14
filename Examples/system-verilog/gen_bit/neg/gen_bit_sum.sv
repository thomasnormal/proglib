// `((i + 1) >> l)`: a shift of a sum is not an atom (only a name is shifted), so the index is refused.
module gen_bit_sum #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_node
      assign y[i] = a[(i + 1) >> 1];
    end
  endgenerate
endmodule
