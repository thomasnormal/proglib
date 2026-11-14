// `(i >> l) & 2` tests bit `l + 1`: only `& 1` is the bit atom, so the condition is refused.
module gen_bit_two #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer L = $clog2(N);
  genvar i, l;
  generate
    for (l = 0; l < L; l++) begin : g_lvl
      for (i = 0; i < N; i++) begin : g_node
        if (((i >> l) & 2) == 2) begin : g_op
          assign y[i] = a[i];
        end
      end
    end
  endgenerate
endmodule
