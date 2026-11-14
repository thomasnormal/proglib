// `$clog2` of a quotient in a localparam (IEEE 1800-2023 §20.8.1 `$clog2`, §11.4.2 `/` truncating toward zero):
// NI = $clog2((N + 9) / 8) + 1 is the Newton step count of a Newton-Raphson divider (the least K >= 1 with
// 2^(K+2) >= N + 2). The low NI bits of `a` pass to `q` and the others are zero, so a generate condition reads NI.
module gen_clog2q #(parameter int N = 11) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  localparam integer NI = $clog2((N + 9) / 8) + 1;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      if (i < NI) begin : g_lo
        assign q[i] = a[i];
      end else begin : g_hi
        assign q[i] = 1'b0;
      end
    end
  endgenerate
endmodule
