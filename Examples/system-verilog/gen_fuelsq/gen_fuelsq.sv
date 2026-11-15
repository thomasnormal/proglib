// A loop count above the linear part of the generate fuel: `P = 4 * 2**L` with `L = $clog2(N + 1)` (the Karatsuba
// padding), so `P` is up to `8N + 4`, while the fuel bound owed is `N*N + 4N + 67`: within it by `N*N >= 4N - 4`.
module gen_fuelsq #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int L = $clog2(N + 1);
  localparam int P = 4 * 2**L;
  logic [P-1:0] w;
  genvar i;
  generate
    for (i = 0; i < P; i++) begin : g_w
      assign w[i] = cin;
    end
    for (i = 0; i < N; i++) begin : g_out
      assign s[i] = a[i] ^ b[i];
    end
  endgenerate
  assign cout = w[P-1];
endmodule
