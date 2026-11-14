// `$clog2` of a quotient that is negative for small N: (N - 20) / 8 is -1 at N <= 12 (`/` truncates toward zero,
// IEEE 1800-2023 §11.4.2), where the instantiation refuses `$clog2` of a negative value; at N >= 13 it is at least 0.
module gen_clog2q_neg #(parameter int N = 30) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  localparam integer NI = $clog2((N - 20) / 8) + 1;
  assign q = a;
endmodule
