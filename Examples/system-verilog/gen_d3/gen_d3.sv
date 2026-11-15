// A three-dimensional packed declaration (IEEE 1800-2023 §7.4.5, the Dadda multiplier's `T[s][k][i]`), read and written
// as a whole signal: the width is the product of the three extents.
module gen_d3 #(parameter int N = 2) (
  input  logic [1:0][N-1:0][2:0] a,
  input  logic [1:0][N-1:0][2:0] b,
  output logic [1:0][N-1:0][2:0] y
);
  logic [1:0][N-1:0][2:0] t;
  assign t = a ^ b;
  assign y = t;
endmodule
