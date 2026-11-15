// Planes of a three-dimensional packed array whose middle dimension is a parameter (tac8): `T[0]`, `T[1]` are read and
// written as whole planes (the envelope's legacy select over a 3-D declaration: one `elemW`-bit chunk, a plane), and
// `y` is one cell of the last plane: `y` is bit `3*(N-1) + 2` of `a`.
module gen_d3p #(parameter int N = 2) (
  input  logic [3*N-1:0] a,
  output logic           y
);
  logic [1:0][N-1:0][2:0] T;
  assign T[0] = a;
  assign T[1] = T[0];
  assign y = T[1][N-1][2];
endmodule
