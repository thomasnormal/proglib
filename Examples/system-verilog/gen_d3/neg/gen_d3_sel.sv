// A select of a three-dimensional packed declaration (`t[1][0][2]`): the summary reads selects of one- and
// two-dimensional declarations only, so the select is refused, naming it.
module gen_d3_sel #(parameter int N = 2) (
  input  logic [1:0][N-1:0][2:0] a,
  output logic                   y
);
  logic [1:0][N-1:0][2:0] t;
  assign t = a;
  assign y = t[1][0][2];
endmodule
