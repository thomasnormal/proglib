// A select of a three-dimensional packed declaration whose plane range is not zero-based (`[2:1]`): the summary reads
// the selects of zero-based descending declarations only, so the select is refused, naming the declaration.
module gen_d3_nz #(parameter int N = 2) (
  input  logic [2:1][N-1:0][2:0] a,
  output logic                   y
);
  logic [2:1][N-1:0][2:0] t;
  assign t = a;
  assign y = t[1][0][2];
endmodule
