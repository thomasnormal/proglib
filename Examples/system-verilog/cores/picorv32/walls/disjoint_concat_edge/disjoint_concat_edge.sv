// Clean-room repro for the current scheduler wall. The two same-edge
// processes write disjoint objects, with one concatenation target.
module disjoint_concat_edge(
  input logic clk,
  input logic a,
  input logic b,
  output logic x,
  output logic [1:0] y
);
  always @(posedge clk) x = a;
  always @(posedge clk) {y[1], y[0]} = {a, b};
endmodule
