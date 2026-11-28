// Clean-room F1 witness for four-state $onehot.
module sva_onehot (
  input logic clk,
  input logic [3:0] a,
  output logic q
);
  assign q = $onehot(a);
  assert property (@(posedge clk) $onehot(a));
endmodule
