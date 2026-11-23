module edge_multiple_write_nba_refuse(
  input logic clk,
  input logic d,
  input logic e,
  output logic a
);
  always @(posedge clk) a <= d;
  always @(posedge clk) a <= e;
endmodule
