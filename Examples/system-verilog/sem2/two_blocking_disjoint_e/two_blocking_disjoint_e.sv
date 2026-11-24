module two_blocking_disjoint_e(
  input logic clk,
  input logic d,
  input logic e,
  output logic a,
  output logic b
);
  always @(posedge clk) a = d;
  always @(posedge clk) b = e;
endmodule
