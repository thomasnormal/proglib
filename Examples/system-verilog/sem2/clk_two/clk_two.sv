// Multi-clock source fixture. Ordinary run2 refuses the two-clock shape;
// canonical E keeps source-shaped edge processes, while schedule-sensitive
// observations remain outside this receipt.
module clk_two (
  input  logic clk1, clk2, d,
  output logic a, b
);
  always_ff @(posedge clk1) a <= d;
  always_ff @(posedge clk2) b <= a;
endmodule
