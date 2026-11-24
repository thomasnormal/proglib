module simultaneous_nba (
    input logic clk_a,
    input logic clk_b,
    output logic a,
    output logic b
);
  always_ff @(posedge clk_a) a <= b;
  always_ff @(posedge clk_b) b <= a;
endmodule
