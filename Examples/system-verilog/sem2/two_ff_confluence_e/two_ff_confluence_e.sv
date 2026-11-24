// Clean-room confluence witness: two independent NBA edge processes share one
// input clock and write disjoint registers.
module two_ff_confluence_e (
  input logic clk,
  input logic a_in,
  input logic b_in,
  output logic a_q,
  output logic b_q
);
  always_ff @(posedge clk)
    a_q <= a_in;

  always_ff @(posedge clk)
    b_q <= b_in;
endmodule
