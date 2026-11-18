// SPDX-License-Identifier: Apache-2.0
// Clean-room event-control admission fixture.
module top(input logic clk, input logic a, input logic b, output logic q_clk, output logic q_event);
  always @(posedge clk) q_clk <= a;
  always @(a or b) q_event = a ^ b;
endmodule
