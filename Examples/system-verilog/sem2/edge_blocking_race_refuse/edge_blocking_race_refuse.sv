// Two same-edge blocking processes communicate through a variable.
// IEEE 1800-2023 §4.7 leaves their active-region order open, so the
// canonical executor refuses this schedule-dependent shape.
module edge_blocking_race_refuse(input logic clk, d, output logic a, b);
  always_ff @(posedge clk) a = d;
  always_ff @(posedge clk) b = a;
endmodule
