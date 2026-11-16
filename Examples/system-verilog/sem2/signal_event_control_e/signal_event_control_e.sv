module signal_event_control_e(input logic clk, d, output logic q);
  always_ff @(clk) q <= d;
endmodule
