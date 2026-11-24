module plain_event_any_edge_e (input logic clk, input logic d, output logic q);
  always_ff @(clk) q <= d;
endmodule
