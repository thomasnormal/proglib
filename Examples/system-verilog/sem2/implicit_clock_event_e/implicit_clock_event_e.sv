module implicit_clock_event_e(input wire clk, d, output reg q);
  always_ff @(clk) q <= d;
endmodule
