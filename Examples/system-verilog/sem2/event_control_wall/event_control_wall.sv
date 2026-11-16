// IEEE 1800-2023 §§9.2 and 9.4: explicit level event control.
module event_control_wall(input logic en, input logic d, output logic q);
  always @(en) q = d;
endmodule
