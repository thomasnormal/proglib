module constant_width_conversion_e #(parameter integer E = 8)(input logic x, output logic y);
  localparam integer BASE = (1 << (E - 1)) - 1;
  localparam signed [11:0] DOUBLE = 2 * BASE;
  assign y = x ^ DOUBLE[0];
endmodule
