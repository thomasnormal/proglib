// IEEE 1800-2023 §10.9: parameter default assignment pattern.
module assignment_pattern_param_e #(parameter logic [3:0] P = '{default: 4'h0})
  (input logic [3:0] x, output logic [3:0] y);
  assign y = P ^ x;
endmodule
