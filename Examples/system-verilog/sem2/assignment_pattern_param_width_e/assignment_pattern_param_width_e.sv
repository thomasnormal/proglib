// IEEE 1800-2023 §10.9: parameter-dependent packed default pattern.
module assignment_pattern_param_width_e #(parameter int W = 4,
    parameter logic [W-1:0] P = '{default: 1'b0})
  (input logic [W-1:0] x, output logic [W-1:0] y);
  assign y = P ^ x;
endmodule
