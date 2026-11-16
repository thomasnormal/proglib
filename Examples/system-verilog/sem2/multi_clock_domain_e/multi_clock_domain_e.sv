// IEEE 1800-2023 §9.4.2: independent input clocks.
module multi_clock_domain_e(input logic aclk, input logic bclk, input logic d,
                            output logic x, output logic y);
  always_ff @(posedge aclk) x <= d;
  always_ff @(posedge bclk) y <= x;
endmodule
