// SPDX-License-Identifier: Apache-2.0
// IEEE 1800-2023 §6.6: equal-strength continuous drivers resolve per bit.
module resolved_net_canonical_e(input logic a, input logic b);
  wire y;

  assign y = a;
  assign y = b;
endmodule
