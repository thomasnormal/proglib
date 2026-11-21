// SPDX-License-Identifier: Apache-2.0
// Clean-room receipt for continuous-assignment and always_comb startup ordering.
module time_zero_comb_quiesce_e (
  output logic a,
  output logic b,
  output logic y
);
  assign a = b;
  assign b = 1'b1;
  always_comb y = a;
endmodule
