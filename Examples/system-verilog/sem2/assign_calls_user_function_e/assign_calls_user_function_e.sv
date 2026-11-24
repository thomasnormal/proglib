// SPDX-License-Identifier: Apache-2.0
// Source-shaped continuous assignments calling an automatic function.
module assign_calls_user_function_e (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [1:0] invert2(input logic [1:0] x);
    return ~x;
  endfunction
  assign y[0 +: 2] = invert2(a[0 +: 2]);
  assign y[2 +: 2] = invert2(a[2 +: 2]);
endmodule
