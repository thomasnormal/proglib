package constant_struct_pattern_package_e_pkg;
  typedef struct packed { logic p; logic n; } pair_t;
  parameter pair_t DEFAULT_PAIR = '{p: 1'b0, n: 1'b1};
endpackage
module constant_struct_pattern_package_e #(parameter integer N = 1) (
    output logic [1:0] y);
  import constant_struct_pattern_package_e_pkg::*;
  localparam pair_t P = DEFAULT_PAIR;
  assign y = P;
endmodule
