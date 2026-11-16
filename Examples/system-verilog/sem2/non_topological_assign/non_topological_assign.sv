// Continuous assignments deliberately read a later target (IEEE 1800-2023 §10.3).
module non_topological_assign(input logic x, output logic y);
  logic a, b;
  assign a = b;
  assign b = x;
  assign y = a;
endmodule
