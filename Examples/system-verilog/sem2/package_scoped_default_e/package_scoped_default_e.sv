package package_scoped_default_e_pkg;
  parameter int unsigned P = 16;
endpackage
module package_scoped_default_e #(parameter int unsigned N = package_scoped_default_e_pkg::P) (
  input logic [N-1:0] i, output logic [N-1:0] o);
  assign o = i;
endmodule
