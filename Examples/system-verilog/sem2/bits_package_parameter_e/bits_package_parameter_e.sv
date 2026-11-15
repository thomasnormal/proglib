package bits_package_parameter_e_pkg;
  parameter logic [7:0] AttrDw = 8'h08;
endpackage
module bits_package_parameter_e(output logic [7:0] y);
  localparam int W = $bits(bits_package_parameter_e_pkg::AttrDw);
  assign y = W;
endmodule
