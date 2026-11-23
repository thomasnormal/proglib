package bits_type_alias_e_pkg;
  typedef logic [11:0] csr_t;
endpackage
module bits_type_alias_e(output logic [11:0] y);
  localparam int W = $bits(bits_type_alias_e_pkg::csr_t);
  assign y = W;
endmodule
