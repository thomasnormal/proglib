package package_scoped_type_e_pkg;
  typedef logic [7:0] word_t;
  parameter int W = 8;
endpackage
module package_scoped_type_e (
  input package_scoped_type_e_pkg::word_t i_word,
  output logic [package_scoped_type_e_pkg::W-1:0] o_word);
  assign o_word = i_word;
endmodule
