package assignment_pattern_storage_pkg;
  parameter logic [4:0] PmpCfgRst [0:1] = '{default: '0};
endpackage
module assignment_pattern_storage_refuse(input logic x, output logic y);
  import assignment_pattern_storage_pkg::*;
  assign y = PmpCfgRst[0][0] ^ x;
endmodule
