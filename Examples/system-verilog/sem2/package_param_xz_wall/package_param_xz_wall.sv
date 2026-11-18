package package_param_xz_wall_pkg;
  parameter logic [31:0] INSTR_LUI = {25'bz, 7'b0110111};
endpackage

module package_param_xz_wall(output logic [31:0] y);
  import package_param_xz_wall_pkg::*;
  assign y = INSTR_LUI;
endmodule
