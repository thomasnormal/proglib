package package_param_xz_ops_pkg;
  parameter logic [3:0] MASK = 4'b1z0z;
endpackage

module package_param_xz_ops(
  input logic [3:0] a,
  output logic casez_hit,
  output logic inside_hit,
  output logic caseeq_hit
);
  import package_param_xz_ops_pkg::*;
  always_comb begin
    casez (a)
      MASK: casez_hit = 1'b1;
      default: casez_hit = 1'b0;
    endcase
    inside_hit = 1'b0;
`ifndef NO_INSIDE
    case (a) inside
      MASK: inside_hit = 1'b1;
      default: inside_hit = 1'b0;
    endcase
`endif
    caseeq_hit = (a === MASK);
  end
endmodule
