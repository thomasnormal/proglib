// The module never names a package.
module leaf #(parameter int unsigned W = 4) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o);
  assign o = i;
endmodule
