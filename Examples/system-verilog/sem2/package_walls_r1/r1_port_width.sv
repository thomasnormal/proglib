module leaf (
  input  logic [cfg::W-1:0] i,
  output logic [cfg::W-1:0] o);
  assign o = i;
endmodule
