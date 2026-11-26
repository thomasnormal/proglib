// The package constant is a 64-bit expression (no function); its upper half is read by a process.
module leaf (output logic [31:0] o);
  assign o = rec::Q[63:32];
endmodule
