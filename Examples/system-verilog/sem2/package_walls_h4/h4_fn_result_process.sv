// The truncated value reaches a process expression; no parameter carries `resolved` metadata.
module leaf (output logic [31:0] o);
  assign o = rec::P[63:32];
endmodule
