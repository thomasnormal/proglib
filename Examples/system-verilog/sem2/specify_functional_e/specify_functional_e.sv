// A module containing an IEEE timing specify path.
module specify_repro(input wire source, output wire result);
  assign result = source;
  specify
    (source *> result) = (0, 0);
  endspecify
endmodule

module specify_repro_check(input logic a, output logic y);
  specify_repro u_child(.source(a), .result(y));
endmodule
