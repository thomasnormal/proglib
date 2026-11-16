module inout_leaf(inout wire pad, input wire drive, output wire seen);
  assign pad = drive ? 1'b1 : 1'bz;
  assign seen = pad;
endmodule
module inout_repro(input wire drive, inout wire pad, output wire seen);
  inout_leaf child(.pad(pad), .drive(drive), .seen(seen));
endmodule
