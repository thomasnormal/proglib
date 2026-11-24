module signed_self_determined(input logic signed [3:0] a, input logic signed [3:0] b, input logic en, output logic y);
  assign y = en && (a < b);
endmodule
