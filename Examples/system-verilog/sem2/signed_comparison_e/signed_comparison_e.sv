module signed_comparison(input logic signed [7:0] x, output logic y);
  assign y = x >= 0;
endmodule
