module clog2_negative_e(output logic [5:0] y);
  localparam int W = $clog2(-1);
  assign y = W;
endmodule
