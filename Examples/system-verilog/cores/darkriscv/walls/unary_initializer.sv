// Clean-room wall: an INT-class constant initializer is context-sized.
module unary_initializer(output logic [1:0] q);
  logic [1:0] value = -1;
  assign q = value;
endmodule
