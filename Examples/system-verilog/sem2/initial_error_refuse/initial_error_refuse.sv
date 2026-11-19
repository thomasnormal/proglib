module initial_error_refuse(input logic x, output logic y);
  initial $error("check");
  assign y = x;
endmodule
