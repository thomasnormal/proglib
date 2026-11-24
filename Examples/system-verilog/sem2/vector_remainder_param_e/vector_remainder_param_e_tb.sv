module vector_remainder_param_e_tb;
  wire [7:0] y;
  vector_remainder_param_e #(.N(13)) dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
