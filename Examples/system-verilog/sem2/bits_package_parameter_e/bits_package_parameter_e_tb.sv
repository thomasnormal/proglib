module bits_package_parameter_e_tb;
  wire [7:0] y;
  bits_package_parameter_e dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
