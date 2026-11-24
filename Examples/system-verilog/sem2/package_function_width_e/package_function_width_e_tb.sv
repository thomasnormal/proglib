module package_function_width_e_tb;
  wire y;
  package_function_width_e #(.N(1)) dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
