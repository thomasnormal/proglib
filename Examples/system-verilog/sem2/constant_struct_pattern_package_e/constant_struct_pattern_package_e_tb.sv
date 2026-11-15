module constant_struct_pattern_package_e_tb;
  wire [1:0] y;
  constant_struct_pattern_package_e #(.N(1)) dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
