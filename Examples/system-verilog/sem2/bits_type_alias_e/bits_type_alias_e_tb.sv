module bits_type_alias_e_tb;
  wire [11:0] y;
  bits_type_alias_e dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
