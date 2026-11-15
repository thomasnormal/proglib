module clog2_negative_e_tb;
  wire [5:0] y;
  clog2_negative_e dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
