module tb;
  wire y;
  m dut(y);
  initial begin #1 $display("ROW %b", y); $finish; end
endmodule
