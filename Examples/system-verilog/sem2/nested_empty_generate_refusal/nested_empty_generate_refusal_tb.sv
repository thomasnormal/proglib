module nested_empty_generate_refusal_tb;
  wire [1:0] y;
  nested_empty_generate_refusal dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
