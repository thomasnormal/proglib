module nested_generate_template_e_tb;
  wire [1:0] y;
  nested_generate_template_e dut(.y(y));
  initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
