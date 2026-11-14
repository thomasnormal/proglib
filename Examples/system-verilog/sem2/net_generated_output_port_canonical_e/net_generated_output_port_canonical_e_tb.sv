module net_generated_output_port_canonical_e_tb;
  logic clk; wire z_out;
  net_generated_output_port_canonical_e #(.N(1)) dut(.clk(clk), .z_out(z_out));
  initial begin clk=0; #1 $display("ROW i=0 z_out=%b", z_out); clk=1; #1 $display("ROW i=1 z_out=%b", z_out); $finish; end
endmodule
