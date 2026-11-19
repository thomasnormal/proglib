`timescale 1ns/1ps
module nested_unpacked_target_tb;
  logic clk = 0;
  logic rst_n = 1;
  logic [7:0] d = 8'h00;
  wire [7:0] q;
  nested_unpacked_target #(.W(8), .R(2), .C(2)) dut
    (.clk(clk), .rst_n(rst_n), .d(d), .q(q));
  always #1 clk = ~clk;
  initial begin
    #0.5; $display("ROW i=0 q=%b", q);
    #1; $display("ROW i=1 q=%b", q);
    d = 8'h00; #1.5; $display("ROW i=2 q=%b", q);
    d = 8'ha5; #2; $display("ROW i=3 q=%b", q);
    d = 8'bxxxxxxxx; #2; $display("ROW i=4 q=%b", q);
    d = 8'bzzzzzzzz; #2; $display("ROW i=5 q=%b", q);
    $finish;
  end
endmodule
