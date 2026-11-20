`timescale 1ns/1ps
module daddr_cleanroom_tb;
  logic clk = 1'b0;
  logic [31:0] d = 32'bx;
  logic [31:0] q;
  wire [31:0] y;
  daddr_cleanroom dut(.*);
  always #5 clk = ~clk;
  task automatic row(input logic [31:0] value);
    d = value;
    @(posedge clk);
    #1 $display("ROW d=%b q=%b y=%b", d, q, y);
  endtask
  initial begin
    #1 $display("ROW d=%b q=%b y=%b", d, q, y);
    row(32'h00000005);
    row(32'h00000000);
    row(32'hxxxxxxxx);
    row(32'hzzzzzzzz);
    $finish;
  end
endmodule
