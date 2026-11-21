`timescale 1ns/1ps
module daddr_memory5_cleanroom_tb;
  logic clk = 1'b0;
  logic [4:0] idx = 5'b0;
  logic [31:0] d = 32'bx;
  wire [31:0] y;
  daddr_memory5_cleanroom dut(.*);
  always #5 clk = ~clk;
  task automatic row(input logic [4:0] index, input logic [31:0] value);
    idx = index;
    d = value;
    @(posedge clk);
    #1 $display("ROW idx=%b d=%b y=%b", idx, d, y);
  endtask
  initial begin
    #1 $display("ROW idx=%b d=%b y=%b", idx, d, y);
    row(5'b00001, 32'h00000005);
    row(5'b00001, 32'h00000000);
    row(5'b00010, 32'hxxxxxxxx);
    row(5'b00010, 32'hzzzzzzzz);
    $finish;
  end
endmodule
