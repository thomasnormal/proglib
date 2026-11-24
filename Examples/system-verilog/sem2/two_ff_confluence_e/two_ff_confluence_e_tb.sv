`timescale 1ns/1ps
module two_ff_confluence_e_tb;
  logic clk = 1'b0;
  logic a_in = 1'b0;
  logic b_in = 1'b1;
  wire a_q;
  wire b_q;

  two_ff_confluence_e dut (.*);

  task row(input [63:0] name);
    $display("ROW %0s a_q=%b b_q=%b", name, a_q, b_q);
  endtask

  initial begin
    #1 row("low0");
    #1 clk = 1'b1; #1 row("edge0");
    #1 clk = 1'b0; a_in = 1'b1; b_in = 1'b0; #1 row("low1");
    #1 clk = 1'b1; #1 row("edge1");
    $finish;
  end
endmodule
