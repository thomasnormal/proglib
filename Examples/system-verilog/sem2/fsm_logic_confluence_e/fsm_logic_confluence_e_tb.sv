`timescale 1ns/1ps
module fsm_logic_confluence_e_tb;
  logic clk = 0, rst, go;
  logic busy, done;
  fsm_logic_confluence_e dut(.*);
  task automatic row(input [8*16-1:0] name, input logic r, input logic g);
    begin
      rst = r; go = g; #5 clk = 1; #1 $display("ROW %0s busy=%b done=%b", name, busy, done); clk = 0; #1;
    end
  endtask
  initial begin
    rst = 1'bx; go = 1'bx; #1 $display("ROW first busy=%b done=%b", busy, done);
    row("reset", 1'b1, 1'b0);
    row("start", 1'b0, 1'b1);
    row("run", 1'b0, 1'b0);
    row("done", 1'b0, 1'b0);
    row("idle", 1'b0, 1'b0);
    $finish;
  end
endmodule
