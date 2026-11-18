`timescale 1ns/1ns
module initial_memory_tb;
  logic clk = 1'b0;
  logic [7:0] q;
  logic [31:0] q32;
  initial_memory #(.W(8)) dut (.clk(clk), .q(q));
  initial_memory #(.W(32), .DEPTH(32)) dut32 (.clk(clk), .q(q32));
  initial begin
    #1 $display("ROW q=%h q32=%h", q, q32);
    #1 $finish;
  end
endmodule
