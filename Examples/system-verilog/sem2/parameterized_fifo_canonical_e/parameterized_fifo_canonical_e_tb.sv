`timescale 1ns/1ps
module parameterized_fifo_canonical_e_tb;
  logic clk = 1'b0;
  logic rst_n = 1'b1;
  logic push = 1'b0;
  logic pop = 1'b0;
  logic [31:0] push_data = 32'h000000a5;
  wire [31:0] head;
  wire empty, full, push_accepted, pop_accepted;
  wire [2:0] level;

  parameterized_fifo_canonical_e #(.DATA_W(32), .DEPTH(4)) dut (.*);

  task row(input [127:0] name);
    $display("ROW %0s head=%b empty=%b full=%b level=%b push_accepted=%b pop_accepted=%b", name,
      head, empty, full, level, push_accepted, pop_accepted);
  endtask

  initial begin
    #1 rst_n = 1'b0;
    #1 row("reset");
    #1 rst_n = 1'b1; push = 1'b1;
    #1 clk = 1'b1;
    #1 row("push0");
    #1 clk = 1'b0;
    #1 push_data = 32'h0000005a;
    #1 clk = 1'b1;
    #1 row("push1");
    #1 clk = 1'b0; push = 1'b0; pop = 1'b1;
    #1 clk = 1'b1;
    #1 row("pop0");
    #1 clk = 1'b0; push = 1'b1; pop = 1'b1; push_data = 32'h0000003c;
    #1 clk = 1'b1;
    #1 row("both");
    #1 clk = 1'b0; push = 1'b0; pop = 1'b0;
    #1 row("settled");
    $finish;
  end
endmodule
