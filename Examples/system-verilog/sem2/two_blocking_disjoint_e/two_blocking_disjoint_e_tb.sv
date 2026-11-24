module two_blocking_disjoint_e_tb;
  logic clk = 0, d = 0, e = 1;
  logic a, b;
  two_blocking_disjoint_e dut(.clk, .d, .e, .a, .b);
  task row(input string tag);
    $display("ROW %s a=%b b=%b", tag, a, b);
  endtask
  initial begin
    #1 row("initial");
    #4 clk = 1; #1 row("edge0");
    #1 clk = 0; d = 1; e = 0;
    #4 clk = 1; #1 row("edge1");
    #1 $finish;
  end
endmodule
