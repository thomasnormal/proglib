module fifo_edge_order_e_tb;
  logic clk = 0;
  logic rst = 1;
  logic push = 0;
  logic pop = 0;
  logic [7:0] din = 0;
  logic [7:0] dout;
  logic [8:0] count;
  fifo_edge_order_e #(.DATA_W(8), .DEPTH(4)) dut(.*);
  always #5 clk = ~clk;
  task automatic row(input string tag);
    #1 $display("ROW %s rst=%b push=%b pop=%b din=%02x dout=%02x count=%0d", tag, rst, push, pop, din, dout, count);
  endtask
  initial begin
    @(posedge clk); #1 row("reset");
    @(negedge clk); rst = 0; push = 1; din = 8'ha5;
    @(posedge clk); #1 row("push0");
    @(negedge clk); din = 8'h3c;
    @(posedge clk); #1 row("push1");
    @(negedge clk); push = 0; pop = 1;
    @(posedge clk); #1 row("pop0");
    @(negedge clk); push = 1; din = 8'h5a;
    @(posedge clk); #1 row("both");
    @(negedge clk); push = 0; pop = 0;
    @(posedge clk); #1 row("settled");
    $finish;
  end
endmodule
