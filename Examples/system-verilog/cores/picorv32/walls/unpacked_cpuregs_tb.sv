module unpacked_cpuregs_tb;
  logic clk;
  logic [4:0] raddr, waddr;
  logic [31:0] wdata;
  logic we;
  wire [31:0] rdata;

  unpacked_cpuregs #(.N(32)) dut
    (.clk(clk), .raddr(raddr), .waddr(waddr), .wdata(wdata),
     .we(we), .rdata(rdata));

  initial begin
    clk = 0; raddr = 0; waddr = 0; wdata = 0; we = 0;
    #1 $display("ROW init r=%b", rdata);
    waddr = 5'd1; wdata = 32'h000000a5; we = 1;
    #1 clk = 1; #1 $display("ROW w1 r=%b", rdata);
    clk = 0; we = 0; raddr = 1; #1 $display("ROW r1 r=%b", rdata);
    waddr = 5'd2; wdata = 32'h0000003c; we = 1;
    #1 clk = 1; #1 $display("ROW w2 r=%b", rdata);
    clk = 0; we = 0; raddr = 2; #1 $display("ROW r2 r=%b", rdata);
    raddr = 5'bxxxxx; #1 $display("ROW rx r=%b", rdata);
    $finish;
  end
endmodule
