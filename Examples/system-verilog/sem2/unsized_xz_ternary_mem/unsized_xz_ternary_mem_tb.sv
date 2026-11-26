module unsized_xz_ternary_mem_tb;
  logic clk;
  logic a;
  wire [7:0] y;
  wire [7:0] mem_q;

  unsized_xz_ternary_mem #(.N(8)) dut
    (.clk(clk), .a(a), .y(y), .mem_q(mem_q));

  initial begin
    a = 1'b0;
    #1 $display("ROW a0 y=%b mem=%b", y, mem_q);
    a = 1'b1;
    #1 $display("ROW a1 y=%b mem=%b", y, mem_q);
    a = 1'bx;
    #1 $display("ROW ax y=%b mem=%b", y, mem_q);
    a = 1'bz;
    #1 $display("ROW az y=%b mem=%b", y, mem_q);
    $finish;
  end
endmodule
