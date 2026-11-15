`timescale 1ns/1ps
module async_mem_fifo_canonical_e_tb;
  logic clk, rstn; logic [7:0] d; wire [7:0] q;
  async_mem_fifo_canonical_e #(.W(8), .N(4)) dut(.clk(clk), .rstn(rstn), .d(d), .q(q));
  initial begin
    clk=1'b1; rstn=1'b0; d=8'd3; #1 $display("ROW q=%b", q);
    clk=1'b0; rstn=1'b1; d=8'd17; #1 $display("ROW q=%b", q);
    clk=1'b1; rstn=1'b1; d=8'd17; #1 $display("ROW q=%b", q);
    clk=1'b0; rstn=1'b1; d=8'd34; #1 $display("ROW q=%b", q);
    clk=1'b1; rstn=1'b1; d=8'd34; #1 $display("ROW q=%b", q); $finish;
  end
endmodule
