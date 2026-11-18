`timescale 1ns/1ns
module memory_unary_initializer_tb;
  wire [1:0] q;
  memory_unary_initializer dut(.q(q));
  initial begin
    #1;
    $display("q=%b", q);
    if (q !== 2'b11) $fatal(1, "expected q=11, got %b", q);
    $finish;
  end
endmodule
