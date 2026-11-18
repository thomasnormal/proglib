`timescale 1ns/1ps
module function_call_expression_repro_tb;
  logic in;
  logic y;
  function_call_expression_repro dut(.in(in), .y(y));

  initial begin
    in = 1'b0;
    #1 $display("ROW in=0 y=%b", y);
    in = 1'b1;
    #1 $display("ROW in=1 y=%b", y);
    $finish;
  end
endmodule
