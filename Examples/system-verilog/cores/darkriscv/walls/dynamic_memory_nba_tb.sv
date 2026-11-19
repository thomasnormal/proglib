`timescale 1ns/1ps
module darkriscv_dynamic_memory_nba_tb;
  logic CLK = 0;
  logic RES = 1;
  logic [1:0] DPTR = 0;
  logic [31:0] DATA = 0;
  wire [31:0] R0, R1, R2, R3;

  darkriscv_dynamic_memory_nba dut (
    .CLK(CLK), .RES(RES), .DPTR(DPTR), .DATA(DATA),
    .R0(R0), .R1(R1), .R2(R2), .R3(R3));

  always #5 CLK = ~CLK;

  initial begin
    #2;
    $display("ROW reset=%b dptr=%0d data=%08x regs=%08x_%08x_%08x_%08x",
      RES, DPTR, DATA, R3, R2, R1, R0);
    #6;
    RES = 0;
    DPTR = 2;
    DATA = 32'h000000a5;
    #2;
    $display("ROW reset=%b dptr=%0d data=%08x regs=%08x_%08x_%08x_%08x",
      RES, DPTR, DATA, R3, R2, R1, R0);
    #5;
    $display("ROW reset=%b dptr=%0d data=%08x regs=%08x_%08x_%08x_%08x",
      RES, DPTR, DATA, R3, R2, R1, R0);
    DPTR = 1;
    DATA = 32'h0000005a;
    #10;
    $display("ROW reset=%b dptr=%0d data=%08x regs=%08x_%08x_%08x_%08x",
      RES, DPTR, DATA, R3, R2, R1, R0);
    $finish;
  end
endmodule
