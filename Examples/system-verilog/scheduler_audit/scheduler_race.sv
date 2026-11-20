// SPDX-License-Identifier: Apache-2.0
// Clean-room S1 C1/C2 audit bench.  Two source-shaped edge processes enqueue
// conflicting NBAs in one active region.  IEEE 1800-2023 §§4.6 and 10.4.2
// permit either active-event order, so q may settle to 8'h00 or 8'h01.
module scheduler_race(input logic clk, output logic [7:0] q);
  always @(posedge clk) q <= 8'h00;
  always @(posedge clk) q <= 8'h01;
endmodule

module scheduler_race_tb;
  logic clk = 1'b0;
  logic [7:0] q;
  scheduler_race dut(.clk(clk), .q(q));
  initial begin
    #1 clk = 1'b1;
    #1 $display("S1-C1 q=%02h", q);
    #1 $finish;
  end
endmodule
