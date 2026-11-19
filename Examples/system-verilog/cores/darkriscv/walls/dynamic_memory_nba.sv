`timescale 1ns/1ps

// Clean-room receipt for the DarkRISCV first-clock target wall.
module darkriscv_dynamic_memory_nba (
  input logic CLK,
  input logic RES,
  input logic [1:0] DPTR,
  input logic [31:0] DATA,
  output logic [31:0] R0,
  output logic [31:0] R1,
  output logic [31:0] R2,
  output logic [31:0] R3
);
  logic [31:0] REGS [0:3];

  assign R0 = REGS[0];
  assign R1 = REGS[1];
  assign R2 = REGS[2];
  assign R3 = REGS[3];

  always @(posedge CLK) begin
    if (!RES)
      REGS[DPTR] <= DATA;
  end
endmodule
