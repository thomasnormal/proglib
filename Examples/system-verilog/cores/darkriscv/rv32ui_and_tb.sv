`timescale 1ns/1ps

// A riscv-tests rv32ui/and image with instruction acknowledgement stalls.
// The DarkRISCV RTL is unchanged.  The checked-in image is loaded by the
// checker into the same reset-at-zero memory used by the source test.
module darkriscv_rv32ui_and_tb;
  reg clk = 0;
  reg reset = 1;
  wire instr_req;
  wire [31:0] instr_addr;
  reg [31:0] instr_data;
  reg instr_ack = 1;
  wire instr_err = 1'b0;
  wire data_req;
  wire [31:0] data_addr;
  wire [2:0] data_len;
  wire [3:0] data_be;
  wire data_rw;
  wire data_rd;
  wire data_wr;
  wire [31:0] data_out;
  reg [31:0] data_in = 0;
  reg data_ack = 1;
  wire data_err = 1'b0;
  wire [3:0] debug;
  reg [31:0] image [0:2047];
  reg [31:0] sampled_instr_data;
  reg sampled_instr_ack;
  integer i;
  integer stall_tick = 0;
  reg next_ack;

  darkriscv dut (
    .CLK(clk), .RES(reset),
    .IDREQ(instr_req), .IADDR(instr_addr), .IDATA(instr_data),
    .IDACK(instr_ack), .IBERR(instr_err),
    .DDREQ(data_req), .DADDR(data_addr), .DLEN(data_len),
    .DBE(data_be), .DRW(data_rw), .DRD(data_rd), .DWR(data_wr),
    .DATAO(data_out), .DATAI(data_in), .DDACK(data_ack), .DBERR(data_err),
    .DEBUG(debug)
  );

  always #5 clk = ~clk;

  always @* begin
    if ((instr_addr >> 2) < 2048)
      instr_data = image[instr_addr >> 2];
    else
      instr_data = 32'h00000013;
    data_in = 32'b0;
  end

  always @(negedge clk) begin
    sampled_instr_data <= instr_data;
    sampled_instr_ack <= instr_ack;
    stall_tick = stall_tick + 1;
    if (instr_req) begin
      next_ack = (stall_tick % 3 == 0) ? 1'b0 : 1'b1;
      instr_ack <= next_ack;
      sampled_instr_ack <= next_ack;
    end else begin
      instr_ack <= 1'b1;
      sampled_instr_ack <= 1'b1;
    end
    if (data_req) begin
      next_ack = (stall_tick % 5 == 0) ? 1'b0 : 1'b1;
      data_ack <= next_ack;
    end else begin
      data_ack <= 1'b1;
    end
  end

  initial begin
    for (i = 0; i < 2048; i = i + 1)
      image[i] = 32'h00000013;
    $readmemh("rv32ui_and.hex", image, 0, 415);
    repeat (4) @(posedge clk);
    reset <= 0;
    repeat (300) begin
      @(posedge clk);
      #1;
      $display("ROW cycle=%0d reset=%b instr_req=%b instr_addr=%08x instr_data=%08x data_req=%b data_addr=%08x data_len=%03b data_be=%04b data_rw=%b data_rd=%b data_wr=%b data_out=%08x data_in=%08x data_ack=%b debug=%04b instr_ack=%b",
        $time / 10 - 4, reset, instr_req, instr_addr, sampled_instr_data,
        data_req, data_addr, data_len, data_be, data_rw, data_rd, data_wr,
        data_out, data_in, data_ack, debug, sampled_instr_ack);
    end
    $finish;
  end
endmodule
