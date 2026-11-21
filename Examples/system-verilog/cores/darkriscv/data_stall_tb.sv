`timescale 1ns/1ps

// Input-driven DarkRISCV witness with data-memory wait states.  The pinned
// RTL is unchanged.  The image performs a store and a load while DDACK is
// lowered on every third active falling edge.
module darkriscv_data_stall_tb;
  reg clk = 0;
  reg reset = 1;
  wire instr_req;
  wire [31:0] instr_addr;
  reg [31:0] instr_data;
  wire instr_ack = 1'b1;
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
  reg [31:0] image [0:63];
  integer i;
  integer stall_tick = 0;
  reg [31:0] sampled_instr_data;
  reg sampled_data_ack;
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
    if ((instr_addr >> 2) < 64)
      instr_data = image[instr_addr >> 2];
    else
      instr_data = 32'h00000013;
    data_in = 32'b0;
  end

  always @(negedge clk) begin
    sampled_instr_data <= instr_data;
    sampled_data_ack <= data_ack;
    stall_tick = stall_tick + 1;
    if (data_req) begin
      next_ack = (stall_tick % 3 == 0) ? 1'b0 : 1'b1;
      data_ack <= next_ack;
      sampled_data_ack <= next_ack;
    end else begin
      next_ack = 1'b1;
      data_ack <= next_ack;
      sampled_data_ack <= next_ack;
    end
  end

  initial begin
    for (i = 0; i < 64; i = i + 1)
      image[i] = 32'h00000013;
    image[0] = 32'h00500093; // addi x1, x0, 5
    image[1] = 32'h00102023; // sw   x1, 0(x0)
    image[2] = 32'h00002103; // lw   x2, 0(x0)
    image[3] = 32'h00110193; // addi x3, x2, 1
    repeat (4) @(posedge clk);
    reset <= 0;
    repeat (1000) begin
      @(posedge clk);
      #1;
      $display("ROW cycle=%0d reset=%b instr_req=%b instr_addr=%08x instr_data=%08x data_req=%b data_addr=%08x data_len=%03b data_be=%04b data_rw=%b data_rd=%b data_wr=%b data_out=%08x data_in=%08x data_ack=%b debug=%04b",
        $time / 10 - 4, reset, instr_req, instr_addr, sampled_instr_data,
        data_req, data_addr, data_len, data_be, data_rw, data_rd, data_wr,
        data_out, data_in, sampled_data_ack, debug);
    end
    $finish;
  end
endmodule
