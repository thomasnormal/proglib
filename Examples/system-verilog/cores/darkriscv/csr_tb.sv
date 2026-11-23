`timescale 1ns/1ps

module darkriscv_csr_tb;
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
  wire data_ack = 1'b1;
  wire data_err = 1'b0;
  wire [3:0] debug;
  reg [31:0] image [0:63];
  integer i;

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

  always @(posedge clk) begin
    if (!reset && data_req && data_wr)
      $display("CSR_STORE addr=%08x value=%08x", data_addr, data_out);
  end

  initial begin
    for (i = 0; i < 64; i = i + 1)
      image[i] = 32'h00000013;
    image[0] = 32'h00000013;
    image[1] = 32'h00000013;
    image[2] = 32'h00000013;
    image[3] = 32'h00000013;
    image[4] = 32'hc00020f3; // rdcycle x1
    image[5] = 32'hc0202173; // rdinstret x2
    image[6] = 32'h00102023; // sw x1, 0(x0)
    image[7] = 32'h00202223; // sw x2, 4(x0)
    repeat (4) @(posedge clk);
    reset <= 0;
    repeat (80) @(posedge clk);
    $finish;
  end
endmodule
