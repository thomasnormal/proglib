`timescale 1ns/1ps

// One boot-ROM word has a programmed low byte. The upper 24 bits retain
// their power-on unknown values. Read that word into x2 and store x2 at 4.
module darkriscv_x_register_tb;
  reg clk = 0, reset = 1;
  reg [31:0] boot_word;
  reg [31:0] idata, sampled_idata;
  wire ireq, dreq, drw, drd, dwr, esimack;
  wire [31:0] iaddr, daddr, data_out;
  wire [2:0] dlen;
  wire [3:0] dbe, debug;

  wire [31:0] data_in = reset ? 32'b0 : boot_word;

  darkriscv dut (
    .CLK(clk), .RES(reset), .IRQ(1'b0), .ESIMREQ(1'b0), .ESIMACK(esimack),
    .IDREQ(ireq), .IADDR(iaddr), .IDATA(idata),
    .IDACK(1'b1), .IBERR(1'b0), .DDREQ(dreq), .DADDR(daddr),
    .DLEN(dlen), .DBE(dbe), .DRW(drw), .DRD(drd), .DWR(dwr),
    .DATAO(data_out), .DATAI(data_in), .DDACK(1'b1), .DBERR(1'b0),
    .DEBUG(debug)
  );

  always #5 clk = ~clk;
  always @* begin
    case (iaddr)
      16: idata = 32'h00002103; // lw x2, 0(x0)
      32: idata = 32'h00202223; // sw x2, 4(x0)
      default: idata = 32'h00000013;
    endcase
  end
  always @(negedge clk) sampled_idata <= idata;

  initial begin
    boot_word[7:0] = 8'ha5;
    repeat (4) @(posedge clk);
    reset <= 0;
    for (int cycle = 0; cycle < 32; cycle++) begin
      @(posedge clk);
      #1;
      $display("ROW cycle=%0d reset=%b instr_req=%b instr_addr=%b instr_data=%b data_req=%b data_addr=%b data_len=%b data_be=%b data_rw=%b data_rd=%b data_wr=%b data_out=%b data_in=%b data_ack=1 debug=%b esimack=%b x2=%b",
        cycle, reset, ireq, iaddr, sampled_idata, dreq, daddr, dlen, dbe,
        drw, drd, dwr, data_out, data_in, debug, esimack, dut.REGS[2]);
    end
    $finish;
  end
endmodule
