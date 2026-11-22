`timescale 1ns/1ps

// The pinned core's Harvard interface has a registered instruction RAM
// (upstream rtl/darkram.v). Data writes use DBE in little-endian lane order.
module rv32ui_memory_tb;
  bit clk, reset = 1;
  reg [31:0] mem [0:4095];
  reg [31:0] idata = 32'h13;
  wire ireq, dreq, drd, dwr, drw, esimack;
  wire [31:0] iaddr, daddr, data_out;
  wire [3:0] dbe, debug;
  wire [2:0] dlen;
  reg iack = 1, dack = 1;
  wire [31:0] data_in = (dreq && drd) ? mem[daddr >> 2] : 0;
  int cycle = 0;
  bit started;
  string image;

  darkriscv dut (
    .CLK(clk), .RES(reset), .IRQ(1'b0), .IDREQ(ireq), .IADDR(iaddr),
    .IDATA(idata), .IDACK(iack), .IBERR(1'b0), .DDREQ(dreq), .DADDR(daddr),
    .DLEN(dlen), .DBE(dbe), .DRW(drw), .DRD(drd), .DWR(dwr), .DATAO(data_out),
    .DATAI(data_in), .DDACK(dack), .DBERR(1'b0), .DEBUG(debug),
    .ESIMREQ(1'b0), .ESIMACK(esimack)
  );

  initial begin
    if (!$value$plusargs("image=%s", image)) $fatal(1, "missing test image");
    $readmemh(image, mem);
  end
  always #5 clk = ~clk;
  always @(negedge clk) begin
    iack <= !(ireq && cycle % 3 == 0);
    dack <= !(dreq && cycle % 5 == 0);
  end
  always @(posedge clk) begin
    // Sample inputs and outputs before nonblocking updates. The Lean replay
    // compares after driving these inputs at clk=0, then issues the posedge.
    $display("ROW %0d %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b",
      cycle, reset, idata, iack, data_in, dack, ireq, iaddr, dreq, daddr, dlen,
      dbe, drw, drd, dwr, data_out, debug, esimack, dut.XRES, dut.HLT,
      dut.FLUSH, dut.PC, dut.XIDATA, dut.IERR, dut.REGS[3], dut.REGS[10], dut.REGS[17]);
    if (!reset && !dut.XRES && !dut.HLT && !dut.FLUSH) begin
      if (dut.PC == 0) begin
        if (started) begin
          $display("END restarted");
          $finish;
        end
        started <= 1;
      end
      if (dut.XIDATA == 32'h00000073) begin
        $display("END ecall");
        $finish;
      end
    end
    if (dreq && dwr && dack) begin
      if ((daddr >> 2) >= 4096) $fatal(1, "write outside test memory");
      for (int lane = 0; lane < 4; lane++)
        if (dbe[lane]) mem[daddr >> 2][lane*8 +: 8] <= data_out[lane*8 +: 8];
    end
    idata <= mem[iaddr >> 2];
    if (cycle == 3) reset <= 0;
    if (cycle == 9999) $fatal(1, "no ecall or return to the reset vector in 10000 cycles");
    cycle++;
  end
endmodule
