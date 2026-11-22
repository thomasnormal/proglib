`default_nettype none

// Simulator witness for the pinned SERV source set.  The source is supplied
// unchanged by the receipt script.
module serv_rvfi_tb;
  reg clk = 1'b0;
  reg i_rst = 1'b1;
  reg i_timer_irq = 1'b0;
  reg [31:0] i_ibus_rdt = 32'h00000013;
  wire i_ibus_ack;
  wire [31:0] i_dbus_rdt;
  wire i_dbus_ack;
  reg [31:0] i_ext_rd = 32'b0;
  reg i_ext_ready = 1'b0;

  wire [63:0] rvfi_order;
  wire rvfi_valid, rvfi_trap, rvfi_halt, rvfi_intr;
  wire [1:0] rvfi_mode, rvfi_ixl;
  wire [4:0] rvfi_rs1_addr, rvfi_rs2_addr, rvfi_rd_addr;
  wire [31:0] rvfi_insn, rvfi_rs1_rdata, rvfi_rs2_rdata, rvfi_rd_wdata;
  wire [31:0] rvfi_pc_rdata, rvfi_pc_wdata, rvfi_mem_addr;
  wire [31:0] rvfi_mem_rdata, rvfi_mem_wdata;
  wire [3:0] rvfi_mem_rmask, rvfi_mem_wmask;
  wire [31:0] o_ibus_adr, o_dbus_adr, o_dbus_dat;
  wire [3:0] o_dbus_sel;
  wire o_ibus_cyc, o_dbus_we, o_dbus_cyc;
  wire [31:0] o_ext_rs1, o_ext_rs2;
  wire [2:0] o_ext_funct3;
  wire o_mdu_valid;
  integer cycle = 0;

  bit wishbone;
  bit ibus_ack, dbus_ack;
  reg [31:0] data_word;
  initial wishbone = $test$plusargs("wishbone");
  assign i_ibus_ack = wishbone ? ibus_ack : 1'b1;
  assign i_dbus_ack = wishbone ? dbus_ack : 1'b1;

  always #5 clk = ~clk;
  always @(posedge clk) begin
    ibus_ack <= o_ibus_cyc && !ibus_ack;
    dbus_ack <= o_dbus_cyc && !dbus_ack;
    if (wishbone && o_dbus_cyc && dbus_ack) begin
      if (o_dbus_adr !== 32'h40 || o_dbus_sel !== 4'b1111)
        $fatal(1, "unexpected data address or byte select");
      if (o_dbus_we) data_word <= o_dbus_dat;
    end
  end
  assign i_dbus_rdt = wishbone ? data_word : 32'b0;

  always @* begin
    case (o_ibus_adr)
      32'h00000000: i_ibus_rdt = 32'h00500093; // addi x1,x0,5
      32'h00000004: i_ibus_rdt = 32'h00708113; // addi x2,x1,7
      32'h00000008: i_ibus_rdt = 32'h002081b3; // add x3,x1,x2
      32'h0000000c: i_ibus_rdt = wishbone ? 32'h04302023 : 32'h00000013; // sw x3,64(x0)
      32'h00000010: i_ibus_rdt = wishbone ? 32'h04002203 : 32'h00000013; // lw x4,64(x0)
      32'h00000014: i_ibus_rdt = wishbone ? 32'h00418463 : 32'h00000013; // beq x3,x4,+8
      32'h0000001c: i_ibus_rdt = wishbone ? 32'h0000006f : 32'h00000013; // jal x0,0
      default: i_ibus_rdt = 32'h00000013;
    endcase
  end

  always @(posedge clk) begin
    if (cycle == 3) i_rst <= 1'b0;
    if (wishbone) begin
      $display("BUS %0d %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b %b",
        cycle, rvfi_valid, rvfi_order, rvfi_insn, rvfi_pc_rdata, rvfi_pc_wdata,
        rvfi_rd_addr, rvfi_rd_wdata, o_ibus_cyc, i_ibus_ack, o_ibus_adr, i_ibus_rdt,
        o_dbus_cyc, i_dbus_ack, o_dbus_we, o_dbus_adr, o_dbus_sel, o_dbus_dat,
        i_dbus_rdt, rvfi_trap, rvfi_halt, rvfi_intr);
      if (rvfi_valid && rvfi_pc_rdata == 32'h1c) $finish;
      if (cycle == 799) $fatal(1, "SERV failed to retire the terminal jump");
    end else
      $display("ROW %0d %b %h %h %h %h %h %h %h %h", cycle, rvfi_valid,
      rvfi_order, rvfi_insn, rvfi_pc_rdata, rvfi_pc_wdata,
      rvfi_rd_addr, rvfi_rd_wdata, o_ibus_adr, o_dbus_cyc);
    cycle <= cycle + 1;
    if (!wishbone && cycle == 219) $finish;
  end

  serv_rf_top #(.DEBUG(1)) dut (
    .clk(clk), .i_rst(i_rst), .i_timer_irq(i_timer_irq),
    .rvfi_valid(rvfi_valid), .rvfi_order(rvfi_order), .rvfi_insn(rvfi_insn),
    .rvfi_trap(rvfi_trap), .rvfi_halt(rvfi_halt), .rvfi_intr(rvfi_intr),
    .rvfi_mode(rvfi_mode), .rvfi_ixl(rvfi_ixl), .rvfi_rs1_addr(rvfi_rs1_addr),
    .rvfi_rs2_addr(rvfi_rs2_addr), .rvfi_rs1_rdata(rvfi_rs1_rdata),
    .rvfi_rs2_rdata(rvfi_rs2_rdata), .rvfi_rd_addr(rvfi_rd_addr),
    .rvfi_rd_wdata(rvfi_rd_wdata), .rvfi_pc_rdata(rvfi_pc_rdata),
    .rvfi_pc_wdata(rvfi_pc_wdata), .rvfi_mem_addr(rvfi_mem_addr),
    .rvfi_mem_rmask(rvfi_mem_rmask), .rvfi_mem_wmask(rvfi_mem_wmask),
    .rvfi_mem_rdata(rvfi_mem_rdata), .rvfi_mem_wdata(rvfi_mem_wdata),
    .o_ibus_adr(o_ibus_adr), .o_ibus_cyc(o_ibus_cyc), .i_ibus_rdt(i_ibus_rdt),
    .i_ibus_ack(i_ibus_ack), .o_dbus_adr(o_dbus_adr), .o_dbus_dat(o_dbus_dat),
    .o_dbus_sel(o_dbus_sel), .o_dbus_we(o_dbus_we), .o_dbus_cyc(o_dbus_cyc),
    .i_dbus_rdt(i_dbus_rdt), .i_dbus_ack(i_dbus_ack), .o_ext_rs1(o_ext_rs1),
    .o_ext_rs2(o_ext_rs2), .o_ext_funct3(o_ext_funct3), .i_ext_rd(i_ext_rd),
    .i_ext_ready(i_ext_ready), .o_mdu_valid(o_mdu_valid));
endmodule
