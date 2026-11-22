`timescale 1ns/1ps

// Whole-core input-driven witness for the pinned PicoRV32 source.  The
// memory inserts deterministic waits. The fixed image exercises ALU, branch, store,
// and load instructions before trapping on ebreak.  Every sampled core and
// memory-port output is printed so two approved simulators can be compared
// row-for-row.
module tb_picorv32_rvfi_long;
  reg clk = 0;
  always #5 clk = ~clk;
  reg resetn = 0;
  wire trap;
  wire mem_valid, mem_instr;
  reg mem_ready = 1;
  wire [31:0] mem_addr, mem_wdata;
  wire [3:0] mem_wstrb;
  reg [31:0] mem_rdata;
  wire pcpi_valid;
  wire [31:0] pcpi_insn;
  wire [31:0] pcpi_rs1;
  wire [31:0] pcpi_rs2;
  wire [31:0] eoi;
  wire trace_valid;
  wire [35:0] trace_data;
  localparam WORDS = 4096;
  reg [31:0] mem [0:WORDS-1];
  reg [31:0] mem_index;
  integer i;
  integer cycle;
  reg counters, external_image;
  string image_path;
  integer consecutive_traps;

  wire mem_la_read, mem_la_write;
  wire [31:0] mem_la_addr, mem_la_wdata;
  wire [3:0] mem_la_wstrb;
  wire rvfi_valid, rvfi_trap, rvfi_halt, rvfi_intr;
  wire [63:0] rvfi_order;
  wire [31:0] rvfi_insn, rvfi_rs1_rdata, rvfi_rs2_rdata, rvfi_rd_wdata;
  wire [31:0] rvfi_pc_rdata, rvfi_pc_wdata, rvfi_mem_addr;
  wire [31:0] rvfi_mem_rdata, rvfi_mem_wdata;
  wire [1:0] rvfi_mode, rvfi_ixl;
  wire [4:0] rvfi_rs1_addr, rvfi_rs2_addr, rvfi_rd_addr;
  wire [3:0] rvfi_mem_rmask, rvfi_mem_wmask;

  wire [63:0] rvfi_csr_mcycle_rmask, rvfi_csr_mcycle_wmask;
  wire [63:0] rvfi_csr_mcycle_rdata, rvfi_csr_mcycle_wdata;
  wire [63:0] rvfi_csr_minstret_rmask, rvfi_csr_minstret_wmask;
  wire [63:0] rvfi_csr_minstret_rdata, rvfi_csr_minstret_wdata;

  always @* begin
    mem_index = mem_addr >> 2;
    if (mem_index < WORDS) mem_rdata = mem[mem_index];
    else mem_rdata = 32'b0;
  end

  always @(posedge clk) begin
    if (external_image && resetn && mem_valid && mem_ready && mem_addr === 32'h1000_0000) begin
      if (mem_wstrb !== 4'b1111) $fatal(1, "invalid console write");
      $display("CONSOLE %02h", mem_wdata[7:0]);
    end else if (external_image && resetn && mem_valid && mem_ready && !(mem_addr[31:2] < WORDS)) begin
      $fatal(1, "memory address outside test RAM: %h", mem_addr);
    end else if (resetn && mem_valid && mem_ready && |mem_wstrb) begin
      if (mem_wstrb[0]) mem[mem_addr >> 2][7:0] <= mem_wdata[7:0];
      if (mem_wstrb[1]) mem[mem_addr >> 2][15:8] <= mem_wdata[15:8];
      if (mem_wstrb[2]) mem[mem_addr >> 2][23:16] <= mem_wdata[23:16];
      if (mem_wstrb[3]) mem[mem_addr >> 2][31:24] <= mem_wdata[31:24];
    end
  end

  picorv32 #(
    .ENABLE_COUNTERS(1), .ENABLE_COUNTERS64(1), .ENABLE_REGS_16_31(1),
    .ENABLE_REGS_DUALPORT(1), .LATCHED_MEM_RDATA(0), .TWO_STAGE_SHIFT(1),
    .BARREL_SHIFTER(0), .TWO_CYCLE_COMPARE(0), .TWO_CYCLE_ALU(0),
    .COMPRESSED_ISA(0), .CATCH_MISALIGN(1), .CATCH_ILLINSN(1),
    .ENABLE_PCPI(0), .ENABLE_MUL(0), .ENABLE_FAST_MUL(0), .ENABLE_DIV(0),
    .ENABLE_IRQ(0), .ENABLE_IRQ_QREGS(1), .ENABLE_IRQ_TIMER(1),
    .ENABLE_TRACE(0), .REGS_INIT_ZERO(0), .MASKED_IRQ(0),
    .LATCHED_IRQ(32'hffff_ffff), .PROGADDR_RESET(0),
    .PROGADDR_IRQ(16), .STACKADDR(32'hffff_ffff)
  ) dut (
    .clk(clk), .resetn(resetn), .trap(trap),
    .mem_valid(mem_valid), .mem_instr(mem_instr), .mem_ready(mem_ready),
    .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata),
    .mem_la_read(mem_la_read), .mem_la_write(mem_la_write),
    .mem_la_addr(mem_la_addr), .mem_la_wdata(mem_la_wdata),
    .mem_la_wstrb(mem_la_wstrb),
    .pcpi_valid(pcpi_valid), .pcpi_insn(pcpi_insn), .pcpi_rs1(pcpi_rs1), .pcpi_rs2(pcpi_rs2),
    .pcpi_wr(1'b0), .pcpi_rd(32'b0), .pcpi_wait(1'b0), .pcpi_ready(1'b0),
    .irq(32'b0), .eoi(eoi),
    .rvfi_valid(rvfi_valid), .rvfi_order(rvfi_order), .rvfi_insn(rvfi_insn),
    .rvfi_trap(rvfi_trap), .rvfi_halt(rvfi_halt), .rvfi_intr(rvfi_intr),
    .rvfi_mode(rvfi_mode), .rvfi_ixl(rvfi_ixl),
    .rvfi_rs1_addr(rvfi_rs1_addr), .rvfi_rs2_addr(rvfi_rs2_addr),
    .rvfi_rs1_rdata(rvfi_rs1_rdata), .rvfi_rs2_rdata(rvfi_rs2_rdata),
    .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
    .rvfi_pc_rdata(rvfi_pc_rdata), .rvfi_pc_wdata(rvfi_pc_wdata),
    .rvfi_mem_addr(rvfi_mem_addr), .rvfi_mem_rmask(rvfi_mem_rmask),
    .rvfi_mem_wmask(rvfi_mem_wmask), .rvfi_mem_rdata(rvfi_mem_rdata),
    .rvfi_mem_wdata(rvfi_mem_wdata),
    .rvfi_csr_mcycle_rmask(rvfi_csr_mcycle_rmask),
    .rvfi_csr_mcycle_wmask(rvfi_csr_mcycle_wmask),
    .rvfi_csr_mcycle_rdata(rvfi_csr_mcycle_rdata),
    .rvfi_csr_mcycle_wdata(rvfi_csr_mcycle_wdata),
    .rvfi_csr_minstret_rmask(rvfi_csr_minstret_rmask),
    .rvfi_csr_minstret_wmask(rvfi_csr_minstret_wmask),
    .rvfi_csr_minstret_rdata(rvfi_csr_minstret_rdata),
    .rvfi_csr_minstret_wdata(rvfi_csr_minstret_wdata),
    .trace_valid(trace_valid), .trace_data(trace_data)
  );

  // Save the memory input sampled at the edge. The live RAM bus can already
  // contain the next response when outputs are printed after the NBA region.
  reg [31:0] sampled_rdata;
  task sample_edge;
    begin
      @(posedge clk);
      sampled_rdata = mem_rdata;
      #1;
      $write("CYCLE %0d", cycle);
      $write(" resetn=%b trap=%b mem_valid=%b mem_instr=%b mem_ready=%b",
             resetn, trap, mem_valid, mem_instr, mem_ready);
      $write(" mem_addr=%b mem_wdata=%b mem_wstrb=%b mem_rdata=%b",
             mem_addr, mem_wdata, mem_wstrb, mem_rdata);
      $write(" mem_la_read=%b mem_la_write=%b mem_la_addr=%b",
             mem_la_read, mem_la_write, mem_la_addr);
      $write(" mem_la_wdata=%b mem_la_wstrb=%b",
             mem_la_wdata, mem_la_wstrb);
      $write(" pcpi_valid=%b pcpi_insn=%b pcpi_rs1=%b pcpi_rs2=%b",
             pcpi_valid, pcpi_insn, pcpi_rs1, pcpi_rs2);
      $write(" eoi=%b trace_valid=%b trace_data=%b",
             eoi, trace_valid, trace_data);
      $write(" rvfi_valid=%b rvfi_order=%b rvfi_insn=%b",
             rvfi_valid, rvfi_order, rvfi_insn);
      $write(" rvfi_trap=%b rvfi_halt=%b rvfi_intr=%b rvfi_mode=%b rvfi_ixl=%b",
             rvfi_trap, rvfi_halt, rvfi_intr, rvfi_mode, rvfi_ixl);
      $write(" rvfi_rs1_addr=%b rvfi_rs1_rdata=%b rvfi_rs2_addr=%b rvfi_rs2_rdata=%b",
             rvfi_rs1_addr, rvfi_rs1_rdata, rvfi_rs2_addr, rvfi_rs2_rdata);
      $write(" rvfi_rd_addr=%b rvfi_rd_wdata=%b rvfi_pc_rdata=%b rvfi_pc_wdata=%b",
             rvfi_rd_addr, rvfi_rd_wdata, rvfi_pc_rdata, rvfi_pc_wdata);
      $write(" rvfi_mem_addr=%b rvfi_mem_rmask=%b rvfi_mem_wmask=%b",
             rvfi_mem_addr, rvfi_mem_rmask, rvfi_mem_wmask);
      $write(" rvfi_mem_rdata=%b rvfi_mem_wdata=%b",
             rvfi_mem_rdata, rvfi_mem_wdata);
      $write(" sampled_rdata=%032b pcpi_wr=%b pcpi_rd=%032b pcpi_wait=%b pcpi_ready=%b irq=%032b",
             sampled_rdata, dut.pcpi_wr, dut.pcpi_rd, dut.pcpi_wait, dut.pcpi_ready, dut.irq);
      $write(" rvfi_csr_mcycle_rmask=%064b rvfi_csr_mcycle_wmask=%064b rvfi_csr_mcycle_rdata=%064b rvfi_csr_mcycle_wdata=%064b",
             rvfi_csr_mcycle_rmask, rvfi_csr_mcycle_wmask, rvfi_csr_mcycle_rdata, rvfi_csr_mcycle_wdata);
      $display(" rvfi_csr_minstret_rmask=%064b rvfi_csr_minstret_wmask=%064b rvfi_csr_minstret_rdata=%064b rvfi_csr_minstret_wdata=%064b",
               rvfi_csr_minstret_rmask, rvfi_csr_minstret_wmask, rvfi_csr_minstret_rdata, rvfi_csr_minstret_wdata);
      cycle = cycle + 1;
    end
  endtask

  initial begin
    for (i = 0; i < WORDS; i = i + 1) mem[i] = 32'b0;
    counters = $test$plusargs("counters");
    external_image = $value$plusargs("image=%s", image_path);
    if (external_image) begin
      $readmemh(image_path, mem);
    end else begin
      mem[0] = 32'h00500093; // addi x1, x0, 5
      mem[1] = 32'h00700113; // addi x2, x0, 7
      mem[2] = 32'h002081b3; // add  x3, x1, x2
      mem[3] = 32'h10302023; // sw   x3, 0x100(x0)
      mem[4] = 32'h10002203; // lw   x4, 0x100(x0)
      mem[5] = 32'h00418463; // beq  x3, x4, +8
      mem[6] = 32'h06300293; // addi x5, x0, 99 (branch skips this)
      mem[7] = 32'h02a00313; // addi x6, x0, 42
      mem[8] = 32'h000f83b3; // add x7, x31, x0 (uninitialized register)
      mem[9] = 32'h00100073; // ebreak
      if (counters) begin
        mem[0] = 32'hc0002473; // rdcycle x8
        mem[1] = 32'hc80024f3; // rdcycleh x9
        mem[2] = 32'hc0202573; // rdinstret x10
        mem[3] = 32'hc82025f3; // rdinstreth x11
        mem[4] = 32'h00100073; // ebreak
      end
    end
    $display("BEGIN");
    cycle = -4;
    repeat (4) sample_edge;
    resetn = 1;
    consecutive_traps = 0;
    while (cycle < (external_image ? 20000 : 300) &&
           !((external_image || counters) &&
             ((rvfi_valid === 1'b1 && rvfi_trap === 1'b1) || consecutive_traps == 2))) begin
      mem_ready = (cycle % 4 != 1);
      sample_edge;
      consecutive_traps = trap === 1'b1 ? consecutive_traps + 1 : 0;
    end
    if (external_image && !trap) $fatal(1, "no terminal trap within the cycle bound");
    $display("END trap=%b", trap);
    $finish;
  end
endmodule
