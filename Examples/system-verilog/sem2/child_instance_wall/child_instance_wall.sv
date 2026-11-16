// Clean-room reproduction of the public PicoRV32 optional-PCPI child shape.
// The active generate branch names a module whose definition is absent from
// this source envelope; Slang retains that parser-native child refusal.
module child_instance_wall(
  input logic clk, resetn, pcpi_valid,
  input logic [31:0] pcpi_insn, pcpi_rs1, pcpi_rs2,
  output logic pcpi_wr, pcpi_wait, pcpi_ready,
  output logic [31:0] pcpi_rd
);
  generate
    if (1) begin : g
      picorv32_pcpi_fast_mul pcpi_mul (
        .clk(clk), .resetn(resetn), .pcpi_valid(pcpi_valid),
        .pcpi_insn(pcpi_insn), .pcpi_rs1(pcpi_rs1), .pcpi_rs2(pcpi_rs2),
        .pcpi_wr(pcpi_wr), .pcpi_rd(pcpi_rd), .pcpi_wait(pcpi_wait),
        .pcpi_ready(pcpi_ready)
      );
    end
  endgenerate
endmodule
