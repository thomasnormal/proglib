module pcr_tb;
  wire a0, b0, c0, a1, b1, c1;
  wire [3:0] p0, p1;
  wire [7:0] l0, l1, og;
  wire [39:0] s0, d0, s1, d1;
  wire [31:0] g0, g1;
  pcr_leaf dut0 (.o_msb(a0), .o_formal(b0), .o_top(c0), .o_part(p0), .o_low4(l0), .o_sh(s0), .o_div(d0), .o_g(g0));
  pcr_leaf #(.N(8'h80), .Q(2)) dut1 (.o_msb(a1), .o_formal(b1), .o_top(c1), .o_part(p1), .o_low4(l1),
                                     .o_sh(s1), .o_div(d1), .o_g(g1));
  pcr_gen gen (.o(og));
  initial begin
    #1;
    $display("CONST pcr::PX %b", pcr::PX);
    $display("CONST pcr::RES %b", pcr::RES);
    $display("CONST pcr::CX %b", pcr::CX);
    $display("CONST pcr::CA %b", pcr::CA);
    $display("CONST pcr::CD %b", pcr::CD);
    $display("CONST pcr::M %b", pcr::M);
    $display("CONST pcr::MU %b", pcr::MU);
    $display("CONST pcr::TS %b", pcr::TS);
    $display("POINT default L1 %b L2 %b L3 %b L4 %b L5 %b U1 %b U2 %b G %0d", dut0.L1, dut0.L2, dut0.L3, dut0.L4,
      dut0.L5, dut0.U1, dut0.U2, dut0.blk[0].G);
    $display("POINT N=80,Q=2 L1 %b L2 %b L3 %b L4 %b L5 %b U1 %b U2 %b G %0d", dut1.L1, dut1.L2, dut1.L3, dut1.L4,
      dut1.L5, dut1.U1, dut1.U2, dut1.blk[0].G);
    $display("OUT default %b %b %b %b %b %b %b %b", a0, b0, c0, p0, l0, s0, d0, g0);
    $display("OUT N=80,Q=2 %b %b %b %b %b %b %b %b", a1, b1, c1, p1, l1, s1, d1, g1);
    $display("GEN o %b", og);
    $finish;
  end
endmodule
