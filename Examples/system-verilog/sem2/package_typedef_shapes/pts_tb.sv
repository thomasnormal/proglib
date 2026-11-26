module pts_tb;
  logic [3:0] a, c, e;
  logic [3:0] b;
  logic [5:0] d;
  wire [3:0] oa, oc, oe;
  wire [3:0] ob;
  wire [5:0] od;
  wire [7:0] op;
  wire [2:0] om;
  pts_leaf dut(.a(a), .b(b), .c(c), .d(d), .e(e), .oa(oa), .ob(ob), .oc(oc), .od(od), .oe(oe), .op(op), .om(om));
  initial begin
    $display("BITS a %0d b %0d c %0d d %0d e %0d v %0d w %0d mem[0] %0d", $bits(dut.a), $bits(dut.b), $bits(dut.c),
      $bits(dut.d), $bits(dut.e), $bits(dut.v), $bits(dut.w), $bits(dut.mem[0]));
    $display("PARAM P %0d K %0d K2 %0d SEL_INIT %0d PAIRS %h", dut.P, dut.K, dut.K2, pts_cfg::SEL_INIT, pts_cfg::PAIRS);
    a = 4'b1010; b = 4'b1001; c = 4'b0110; d = 6'b101100; e = 4'b0011;
    #1 $display("ROW %b %b %b %b %b | %b %b %b %b %b %b %b", a, b, c, d, e, oa, ob, oc, od, oe, op, om);
    a = 4'b1x0z; b = 4'bx01z; c = 4'bz1x0; d = 6'b1x0z10; e = 4'b0zx1;
    #1 $display("ROW %b %b %b %b %b | %b %b %b %b %b %b %b", a, b, c, d, e, oa, ob, oc, od, oe, op, om);
    $finish;
  end
endmodule
