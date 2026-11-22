module untyped_localparam_exact_tb;
  wire [31:0] k,a,u,p,ls,rs,neg,cat,signed_kw,range_only,observed,observed_w;
  wire [31:0] k2,a2,u2,p2,ls2,rs2,neg2,cat2,signed_kw2,range_only2,observed2,observed_w2;
  untyped_localparam_exact d(.k(k),.a(a),.u(u),.p(p),.ls(ls),.rs(rs),.neg(neg),
    .cat(cat),.signed_kw(signed_kw),.range_only(range_only),.observed(observed),
    .observed_w(observed_w));
  untyped_localparam_exact #(.N(8)) e(.k(k2),.a(a2),.u(u2),.p(p2),.ls(ls2),.rs(rs2),
    .neg(neg2),.cat(cat2),.signed_kw(signed_kw2),.range_only(range_only2),
    .observed(observed2),.observed_w(observed_w2));
  initial begin
    #1;
    $display("ROW N=10000 k=%0d a=%0d u=%0d p=%0d ls=%0d rs=%0d neg=%0d cat=%0d signed=%0d range=%0d observed=%0d observed_w=%0d", k,a,u,p,ls,rs,neg,cat,signed_kw,range_only,observed,observed_w);
    $display("ROW N=8 k=%0d a=%0d u=%0d p=%0d ls=%0d rs=%0d neg=%0d cat=%0d signed=%0d range=%0d observed=%0d observed_w=%0d", k2,a2,u2,p2,ls2,rs2,neg2,cat2,signed_kw2,range_only2,observed2,observed_w2);
    $finish;
  end
endmodule
