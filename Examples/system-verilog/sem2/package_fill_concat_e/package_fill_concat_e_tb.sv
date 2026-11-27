module package_fill_concat_e_tb;
  logic [4:0] k0_4, k1_4; logic [1:0] u0_4, u1_4;
  logic [8:0] k0_8, k1_8; logic [1:0] u0_8, u1_8;
  package_fill_concat_e #(.W(4)) d4(.k0(k0_4), .k1(k1_4), .u0(u0_4), .u1(u1_4));
  package_fill_concat_e #(.W(8)) d8(.k0(k0_8), .k1(k1_8), .u0(u0_8), .u1(u1_8));
  initial begin
    #1;
    $display("ROW W=4 %b %b %b %b", k0_4, k1_4, u0_4, u1_4);
    $display("ROW W=8 %b %b %b %b", k0_8, k1_8, u0_8, u1_8);
    $finish;
  end
endmodule
