module package_unsigned_member_canonical_e_tb;
  logic [7:0] i;
  logic [31:0] o0, o1;
  package_unsigned_member_canonical_e #(.K(0)) u0(.i(i), .o(o0));
  package_unsigned_member_canonical_e #(.K(1)) u1(.i(i), .o(o1));
  initial begin
    i = 8'd1; #1;
    $display("ROW o0=%h o1=%h", o0, o1);
    $finish;
  end
endmodule
