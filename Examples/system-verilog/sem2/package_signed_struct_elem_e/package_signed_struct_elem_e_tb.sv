module package_signed_struct_elem_e_tb;
  logic [7:0] i;
  logic [31:0] o;
  package_signed_struct_elem_e d(.i(i), .o(o));
  initial begin
    i = 8'h00; #1 $display("ROW 0 %h", o);
    i = 8'h01; #1 $display("ROW 1 %h", o);
    i = 8'hff; #1 $display("ROW ff %h", o);
    i = 8'hxx; #1 $display("ROW x %h", o);
    $finish;
  end
endmodule
