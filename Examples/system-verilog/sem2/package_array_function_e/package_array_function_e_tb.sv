module package_array_function_e_tb;
  logic [7:0] i, o;
  package_array_function_e d(.i(i), .o(o));
  initial begin
    i = 8'h00; #1 $display("ROW 0 %h", o);
    i = 8'hff; #1 $display("ROW ff %h", o);
    i = 8'hxx; #1 $display("ROW x %h", o);
    i = 8'hzz; #1 $display("ROW z %h", o);
    $finish;
  end
endmodule
