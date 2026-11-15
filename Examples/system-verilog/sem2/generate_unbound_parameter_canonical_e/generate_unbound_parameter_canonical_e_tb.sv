module generate_unbound_parameter_canonical_e_tb;
  logic x; wire y;
  generate_unbound_parameter_top dut(.x(x), .y(y));
  initial begin
    x=1; #1 $display("ROW i=0 y=%b", y);
    x=1; #1 $display("ROW i=1 y=%b", y);
    x=1; #1 $display("ROW i=2 y=%b", y);
    x=1; #1 $display("ROW i=3 y=%b", y);
    x=1'bz; #1 $display("ROW i=4 y=%b", y);
    x=1; #1 $display("ROW i=5 y=%b", y);
    x=0; #1 $display("ROW i=6 y=%b", y);
    x=1; #1 $display("ROW i=7 y=%b", y); $finish;
  end
endmodule
