module unbound_child_parameter_canonical_e_tb;
  logic [7:0] x; wire [7:0] y;
  unbound_child_parameter_top dut(.x(x), .y(y));
  initial begin
    x=8'b0; #1 $display("ROW i=0 y=%b", y);
    x=8'b1; #1 $display("ROW i=1 y=%b", y);
    x=8'd42; #1 $display("ROW i=2 y=%b", y);
    x=8'hff; #1 $display("ROW i=3 y=%b", y);
    x=8'bxxxxxxxx; #1 $display("ROW i=4 y=%b", y);
    x=8'bzzzzzzzz; #1 $display("ROW i=5 y=%b", y);
    x=8'd127; #1 $display("ROW i=6 y=%b", y);
    x=8'd128; #1 $display("ROW i=7 y=%b", y); $finish;
  end
endmodule
