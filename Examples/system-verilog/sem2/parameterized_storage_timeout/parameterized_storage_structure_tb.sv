module parameterized_storage_structure_tb;
  parameter integer P = 2;
  logic [7:0] x;
  wire [7:0] y;
  parameterized_storage_structure #(.N(P)) dut(.x(x), .y(y));
  initial begin
    x=8'h00; #1 $display("ROW y=%b", y);
    x=8'h01; #1 $display("ROW y=%b", y);
    x=8'h10; #1 $display("ROW y=%b", y);
    x=8'ha5; #1 $display("ROW y=%b", y);
    x=8'hff; #1 $display("ROW y=%b", y);
    x=8'hxx; #1 $display("ROW y=%b", y);
    x=8'hzz; #1 $display("ROW y=%b", y);
    x=8'h5a; #1 $display("ROW y=%b", y);
    $finish;
  end
endmodule
