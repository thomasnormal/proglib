module typed_unpacked_net_tb;
  logic [7:0] x; wire [7:0] y;
  typed_unpacked_net dut(.x(x), .y(y));
  initial begin
    x=8'b10000011; #1 $display("ROW y=%b", y);
    x=8'b10000000; #1 $display("ROW y=%b", y);
    x=8'b10111101; #1 $display("ROW y=%b", y);
    x=8'b01111111; #1 $display("ROW y=%b", y);
    x=8'bx; #1 $display("ROW y=%b", y);
    x=8'bz; #1 $display("ROW y=%b", y);
    x=8'b00111000; #1 $display("ROW y=%b", y);
    x=8'b10100011; #1 $display("ROW y=%b", y); $finish;
  end
endmodule
