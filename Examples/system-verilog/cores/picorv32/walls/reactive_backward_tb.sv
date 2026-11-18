module reactive_backward_tb;
  logic a;
  logic y;
  reactive_backward dut(.a(a), .y(y));

  initial begin
    a = 1'b0;
    $display("ROW t=0 a=%b y=%b", a, y);
    #1;
    a = 1'b1;
    #1;
    $display("ROW t=2 a=%b y=%b", a, y);
    #1;
    $display("ROW t=3 a=%b y=%b", a, y);
    $finish;
  end
endmodule
