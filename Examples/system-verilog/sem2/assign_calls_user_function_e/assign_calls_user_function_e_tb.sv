module assign_calls_user_function_e_tb;
  logic [3:0] a;
  wire [3:0] y;
  assign_calls_user_function_e dut(.a(a), .y(y));
  initial begin
    a=4'b0000; #1 $display("ROW %b %b", a, y);
    a=4'b0101; #1 $display("ROW %b %b", a, y);
    a=4'bx; #1 $display("ROW %b %b", a, y);
    $finish;
  end
endmodule
