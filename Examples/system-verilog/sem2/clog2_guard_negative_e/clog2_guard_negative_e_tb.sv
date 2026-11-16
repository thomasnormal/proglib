module clog2_guard_negative_e_tb;
  wire y_neg, y_zero;
  clog2_guard_negative_e dut_neg(.y(y_neg));
  clog2_guard_negative_e #(.N(0)) dut_zero(.y(y_zero));
  initial begin
    #1 $display("ROW N=-1 y=%b", y_neg);
    #1 $display("ROW N=0 y=%b", y_zero);
    $finish;
  end
endmodule
