module package_param_xz_ops_tb;
  logic [3:0] a;
  wire casez_hit, inside_hit, caseeq_hit;
  package_param_xz_ops dut(a, casez_hit, inside_hit, caseeq_hit);
  task show; $display("ROW %b %b %b %b", a, casez_hit, inside_hit, caseeq_hit); endtask
  initial begin
    a = 4'b1101; #1 show();
    a = 4'b1111; #1 show();
    a = 4'b1z0z; #1 show();
    $finish;
  end
endmodule
