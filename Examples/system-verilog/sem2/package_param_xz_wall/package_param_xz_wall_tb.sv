module package_param_xz_wall_tb;
  wire [31:0] y;
  package_param_xz_wall dut(.y(y));
  initial begin
    #1 $display("ROW %b", y);
    $finish;
  end
endmodule
