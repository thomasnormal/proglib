module comb_unpacked_output_partial_def_tb;
  logic [3:0] a; logic [3:0] y [0:3];
  comb_unpacked_output_partial_def #(.W(4)) dut(.a(a), .y(y));
  initial begin
    a=4'h0; #1 $display("ROW a=%h y=%h%h%h%h",a,y[3],y[2],y[1],y[0]);
    a=4'ha; #1 $display("ROW a=%h y=%h%h%h%h",a,y[3],y[2],y[1],y[0]);
    a=4'hx; #1 $display("ROW a=%h y=%h%h%h%h",a,y[3],y[2],y[1],y[0]);
    a=4'hz; #1 $display("ROW a=%h y=%h%h%h%h",a,y[3],y[2],y[1],y[0]);
    $finish;
  end
endmodule
