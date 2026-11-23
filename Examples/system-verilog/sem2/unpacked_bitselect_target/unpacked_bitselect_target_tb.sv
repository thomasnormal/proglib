module unpacked_bitselect_target_tb;
  logic [3:0] a,b; logic [3:0] y;
  unpacked_bitselect_target #(.W(4)) dut(.a(a),.b(b),.y(y));
  initial begin
    a=4'h0; b=4'h0; #1 $display("ROW a=%h b=%h y=%h",a,b,y);
    a=4'ha; b=4'h3; #1 $display("ROW a=%h b=%h y=%h",a,b,y);
    a=4'hx; b=4'h5; #1 $display("ROW a=%h b=%h y=%h",a,b,y);
    a=4'hz; b=4'h5; #1 $display("ROW a=%h b=%h y=%h",a,b,y);
    $finish;
  end
endmodule
