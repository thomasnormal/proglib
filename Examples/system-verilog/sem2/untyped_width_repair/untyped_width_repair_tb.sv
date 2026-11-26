module untyped_width_repair_tb;
  logic [7:0] y_default, y_override;
  untyped_width_repair d0(.y(y_default));
  untyped_width_repair #(.P(-2)) d1(.y(y_override));
  initial begin
    #1 $display("ROW default=%b override=%b", y_default, y_override);
    $finish;
  end
endmodule
