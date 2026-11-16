module constant_width_conversion_e_tb;
  logic x; wire y8, y4;
  constant_width_conversion_e #(.E(8)) d8(.x(x), .y(y8));
  constant_width_conversion_e #(.E(4)) d4(.x(x), .y(y4));
  initial begin
    x=0; #1 $display("ROW x=0 y8=%b y4=%b", y8, y4);
    x=1; #1 $display("ROW x=1 y8=%b y4=%b", y8, y4);
    x=1'bx; #1 $display("ROW x=x y8=%b y4=%b", y8, y4);
    x=1'bz; #1 $display("ROW x=z y8=%b y4=%b", y8, y4);
    $finish;
  end
endmodule
