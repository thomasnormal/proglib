module mixed_array_edge_e_tb;
  logic clk, i_clk;
  logic [7:0] d;
  logic [15:0] o;
  mixed_array_edge_e dut(.clk(clk), .d(d), .o(o));
  initial begin
    clk = 1'b0; d = 8'h01; #1 $display("ROW 0 %h", o);
    clk = 1'b1; #1 $display("ROW 1 %h", o);
    clk = 1'b0; d = 8'h10; #1 $display("ROW 2 %h", o);
    clk = 1'b1; #1 $display("ROW 3 %h", o);
    clk = 1'b0; d = 8'hff; #1 $display("ROW 4 %h", o);
    $finish;
  end
endmodule
