module tb;
  logic clk = 1'b0;
  logic [7:0] data;
  logic [7:0] out;
  scalar_generated_parent #(.WIDTH(8), .DEPTH(2)) dut(.clk(clk), .data(data), .out(out));
  task automatic row(input integer n, input logic [7:0] v);
    begin
      data = v;
      #1 clk = 1'b1;
      #1 $display("ROW %0d data=%b out=%b", n, data, out);
      #1 clk = 1'b0;
      #1;
    end
  endtask
  initial begin
    data = 8'b0;
    #1;
    row(0, 8'b00000000);
    row(1, 8'b10101100);
    row(2, 8'b11110000);
    row(3, 8'bxxxxxxxx);
    row(4, 8'bzzzzzzzz);
    $finish;
  end
endmodule
