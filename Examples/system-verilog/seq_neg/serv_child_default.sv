module serv_child_ram #(parameter width=0, parameter depth=8/width)
  (input logic clk, wen, input logic [1:0] addr,
   input logic [width-1:0] data, output logic [width-1:0] value);
  logic [width-1:0] memory [0:depth-1];
  always @(posedge clk) if (wen) memory[addr] <= data;
  assign value = memory[addr];
endmodule

module serv_child_default #(parameter W=2)
  (input wire clk, wen, input wire [1:0] addr,
   input wire [W-1:0] data, output wire [W-1:0] value);
  serv_child_ram #(.width(W)) cell0(clk, wen, addr, data, value);
endmodule
