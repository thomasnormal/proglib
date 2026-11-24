// Clean-room fixed-width localparam fixture for the sv_structure wall.
module localparam_logic(input logic [3:0] a, output logic [3:0] y);
  localparam logic [3:0] OP = 4'd1;
  assign y = a ^ OP;
endmodule
