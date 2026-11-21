// Clean-room differential for a 5-bit dynamic register-file index.
module daddr_memory5_cleanroom(input logic clk, input logic [4:0] idx,
                               input logic [31:0] d, output wire [31:0] y);
  logic [31:0] regs [0:31];
  always @(posedge clk)
    regs[idx] <= d;
  assign y = regs[idx];
endmodule
