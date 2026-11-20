// Clean-room differential for the DarkRISCV DADDR witness shape.
// An NBA register feeds a continuous output, so a post-edge sample must see
// the committed register value (IEEE 1800-2023 §§4.6, 10.4, 10.6).
module daddr_cleanroom(input logic clk, input logic [31:0] d,
                       output logic [31:0] q, output wire [31:0] y);
  always @(posedge clk)
    q <= d;
  assign y = q;
endmodule
