module datapath #(parameter int WIDTH = 8)
    (input logic clk, rstn, load, exec,
     input logic [WIDTH-1:0] a, b,
     output logic [2*WIDTH-1:0] y);
  logic [WIDTH-1:0] ar, br, an, bn;
  logic [WIDTH:0] pr, pn;
  assign an = load ? a : ar;
  assign bn = load ? b : exec ? {1'b0, br[WIDTH-1:1]} : br;
  assign pn = load ? '0 : exec ? {1'b0, (pr + {1'b0, ar})[WIDTH:1]} : pr;
  assign y = {pr[WIDTH-1:0], ar};
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) {ar, br, pr} <= '0;
    else {ar, br, pr} <= {an, bn, pn};
endmodule
