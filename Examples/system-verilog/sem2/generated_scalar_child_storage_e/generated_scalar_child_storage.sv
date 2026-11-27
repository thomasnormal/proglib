// A child module whose active generated arm owns scalar clocked storage.
module scalar_generated_child #(parameter int WIDTH = 8, parameter int DEPTH = 2) (
    input logic clk,
    input logic [WIDTH-1:0] data,
    output logic [WIDTH-1:0] out
);
  generate
    if (DEPTH == 0) begin : wire_through
      assign out = data;
    end else begin : shift
      logic [WIDTH-1:0] pipe;
      always @(posedge clk) pipe <= data;
      assign out = pipe;
    end
  endgenerate
endmodule

module scalar_generated_parent #(parameter int WIDTH = 8, parameter int DEPTH = 2) (
    input logic clk,
    input logic [WIDTH-1:0] data,
    output logic [WIDTH-1:0] out
);
  scalar_generated_child #(.WIDTH(WIDTH), .DEPTH(DEPTH)) child(
      .clk(clk), .data(data), .out(out));
endmodule
