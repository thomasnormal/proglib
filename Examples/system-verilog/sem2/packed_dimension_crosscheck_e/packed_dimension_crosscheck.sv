module packed_dimension_child #(
    parameter integer EXPONENT = 8,
    parameter integer FRACTION = 23,
    parameter integer STAGES = 2,
    parameter USE_DSP = "yes"
) (
    input wire clk,
    input wire rst,
    input wire valid_in,
    input wire [EXPONENT+FRACTION:0] a, b,
    output reg valid_out,
    output reg [EXPONENT+FRACTION:0] result
);
    always @(posedge clk) begin
        valid_out <= !rst && valid_in;
        result <= a ^ b;
    end
endmodule
