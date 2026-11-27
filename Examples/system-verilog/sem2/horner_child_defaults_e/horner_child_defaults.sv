module coefficient_child #(
    parameter integer WIDTH = 8,
    parameter integer ADDRESS_BITS = 2,
    parameter integer DEGREE = 2,
    parameter ROM_STYLE = "distributed"
) (
    input wire [ADDRESS_BITS-1:0] address,
    input wire [WIDTH-1:0] t,
    output wire [WIDTH+2:0] value
);
    localparam integer CB = WIDTH + 3;
    localparam integer ROW = CB * (DEGREE + 1);
    (* rom_style = ROM_STYLE *) reg [ROW-1:0] rom [0:3];
    assign value = {3'b000, t};
endmodule

module coefficient_parent #(
    parameter integer WIDTH = 8,
    parameter integer ADDRESS_BITS = 2,
    parameter integer DEGREE = 2,
    parameter ROM_STYLE = "distributed"
) (
    input wire [ADDRESS_BITS-1:0] address,
    input wire [WIDTH-1:0] t,
    output wire [WIDTH+2:0] value
);
    coefficient_child #(
        .WIDTH(WIDTH),
        .ADDRESS_BITS(ADDRESS_BITS),
        .DEGREE(DEGREE),
        .ROM_STYLE(ROM_STYLE)
    ) child (
        .address(address), .t(t), .value(value)
    );
endmodule
