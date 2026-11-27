module readmemh_parameter_file #(
    parameter MEMFILE = "values.mem",
    parameter int W = 8,
    parameter int D = 4
) (
    output logic [W-1:0] y
);
    logic [W-1:0] mem [0:D-1];
    initial $readmemh(MEMFILE, mem);
    assign y = mem[0];
endmodule
