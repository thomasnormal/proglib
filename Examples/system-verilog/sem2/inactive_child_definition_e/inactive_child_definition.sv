module inactive_child_definition #(
    parameter int USE_VENDOR = 0
) (
    input logic a,
    output logic y
);
    generate
        if (USE_VENDOR) begin : vendor
            missing_vendor_child child (.a(a), .y(y));
        end else begin : portable
            assign y = a;
        end
    endgenerate
endmodule
