module tb;
    reg [1:0] address;
    reg [7:0] t;
    wire [10:0] value;
    coefficient_parent dut(.address(address), .t(t), .value(value));
    initial begin
        address=0; t=8'h00; #1;
        if (value !== 11'h000) $fatal(1, "zero row mismatch");
        address=2; t=8'hA5; #1;
        if (value !== 11'h0A5) $fatal(1, "data row mismatch");
        t=8'hxx; #1;
        if (value !== 11'h0xx) $fatal(1, "x row mismatch");
        t=8'hzz; #1;
        if (value !== 11'h0zz) $fatal(1, "z row mismatch");
        $display("TB_RESULT rows=4 errors=0");
        $finish;
    end
endmodule
