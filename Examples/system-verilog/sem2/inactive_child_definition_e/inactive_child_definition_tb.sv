module tb;
    logic a;
    logic y;
    inactive_child_definition dut (.a(a), .y(y));
    initial begin
        a=1'b0; #1 $display("ROW 0 a=%b y=%b",a,y);
        a=1'b1; #1 $display("ROW 1 a=%b y=%b",a,y);
        a=1'bx; #1 $display("ROW 2 a=%b y=%b",a,y);
        a=1'bz; #1 $display("ROW 3 a=%b y=%b",a,y);
        $finish;
    end
endmodule
