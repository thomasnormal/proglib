module tb;
    logic [3:0] a;
    logic [3:0] y;
    implicit_event_loop dut (.a(a), .y(y));
    initial begin
        a=4'b0000; #1 $display("ROW 0 a=%b y=%b",a,y);
        a=4'b0001; #1 $display("ROW 1 a=%b y=%b",a,y);
        a=4'b1010; #1 $display("ROW 2 a=%b y=%b",a,y);
        a=4'bxxxx; #1 $display("ROW 3 a=%b y=%b",a,y);
        a=4'bzzzz; #1 $display("ROW 4 a=%b y=%b",a,y);
        $finish;
    end
endmodule
