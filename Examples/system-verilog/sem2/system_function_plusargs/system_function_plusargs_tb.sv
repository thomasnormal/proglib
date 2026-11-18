`timescale 1ns/1ps
module system_function_plusargs_tb;
    logic in;
    wire y;
    system_function_plusargs dut (.in(in), .y(y));

    task automatic row(input string label, input logic value);
        in = value;
        #1 $display("ROW %s plus=%0d in=%b y=%b", label, $test$plusargs("flag"), in, y);
    endtask

    initial begin
        row("zero", 1'b0);
        row("one", 1'b1);
        row("x", 1'bx);
        row("z", 1'bz);
        $finish;
    end
endmodule
