module tb;
    logic [7:0] y;
    readmemh_parameter_file dut (.y(y));
    initial begin
        #1 $display("ROW 0 y=%b", y);
        #1 $finish;
    end
endmodule
