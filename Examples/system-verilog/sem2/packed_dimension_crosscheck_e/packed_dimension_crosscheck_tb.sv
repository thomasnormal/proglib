module tb;
 reg clk=0,rst=0,valid_in=1; reg [31:0] a=32'h5a,b=32'ha5; wire valid_out; wire [31:0] result;
 always #1 clk=!clk;
 packed_dimension_child dut(.clk(clk),.rst(rst),.valid_in(valid_in),.a(a),.b(b),.valid_out(valid_out),.result(result));
 initial begin #2; if (result !== 32'hff) $fatal(1,"xor mismatch"); $display("TB_RESULT rows=1 errors=0"); $finish; end
endmodule
