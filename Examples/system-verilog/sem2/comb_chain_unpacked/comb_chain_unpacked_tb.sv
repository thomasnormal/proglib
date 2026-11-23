module comb_chain_unpacked_tb;
  logic clk; logic [7:0] q;
  comb_chain_unpacked #(.W(8)) dut(.clk(clk),.q(q));
  initial begin clk=0; force dut.q=8'hfc; #1 $display("ROW q=%h s0=%h s1=%h s2=%h",q,dut.s[0],dut.s[1],dut.s[2]); clk=1; #1 $display("ROW q=%h s0=%h s1=%h s2=%h",q,dut.s[0],dut.s[1],dut.s[2]); release dut.q; clk=0; #1 $display("ROW q=%h s0=%h s1=%h s2=%h",q,dut.s[0],dut.s[1],dut.s[2]); clk=1; #1 $display("ROW q=%h s0=%h s1=%h s2=%h",q,dut.s[0],dut.s[1],dut.s[2]); $finish; end
endmodule
