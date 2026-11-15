module readmemh_rom_canonical_e_tb;
  logic [1:0] addr; wire [7:0] q;
  readmemh_rom_canonical_e dut(.addr(addr), .q(q));
  initial begin
    addr=2'b00; #1 $display("ROW q=%b", q);
    addr=2'b01; #1 $display("ROW q=%b", q);
    addr=2'b10; #1 $display("ROW q=%b", q);
    addr=2'b11; #1 $display("ROW q=%b", q);
    addr=2'bxx; #1 $display("ROW q=%b", q); $finish;
  end
endmodule
