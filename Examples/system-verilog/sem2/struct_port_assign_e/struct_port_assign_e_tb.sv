module struct_port_assign_e_tb;
  logic [3:0] instr_i;
  logic valid_i;
  logic [1:0] tag_i;
  logic [6:0] y;
  struct_port_assign_e dut(.instr_i(instr_i), .valid_i(valid_i), .tag_i(tag_i), .y(y));
  task row(input logic [3:0] instr, input logic valid, input logic [1:0] tag);
    begin instr_i = instr; valid_i = valid; tag_i = tag; #1 $display("ROW %b %b", {instr, valid, tag}, y); end
  endtask
  initial begin
    row(4'h0, 1'b0, 2'b00);
    row(4'ha, 1'b1, 2'b01);
    row(4'bx, 1'bz, 2'bxz);
    $finish;
  end
endmodule
