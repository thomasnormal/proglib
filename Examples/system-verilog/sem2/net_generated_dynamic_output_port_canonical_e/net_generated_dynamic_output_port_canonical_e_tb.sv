module net_generated_dynamic_output_port_canonical_e_tb;
  logic a, b; wire wready_o;
  net_generated_dynamic_output_port_canonical_e #(.N(1)) dut(.a(a), .b(b), .wready_o(wready_o));
  initial begin
    a=0; b=0; #1 $display("ROW i=0 wready_o=%b", wready_o);
    a=0; b=1; #1 $display("ROW i=1 wready_o=%b", wready_o);
    a=1; b=0; #1 $display("ROW i=2 wready_o=%b", wready_o);
    a=1; b=1; #1 $display("ROW i=3 wready_o=%b", wready_o); $finish;
  end
endmodule
