module initial_delay_check(input logic x, output logic y);
  assign y = x;
  initial begin
    #1;
    if (y !== x) $error("initial delay check failed");
  end
endmodule
