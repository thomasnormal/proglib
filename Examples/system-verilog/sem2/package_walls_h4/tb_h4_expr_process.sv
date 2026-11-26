module tb;
  wire [31:0] o;
  leaf u(.o(o));
  initial begin
    #1 $display("o=%0d rec::Q=%h", o, rec::Q);
    $finish;
  end
endmodule
