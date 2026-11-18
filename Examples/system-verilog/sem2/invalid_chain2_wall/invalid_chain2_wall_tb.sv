module invalid_chain2_tb;
  logic [3:0] terms [0:3];
  wire [3:0] result;
  invalid_chain2_wall dut(.terms(terms), .result(result));
  initial begin
    terms[0]=4'h1; terms[1]=4'h2; terms[2]=4'h4; terms[3]=4'h8;
    #1 $display("ROW %b", result);
    terms[0]=4'hx; terms[1]=4'hz; terms[2]=4'h3; terms[3]=4'h5;
    #1 $display("ROW %b", result);
    $finish;
  end
endmodule
