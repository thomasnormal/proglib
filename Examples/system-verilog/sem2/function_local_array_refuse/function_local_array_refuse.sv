module function_local_array(
  input logic [7:0] x,
  output logic [7:0] y
);
  function automatic logic [7:0] decode(input logic [7:0] node);
    logic [7:0] key [0:7];
    begin
      key[0] = 8'ha5;
      key[1] = 8'h3c;
      key[2] = 8'hf0;
      key[3] = 8'h17;
      key[4] = 8'h81;
      key[5] = 8'h42;
      key[6] = 8'h99;
      key[7] = 8'h0e;
      decode = key[node[2:0]] ^ node;
    end
  endfunction
  always_comb y = decode(x);
endmodule
