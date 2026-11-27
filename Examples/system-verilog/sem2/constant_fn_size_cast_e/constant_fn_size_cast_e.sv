module leaf (input logic [7:0] i, output logic [7:0] o);
  function automatic bit aligned(input int unsigned n);
    int unsigned sh;
    sh = 32'($clog2(n));
    return ((n >> sh) << sh) == n;
  endfunction
  localparam bit K = aligned(8);
  assign o = i + {7'd0, K};
endmodule
