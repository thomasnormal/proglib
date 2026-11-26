package rec;
  function automatic logic [63:0] pack2(input int unsigned hi, input int unsigned lo);
    return {hi, lo};
  endfunction
  localparam logic [63:0] P = pack2(7, 9);
endpackage
