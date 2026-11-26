package pcr;
  // Selects of function variables whose declared range is not [m:0].
  function automatic logic msb_local(input logic [7:0] x);
    logic [0:7] v;
    v = x;
    return v[0];
  endfunction
  function automatic logic msb_formal(input logic [0:7] v);
    return v[0];
  endfunction
  function automatic logic top_shifted(input logic [7:0] x);
    logic [11:4] v;
    v = x;
    return v[11];
  endfunction
  function automatic logic [3:0] part_shifted(input logic [7:0] x);
    logic [8:1] v;
    v = x;
    return v[8:5];
  endfunction
  // A write to one bit of the function-name result, range [0:3].
  function automatic logic [0:3] set_result(input logic b);
    set_result = 4'b000x;
    set_result[0] = b;
  endfunction
  localparam logic [1:0] PX = {msb_local(8'h80), 1'bx};
  localparam logic [0:3] RES = set_result(1'b1);

  // Explicit casts.
  localparam logic [8:0] CX = {1'bx, 8'(4'(8'hAB))};
  localparam logic [15:0] CA = 4'(8'hAB);
  localparam logic [7:0] CD = unsigned'(-4'sd4);
  function automatic logic [7:0] low4(input logic [7:0] x);
    return 4'(x);
  endfunction

  // Signed constants, typed and untyped.
  parameter int M = -3;
  parameter MU = -3;

  // A static function in a constant call.
  function int twice_static(input int n);
    twice_static = n + n;
  endfunction
  localparam int TS = twice_static(21);

endpackage
