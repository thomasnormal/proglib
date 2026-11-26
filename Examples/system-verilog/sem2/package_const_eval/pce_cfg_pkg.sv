package pce_cfg;
  // A constant of another package aliased, then used (binding order).
  localparam int unsigned UNITS = pce_base::UNITS;
  localparam int unsigned UNIT_W = $clog2(UNITS);

  function automatic int unsigned bigger(input int unsigned a, input int unsigned b);
    return (a > b) ? a : b;
  endfunction
  // Nested calls, and a call inside arithmetic.
  localparam int unsigned M3 = bigger(bigger(UNITS, 5), 2) + 1;

  function automatic bit is_pow2(input int unsigned n);
    return (n != 0) && ((n & (n - 1)) == 0);
  endfunction
  localparam bit POW2 = is_pow2(UNITS);

  // A procedural body: a local, blocking assignments, an if chain.
  function automatic pce_base::wide_t pick(input int unsigned sel);
    pce_base::wide_t t;
    t = '0;
    if (sel == 1) begin
      t = pce_base::WIDE;
    end else if (sel == 2) begin
      t = '1;
    end
    return t;
  endfunction
  localparam pce_base::wide_t PICK1 = pick(1);
  localparam pce_base::wide_t PICK3 = pick(3);

  function automatic logic [63:0] pack2(input int unsigned hi, input int unsigned lo);
    return {hi, lo};
  endfunction
  localparam logic [63:0] P64 = pack2(7, 9);

  // A for loop over the bits of the argument.
  function automatic int unsigned ones8(input logic [7:0] v);
    int unsigned n;
    n = 0;
    for (int i = 0; i < 8; i++) begin
      if (v[i]) n = n + 1;
    end
    return n;
  endfunction
  localparam int unsigned ONES = ones8(8'b1011_0010);

  // A case statement; the result is assigned to the function name.
  function automatic logic [3:0] decode(input logic [1:0] s);
    case (s)
      2'd0: decode = 4'b0001;
      2'd1: decode = 4'b0010;
      2'd2: decode = 4'b0100;
      default: decode = 4'b1000;
    endcase
  endfunction
  localparam logic [3:0] DEC2 = decode(2'd2);
  localparam logic [3:0] DEC3 = decode(2'd3);

  // x and z bits carried through a function, a select and a concatenation.
  function automatic logic [7:0] pass(input logic [7:0] v);
    logic [7:0] t;
    t = v;
    return t;
  endfunction
  localparam logic [7:0] XZF = pass(pce_base::XZ8);
  localparam logic [3:0] XZSEL = pce_base::XZ8[5:2];
  localparam logic [11:0] XZCAT = {pce_base::XZ8[3:0], pce_base::XZ8};

  // Width and sign conversions at 33 and 65 bits.
  localparam logic [64:0] SX65 = pce_base::S32;
  localparam logic [64:0] ZX65 = pce_base::W32;
  localparam logic signed [32:0] SUM33 = pce_base::S32 + pce_base::NEG;
  localparam logic [32:0] CARRY33 = pce_base::W32 + pce_base::W32;
  localparam logic [31:0] PHI = pce_base::PAIR.hi;
  localparam logic [31:0] WFB = pce_base::WIDE.fb;

  // A recursive constant function: legal SystemVerilog that this loader does
  // not model. The constant is left unbound; only a module that reads it is
  // refused.
  function automatic int unsigned fact(input int unsigned n);
    return (n <= 1) ? 1 : n * fact(n - 1);
  endfunction
  localparam int unsigned F5 = fact(5);
endpackage
