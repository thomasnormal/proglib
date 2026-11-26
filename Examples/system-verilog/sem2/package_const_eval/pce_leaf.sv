module pce_leaf #(parameter int unsigned W = pce_cfg::UNIT_W + 2) (
  input  logic [W-1:0] i,
  input  logic [7:0] a,
  output logic [W-1:0] o,
  output logic [1:0] q,
  output logic [31:0] hi,
  output logic [7:0] xz,
  output logic [31:0] fb);
  // A module function with a local variable.
  function automatic int unsigned twice(input int unsigned n);
    int unsigned t;
    t = n;
    t = t + n;
    return t;
  endfunction
  // A package function whose argument is a call of a module function.
  localparam int unsigned K = pce_cfg::bigger(twice(W), 3);
  for (genvar g = 0; g < 2; g++) begin : gen
    // A generate-local constant computed by a call with the genvar.
    localparam int unsigned GK = $clog2(twice(g + 1) + 1);
    assign q[g] = a[GK];
  end
  assign o = i ^ K[W-1:0];
  assign hi = pce_cfg::P64[63:32];
  assign xz = pce_cfg::XZF;
  assign fb = pce_cfg::PICK1.fb;
endmodule
