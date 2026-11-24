package ibex_lockstep_offset_e_pkg;
  function automatic int unsigned vbits(input int unsigned value);
    return (value == 1) ? 1 : $clog2(value);
  endfunction
endpackage

module ibex_lockstep_offset_e #(
  parameter int unsigned LockstepOffset = 4,
  localparam int unsigned LockstepOffsetW = ibex_lockstep_offset_e_pkg::vbits(LockstepOffset)
) (
  input logic [LockstepOffsetW-1:0] i,
  output logic [LockstepOffsetW-1:0] o);
  assign o = i;
endmodule
