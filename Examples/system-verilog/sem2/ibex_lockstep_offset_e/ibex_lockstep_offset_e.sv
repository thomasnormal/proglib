package ibex_lockstep_offset_e_pkg;
  function automatic int unsigned vbits(input int unsigned value);
    if (value == 0) vbits = 1;
    else begin
      vbits = 0;
      for (int unsigned n = value; n != 0; n = n >> 1) vbits++;
    end
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
