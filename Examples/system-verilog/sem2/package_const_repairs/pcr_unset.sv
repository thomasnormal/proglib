package pcr_u;
  // A four-state result that is never assigned (IEEE 1800-2023 6.8, 13.4.3).
  function automatic logic [3:0] unset(input logic a);
  endfunction
  localparam logic [3:0] UNSET = unset(1'b0);
endpackage
module pcr_unset (output logic [3:0] o);
  assign o = pcr_u::UNSET;
endmodule
