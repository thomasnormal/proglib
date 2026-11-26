module pcr_leaf #(parameter logic [7:0] N = 8'h81, parameter int Q = 0) (
  output logic o_msb, output logic o_formal, output logic o_top,
  output logic [3:0] o_part, output logic [7:0] o_low4,
  output logic [39:0] o_sh, output logic [39:0] o_div,
  output logic [31:0] o_g);
  localparam logic L1 = pcr::msb_local(N);
  localparam logic L2 = pcr::msb_formal(N);
  localparam logic L3 = pcr::top_shifted(N);
  localparam logic [3:0] L4 = pcr::part_shifted(N);
  localparam logic [7:0] L5 = pcr::low4(N);
  localparam U1 = (Q > 0) ? pcr::M >>> 1 : 0;
  localparam U2 = (Q > 0) ? pcr::MU / Q : 0;
  // A module function reads the module's K, also when a generate scope
  // declares its own K.
  localparam int K = 1;
  function automatic int addk(input int x);
    return x + K;
  endfunction
  for (genvar g = 0; g < 1; g++) begin : blk
    localparam int K = 100;
    localparam int G = addk(1);
    assign o_g = G;
  end
  assign o_msb = L1;
  assign o_formal = L2;
  assign o_top = L3;
  assign o_part = L4;
  assign o_low4 = L5;
  assign o_sh = U1;
  assign o_div = U2;
endmodule
