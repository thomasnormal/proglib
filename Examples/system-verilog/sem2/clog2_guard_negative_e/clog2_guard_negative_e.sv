module clog2_guard_negative_e #(parameter int N = -1)(output logic y);
  generate
    if ($clog2(N) & 32) begin : g_match
      assign y = 1'b1;
    end else begin : g_other
      assign y = 1'b0;
    end
  endgenerate
endmodule
