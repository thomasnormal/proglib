// Single-write control for d03 (master's old guard admits it as well).
module level_event_comb_race_e(input logic en, input logic a, b, output logic y);
  logic nxt;
  always @(a or b or en) y = nxt;
  always_comb nxt = en ? b : a;
endmodule
