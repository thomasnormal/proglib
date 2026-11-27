// d08's mechanism with a legacy explicit-list writer always @(ar or b or en), which
// neither the old nor the new preemptive guard classifies as a writer.
// en=1, b=0: old == final == 0; intermediate == new ar == 1 at rows 3 and 7.
module legacy_event_writer_race_e(input logic clk, input logic rst, input logic en,
                                   input logic din, b, output logic q, div);
  logic ar, nxt;
  always_ff @(posedge clk) begin
    ar <= din;
    div <= ~div & ~rst;
  end
  always @(ar or b or en) begin
    nxt = ar;
    if (en) nxt = b;
  end
  always_ff @(posedge div) q <= nxt;
endmodule
