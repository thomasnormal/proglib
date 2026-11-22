// IEEE 1800-2023 §9.2.2.3: a latch self-read before a later write.
module latch_self_read_a(input logic en, input logic a, output logic y);
  logic t;
  always_latch begin
    if (en) begin
      y = t;
      t = a;
    end
  end
endmodule
