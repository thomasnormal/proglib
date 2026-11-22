// IEEE 1800-2023 §9.2.2.3: a latch self-read before a conditional write.
module latch_self_read_b(input logic en, input logic a, output logic y);
  logic t;
  always_latch begin
    y = t;
    if (en) t = a;
  end
endmodule
