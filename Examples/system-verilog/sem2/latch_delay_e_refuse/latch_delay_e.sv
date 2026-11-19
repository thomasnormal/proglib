// IEEE 1800-2023 §9.2.2.3: timing controls are outside zero-delay latch E.
module latch_delay_e(input logic en, input logic a, output logic q);
  always_latch begin
    #1;
    if (en) q = a;
  end
endmodule
