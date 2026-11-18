// Clean-room witness for the whole-core E running wall.  The first reactive
// process reads a value written by the later process.  IEEE 1800-2023
// §9.2.2.2.1 permits the later event to wake the earlier process.
module reactive_backward(
  input logic a,
  output logic y
);
  logic t;
  always @* begin
    y = t;
  end
  always @* begin
    t = a;
  end
endmodule
