// A two-flop synchronizer carrying one bit from clka's domain (src) to clkb's (s1, s2): s1 reads src, a crossing.
// A statement about this design is LANGUAGE-LEVEL: IEEE 1800-2023 gives s1 the committed value of src at clkb's rising
// edge (§9.4.2, §10.4.2); hardware can make s1 metastable when src changes near that edge, which is not modelled.
module sync2 (
  input  logic clka, clkb, d,
  output logic q
);
  logic src, s1, s2;
  always_ff @(posedge clka) src <= d;
  always_ff @(posedge clkb) begin
    s1 <= src;
    s2 <= s1;
  end
  assign q = s2;
endmodule
