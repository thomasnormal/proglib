// Clean-room S1 scheduler wall.  Two always_comb processes can be
// interleaved between blocking statements under IEEE 1800-2023 §4.7.
module preemptive_schedule(
  input logic a,
  input logic b,
  output logic q,
  output logic r,
  output logic z
);
  always_comb begin
    q = a;
    r = q;
  end
  always_comb z = q;
endmodule
