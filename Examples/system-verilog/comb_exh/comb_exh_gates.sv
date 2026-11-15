// A gate design for `sv_exhaustive` (comb_exh): a full adder of continuous assigns, two outputs.
module comb_exh_gates (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic s,
    output logic cout
);
  assign s = (a ^ b) ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule
