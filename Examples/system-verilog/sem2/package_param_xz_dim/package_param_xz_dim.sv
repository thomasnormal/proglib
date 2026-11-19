package p; parameter logic [3:0] MASK=4'b1z0z; endpackage
module m(output logic y); import p::*; logic [MASK:0] x; assign x='0; assign y=x[0]; endmodule
