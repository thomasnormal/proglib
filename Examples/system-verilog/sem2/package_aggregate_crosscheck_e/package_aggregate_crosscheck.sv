package package_aggregate_crosscheck_pkg;
  typedef struct packed { logic a; logic b; logic c; } word_t;
  parameter word_t TABLE [0:1] = '{'{a: 1'b0, b: 1'b0, c: 1'b1},
                                    '{a: 1'b1, b: 1'b1, c: 1'b0}};
endpackage

module package_aggregate_crosscheck (
    output logic y
);
  assign y = 1'b0;
endmodule
