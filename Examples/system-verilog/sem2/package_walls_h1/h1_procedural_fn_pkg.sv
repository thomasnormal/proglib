package rec;
  typedef struct packed { logic [15:0] fa; logic [15:0] fb; } rec_t;
  localparam rec_t R_FAST = '{fa: 16'd10, fb: 16'd12};
  localparam rec_t R_SLOW = '{fa: 16'd9,  fb: 16'd11};
  function automatic rec_t pick(input int unsigned sel);
    rec_t t;
    t = '0;
    if (sel == 1) begin
      t = R_FAST;
    end else if (sel == 2) begin
      t = R_SLOW;
    end
    return t;
  endfunction
  localparam int unsigned SEL = 1;
  localparam rec_t R = pick(SEL);
endpackage
