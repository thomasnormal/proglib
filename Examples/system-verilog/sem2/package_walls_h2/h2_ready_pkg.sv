package base;
  localparam int unsigned U = 4;
endpackage
package cfg;
  function automatic int unsigned bigger(input int unsigned a, input int unsigned b);
    return (a > b) ? a : b;
  endfunction
  localparam int unsigned D = base::U;       // a bare alias: deferred in the first binding pass
  localparam int unsigned M = bigger(D, 2);  // a call: "ready" without looking at its arguments
endpackage
