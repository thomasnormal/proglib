// Interface instance, interface port, and interface connection.
interface generic_bus(input logic clock);
  logic request;
  logic response;
endinterface

module interface_repro(input logic clock, input logic value, output logic result);
  generic_bus bus(clock);
  interface_child child(.bus(bus), .result(result));
  assign bus.request = value;
endmodule

module interface_child(generic_bus bus, output logic result);
  always_comb result = bus.request;
endmodule
