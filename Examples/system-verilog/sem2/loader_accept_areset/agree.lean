import LeanModels.Sv.ClockGuard2
namespace Examples.«system-verilog».sem2.loader_accept_areset.agree
open LeanModels.Sv
private def activeHigh : Design2 where
  name := "loader_accept_areset"
  decls := #[
    { name := "clk", width := 1, isInput := true },
    { name := "rst", width := 1, isInput := true },
    { name := "d", width := 1, isInput := true },
    { name := "q", width := 1, isOutput := true }]
  processes := #[.alwaysFFR "clk" "rst" (.nbaAssign (.ident "q") (.ident "d")) true]
#guard activeHigh.clockResetViol.isSome
#guard activeHigh.clockViolation.isSome
end Examples.«system-verilog».sem2.loader_accept_areset.agree
