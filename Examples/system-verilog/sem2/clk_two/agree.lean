import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_two.agree

open LeanModels.Sv

/-! The source fixture is intentionally not loaded through the ordinary
one-clock command: its two independent edge clocks must be refused until the
owner accepts a multi-clock transport. -/
private def twoClock : Design2 where
  name := "two_clock"
  decls := #[
    { name := "clk1", width := 1, isInput := true },
    { name := "clk2", width := 1, isInput := true },
    { name := "d", width := 1, isInput := true },
    { name := "a", width := 1 }, { name := "b", width := 1 }]
  processes := #[
    .alwaysFF "clk1" (.nbaAssign (.ident "a") (.ident "d")),
    .alwaysFF "clk2" (.nbaAssign (.ident "b") (.ident "a"))]

#guard twoClock.clockNames.length == 2
#guard twoClock.multiClockReport.isSome

end Examples.«system-verilog».sem2.clk_two.agree
