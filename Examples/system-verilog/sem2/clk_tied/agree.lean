/-
Examples/system-verilog/sem2/clk_tied — REFUSED by the clock discipline (`Clock:source`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): the clock is tied to a constant.
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_tied`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_tied.sv      — the SystemVerilog source
  clk_tied.sv.json — generated envelope (extractors/sv/extract.py --top clk_tied)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_tied.agree

#guard_msgs (drop error) in
load_design_sv2 clk_tied from "Examples/system-verilog/sem2/clk_tied/clk_tied.sv.json"

end Examples.«system-verilog».sem2.clk_tied.agree
