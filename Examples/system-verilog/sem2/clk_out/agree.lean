/-
Examples/system-verilog/sem2/clk_out — REFUSED by the clock discipline (`Clock:data-read`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): the clock is exported on an output port.
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_out`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_out.sv      — the SystemVerilog source
  clk_out.sv.json — generated envelope (extractors/sv/extract.py --top clk_out)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_out.agree

#guard_msgs (drop error) in
load_design_sv2 clk_out from "Examples/system-verilog/sem2/clk_out/clk_out.sv.json"

end Examples.«system-verilog».sem2.clk_out.agree
