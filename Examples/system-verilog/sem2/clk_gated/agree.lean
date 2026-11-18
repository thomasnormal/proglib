/-
Examples/system-verilog/sem2/clk_gated — REFUSED by the clock discipline (`Clock:source`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): the clock is assign-derived (gated: clk & en).
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_gated`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_gated.sv      — the SystemVerilog source
  clk_gated.sv.json — generated envelope (extractors/sv/extract.py --top clk_gated)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_gated.agree

#guard_msgs (drop error) in
load_design_sv2 clk_gated from "Examples/system-verilog/sem2/clk_gated/clk_gated.sv.json"

end Examples.«system-verilog».sem2.clk_gated.agree
