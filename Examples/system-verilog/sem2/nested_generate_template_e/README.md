# Nested generate template selection

The outer generate loop starts at `i=0`; its nested loop `j < i` has no
instances in that first elaborated entry but has one at `i=1`. The extractor
selects the first outer entry with a live nested generated member while
retaining both loops symbolically. The agreement file checks that the
source-shaped generate family is retained. The undriven `y[0]` is kept as an
explicit observation boundary, so the runtime receipt claims only the
simulator source row `y=1z` (Icarus Verilog
13.0 and Xcelium 24.03-s004), with no E value claim for that unrelated
undriven-output boundary.
