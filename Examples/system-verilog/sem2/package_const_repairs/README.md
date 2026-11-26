# Constant functions, casts and signed package constants: repair rows

Each row here is a value the loader once produced wrongly without a refusal.
`pcr_leaf` is evaluated at its default point and at `#(.N(8'h80), .Q(2))`;
`pcr_gen` has no parameters.

- **Selects of function variables whose range is not `[m:0]`** (IEEE
  1800-2023 §7.4.1, §11.5.1): a local `[0:7]`, a formal `[0:7]`, a local
  `[11:4]`, a part select of a local `[8:1]`, a bit write to a `[0:3]`
  function result. The frontend writes a literal label of such a range as an
  offset; the evaluator reads an index of a function variable as an offset
  and does not translate it again. At `N = 8'h80` only the most significant
  bit is set, so reading the wrong end gives 0.
- **A module function called from a generate scope** (§13.4.3, §23.9) reads
  the module's `K = 1`, not the `K = 100` the generate block declares.
- **Explicit casts** (§6.24.1): a size cast in a package constant, nested and
  beside an x bit (`{1'bx, 8'(4'(8'hAB))}`), a size cast in a package
  function called at two points (`4'(x)`), and `unsigned'(-4'sd4)`.
- **Signed package constants**, typed (`int M = -3`) and untyped
  (`MU = -3`), read by an untyped localparam (`M >>> 1`, `MU / Q`) and as a
  genvar's initial value.
- **A static function** in a constant call (§13.4.3: each elaboration-time
  call starts from the variables' initial values).

Oracles: Xcelium 26.09-s001 (`oracle_xcelium.txt`) and Icarus Verilog 13.0
(`oracle_iverilog.txt`), the output of `pcr_tb.sv` over `pcr_pkg.sv`,
`pcr_leaf.sv` and `pcr_gen.sv`. The two files are identical below their first
line. `agree.lean` pins every `CONST`, `POINT` and `GEN` value.

`pcr_unset.sv` is not in the testbench: a four-state function result that is
never assigned. The loader gives x (§6.8, §13.4.3). Xcelium folds 0 at
elaboration and gives x at run time; no oracle result is claimed for the
elaboration value. Icarus 13.0 does not evaluate the call.

Envelopes: `pcr_leaf.sv.json` (`--top pcr_leaf pcr_pkg.sv pcr_leaf.sv`),
`pcr_gen.sv.json` (`--top pcr_gen pcr_pkg.sv pcr_gen.sv`), `pcr_unset.sv.json`
(`--top pcr_unset pcr_unset.sv`).
