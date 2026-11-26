# Package constants, constant functions and typedef widths

One design, `pce_leaf`, over two packages. Every constant is evaluated by the
loader's constant evaluator and compared with the reference simulator.

What the rows cover (IEEE 1800-2023):

- Package constants at widths 1, 32, 33, 64, 65 and 1088, signed and
  unsigned, with x and z digits (§6.20.2, §6.20.4, §11.6, §11.8).
- A constant of one package that reads a constant of another, declared before
  and after its readers (binding in dependency order, §26.3).
- Constant functions (§13.4.3): a single return, nested calls, a call inside
  arithmetic, a procedural body with a local, blocking assignments and an
  `if` chain, a `for` loop, a `case`, a result assigned to the function name
  (§13.4.1), a 1088-bit packed-struct result, x and z bits carried through a
  call.
- A module localparam whose value is a package function called with a module
  function, and a generate-local localparam computed from the genvar
  (§27.4, §6.20.4).
- A recursive constant function. It is legal SystemVerilog that the loader
  does not model: its constant `pce_cfg::F5` is left unbound with the reason,
  `pce_leaf`, which does not read it, loads, and `pce_reads_refused`, which
  reads it in a continuous assignment, gets a loud `ParamRef:package` node.

Oracle: Xcelium 26.09-s001, `oracle_xcelium.txt` (the output of `pce_tb.sv`;
the command is its first line). The `CONST` rows are the bit strings that
`agree.lean` pins; `HEX` rows print the 1088-bit values in hexadecimal;
`PARAM` gives `W`, `K` and the two generate-local values; `ROW` gives the
outputs for one known and one x/z input.

Icarus Verilog 13.0 does not parse the packed-struct assignment pattern of a
package parameter (`pce_base_pkg.sv:13: syntax error`): no Icarus result is
claimed for this design.

The envelopes are `pce_leaf.sv.json` and `pce_reads_refused.sv.json`
(`extractors/sv/extract.py --top <module>` over the two packages and the
module, in that order).
