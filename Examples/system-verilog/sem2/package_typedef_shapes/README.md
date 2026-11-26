# Typedef widths and shapes declared in packages

One module, `pts_leaf`, whose ports, variables and localparams are typed by
package typedefs (IEEE 1800-2023 §6.18, §7.4.1, §26.3):

- a typedef whose width is a parameter of its own package (`pts_base::sel_t`),
  as a port, a variable and a localparam type;
- a width written with `$clog2` of a package parameter (`pts_cfg::pos_t`),
  used as the element of a packed array whose dimension is a module
  parameter (`pts_cfg::pos_t [P-1:0]`), as a port and as a variable;
- a typedef of another package's typedef (`pts_cfg::my_sel_t`);
- a typedef of a packed array of another package's typedef
  (`pts_cfg::handles_t`);
- an unpacked array whose element is a package typedef
  (`pts_base::handle_t mem [P]`);
- a package-qualified width written on the port itself
  (`logic [pts_base::SW-1:0]`);
- a package constant typed by the typedef chain, and one that is a packed
  array of packed structs.

Each dimension bound is converted in the scope that declares it, so a bound
that names a package parameter is a package reference in the envelope, and
the use-site dimension keeps the module parameter.

Oracles: Xcelium 26.09-s001 (`oracle_xcelium.txt`) and Icarus Verilog 13.0
(`oracle_iverilog.txt`), the output of `pts_tb.sv`. Both report
`BITS a 4 b 4 c 4 d 6 e 4 v 4 w 6 mem[0] 3`, `PARAM P 2 K 5 K2 9 SEL_INIT 9 PAIRS
01020304`, and the same two `ROW` lines (one known input, one with x and z).

The envelope is `pts_leaf.sv.json` (`extractors/sv/extract.py --top pts_leaf
pts_pkg.sv pts_leaf.sv`).
