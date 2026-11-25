# Shift/add datapath parser boundary

The source-shaped symbolic datapath from `shift_add_datapath_structure_timeout`
contains a parenthesized expression followed by an indexed select. Slang
retains the source and reports `SlangError:InvalidSelectExpression` under
IEEE 1800-2023 expression parsing. Ordinary E refuses the named diagnostic,
and both pinned simulators reject the source before simulation, so no oracle
value rows are claimed.
