# Hierarchical value expression wall

The source reads `u.internal_value` across a child instance. Slang retains this
as the parser construct `HierarchicalValueExpression`; the extractor and
ordinary census keep the exact `parsePExpr` refusal under IEEE 1800-2023 §23.6.
Canonical E does not reparse or flatten this expression into an identifier.
Both pinned simulators produce `result=1` for the four-state source rows; the
receipt claims simulator behavior while the expression remains loud in E.
