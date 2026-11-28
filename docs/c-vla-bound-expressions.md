# C variable-length array bound expressions

C23 §6.7.7.3 evaluates a variable-length array bound once at the
declaration. The bound must be positive. The approved Clang record-layout
plugin now carries a parser-owned `bound_expr` payload on each VLA object,
including its node kind and parser type. A direct declaration reference also
retains the existing declaration-identity observation used to load the bound
value from the current environment.

The C envelope parses the payload into the existing expression AST. A bound
shape whose child nodes are not yet emitted by the plugin becomes an explicit
`Unsupported` expression and remains a loud refusal. The evaluator therefore
does not infer a bound from a type spelling or evaluate a partial expression.
When the declaration identity is present, the bound is loaded once and a
non-positive value is reported as undefined behavior. This item leaves
arithmetic, calls, and side effects inside a VLA bound refused until the
plugin carries their complete parser nodes and their C evaluation order can
be modelled.

CPP-DESIGN READY vla-bound-payload daa59508f
