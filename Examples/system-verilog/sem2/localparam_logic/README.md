# Fixed-width logic localparam fixture

This clean-room fixture isolates the T4 wall where a fixed-width logic
`localparam` is used as a constant in a continuous assignment. Slang loads it
and the pinned simulators agree on the behavior. `sv_structure` currently
refuses the RHS at `plain#0` with:

```text
expression construct outside the v1 fragment (constant, cast, width conversion or system call)
```

The declaration itself is already admitted by `lpTypeOk`; the refusal is the
value-position `paramRef` in `a ^ OP`. A sound extension must carry the exact
`IEnv.nvals` value, width, and signedness of a fixed packed localparam through
`Summary.StructOk`, `Ctx.agree`, and the word-level equation theorem. Treating
it as a signed-32 affine constant would change IEEE 1800 sizing, so no proof
theorem is claimed yet and the source is intentionally not rewritten.
