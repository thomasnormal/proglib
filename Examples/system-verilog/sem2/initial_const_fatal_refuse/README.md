# Runtime `$fatal` in an initial process

This source-shaped fixture exercises the runtime system task boundary in an
`initial` process. The parser retains the `SysCall:$fatal` node, while
canonical E refuses it rather than giving a runtime diagnostic a zero-delay
meaning. The clocked process remains visible in the envelope.

For the safe default `N=1`, eight four-state edge rows match Icarus Verilog
13.0. The `N=0` source run is retained as a diagnostic-only refusal because
both pinned simulators terminate on `$fatal` before the edge rows.
