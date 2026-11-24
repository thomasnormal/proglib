# Fixed-width logic localparam fixture

This clean-room fixture isolates the T4 wall where a fixed-width logic
`localparam` is used as a constant in a continuous assignment. Slang loads it
and the pinned simulators agree on the behavior. The current structural
summary refuses the RHS constant as outside its v1 expression fragment, so no
proof theorem is claimed yet; the source is intentionally not rewritten.
