# Port-connection target wall

This parser-native repro follows the public generated-register shape. The
current extractor retains the whole output connection as an
`AggregateMember` target under IEEE 1800-2023 §23.2.2. The ordinary route then
reaches its named `Schedule:preemptive` refusal because the child
`always_comb` body has multiple blocking writes whose intermediate values may
be observed. Xcelium 24.03-s004 executes four x/z source rows. Icarus Verilog
13.0 reports its documented unsupported-unpacked-struct limitation, so no
Icarus oracle result is claimed.
