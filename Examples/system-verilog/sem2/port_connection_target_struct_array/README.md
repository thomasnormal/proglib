# Port-connection target wall

This parser-native repro follows the public generated-register shape. The
ordinary census reaches the canonical `Schedule:preemptive` refusal in
`PDesign.instantiateE2`. The source contains two blocking writes in the
reactive child process, so the refusal follows IEEE 1800-2023 §4.7 before
the aggregate port-copy path is run. Xcelium 24.03-s004 executes four x/z
source rows; Icarus Verilog 13.0 reports its documented unsupported-unpacked-
struct limitation, so no Icarus oracle result is claimed.
