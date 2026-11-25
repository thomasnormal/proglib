# Continuous user-function assignment receipt

The parser-native `FunctionCall` nodes are retained with `--retain-proc-rewrites`. Canonical E evaluates the automatic input-only function at execution through `evalFunction` under IEEE 1800-2023 §13.4. Three source rows, including x startup, match Icarus Verilog 13.0 and Xcelium 24.03-s004.
# Clean-room wall coverage

This receipt covers the `assign_calls_user_function` wall. The ordinary route
evaluates the retained function call through `evalFunction`.
