# Timed delay control wall

This parser-native fixture contains `#1 q <= d` inside an edge process. The
ordinary census retains the exact `TimedStatement:DelayControl / parsePStmt`
boundary under IEEE 1800-2023 §9.4. Canonical E deliberately remains
zero-delay and refuses timed controls rather than choosing a timing schedule.
Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on the four source rows after
one nanosecond settles; the receipt claims simulator behavior only.
