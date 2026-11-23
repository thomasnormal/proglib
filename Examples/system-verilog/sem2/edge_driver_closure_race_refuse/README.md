# Same-edge race through selected and combinational drivers

This parser-native clean-room fixture covers IEEE 1800-2023 §§4.7 and 10.4.1
for two edge-reader paths. One crosses `assign w[0] = a`, and the other crosses
an `always_comb` driver. Canonical E closes both driver forms and refuses with
`Event:edge-blocking-race`.
