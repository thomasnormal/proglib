# Package aggregate defaults cross-check

The package parameter is an unpacked array of packed structs. Its parser-resolved
bitstream is retained in the envelope and compared by `load_design_sv2` with the
existing source-shaped aggregate binder under IEEE 1800-2023 §§6.20.2 and 10.9.2.
The module does not read the parameter, so the receipt isolates the load-time
differential. Icarus Verilog 13.0 rejects the unchanged packed-struct aggregate
parameter syntax. Xcelium 24.03-s004 accepts it.
