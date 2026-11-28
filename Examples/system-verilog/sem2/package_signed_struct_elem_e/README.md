# Signed packed-struct element from a package array

This clean-room row exercises a whole signed packed-struct element read from an unpacked package array and a size cast. IEEE 1800-2023 §§6.24.1 and 7.2.1 require sign extension. Slang's aggregate metadata currently reports the package aggregate as unsigned, so the ordinary route refuses the shape loudly instead of silently zero-extending it. Xcelium Verilog 24.03-s004 reports the reference rows. Icarus Verilog 13.0 refuses the unpacked package-array parameter syntax, so no Icarus value result is claimed.
