# Empty nested generate-template refusal

The outer generate loop has `j=0` as its first default iteration. Its nested
loop `k=0..j-1` therefore has no elaborated body at that iteration, while a
later outer iteration is nonempty. The approved extractor retains the outer
symbolic loop but refuses the missing inner template as
`GenerateFor:no-template`; it does not copy a later iteration into the empty
one. No E row is claimed. The unchanged source runs as `y=1z` on Icarus
Verilog 13.0 and Xcelium `xrun(64)` 24.03-s004.
