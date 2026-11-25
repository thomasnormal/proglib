# Qualified package constant function in E

This clean-room source keeps a package function and a qualified call in a
typed localparam. Slang's resolved subroutine symbol supplies the package
provenance in the envelope; E evaluates the retained function body at the
same constant context. The three parameter points are differential rows for
Icarus Verilog 13.0 and Xcelium 24.03-s004. The current ordinary route keeps
the source-shaped call and refuses it loudly as `function 'vbits' in a
constant context`, because its defaults elaborator does not yet resolve this
qualified constant-function metadata.
