# Package constant-function width receipt

This clean-room source exercises IEEE 1800-2023 §§6.20.2 and 13.4 with a
package-qualified automatic constant function in a parameterized packed-port
dimension. The function keeps a local `integer`, assigns it through a blocking
`case`, and returns through the function name, matching the Ibex `vbits`
shape. Canonical E evaluates the retained function body and `$clog2` without
inlining the source call. The ordinary row matches both pinned simulators.

The current receipt regenerates byte-identically and reports the single
package-function width row on both pinned simulators.
