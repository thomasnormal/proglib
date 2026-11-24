# Package constant-function width receipt

This clean-room source exercises IEEE 1800-2023 §§6.20.2 and 20.8.1 with a
package-qualified automatic constant function in a parameterized packed-port
dimension. Canonical E evaluates the retained function body and `$clog2`
without inlining the source call. The ordinary row matches both pinned
simulators.
