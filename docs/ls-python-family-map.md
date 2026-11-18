# Python family map

The machine design is the authoritative family map. This file keeps the
build order visible to readers who arrive from the lane index.

1. I. Relational machine and program logic
2. B. Scopes, names, functions as values, and minimal objects
3. H. Registry and argument binder
4. C. Iteration and generators
5. E. Exceptions as objects
6. A. Full object model
7. D. Containers and hashing
8. F. Modules
9. G. Numbers and strings on shared SoftFloat
10. J. Instruments and parity

Each family lands AST cases, differential rows, proof rules, and deletion
targets together. The relation is the one semantic definition. The old
interpreters remain compatibility artifacts until machine parity reaches every
row they decide with zero divergence.

See [docs/python-machine.md](python-machine.md) for the state, labels, choice
sets, resource raises, acceptance rows, and the two-interpreter deletion cost.
