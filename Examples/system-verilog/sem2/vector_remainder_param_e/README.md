# Parameterized vector remainder receipt

This source exercises the vector `%` operator in a typed constant expression
under IEEE 1800-2023 §§11.4.3 and 11.8. Canonical E evaluates the packed
operands at their common width and preserves the remainder value through the
parameter binding. Both pinned simulators match the ordinary row.
