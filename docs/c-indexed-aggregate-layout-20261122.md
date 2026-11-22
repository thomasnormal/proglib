# Indexed aggregate layout, 2026-11-22

The `931004-*.c` rows pass `struct tiny` values by value from an array. Clang's envelope carries the array-to-pointer and record `QualType` nodes plus the record's parser-native size. The evaluator now uses the indexed element's observed size and structured element type for the lvalue-to-rvalue load under C23 §6.3.2.1p2. It no longer asks for the containing array object's extent when loading `x[i]`.

The seven rows `931004-1.c`, `931004-3.c`, `931004-5.c`, `931004-7.c`, `931004-9.c`, `931004-11.c`, and `931004-13.c` moved from `refused-unsupported` to `passed`. Pinned Clang 21.1.8 at `-O0` and `-O2` returned 0 for all seven rows. The full replay moved C-MATCH from 1,004 to 1,012 of 2,214, with 0 DIVERGE.
