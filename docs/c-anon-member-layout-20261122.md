# Anonymous-record member identity, 2026-11-22

The anonymous record in `20031214-1.c` contains an array member `n`. Clang assigns that member its own declaration identity even though the enclosing record has no tag. `Layout` now carries and resolves field declaration IDs, so nested array initialization receives the member's parser-native array `QualType`, extent, and element size. Zero-fill follows the same identity path.

The row moved from `refused-unsupported` to `passed`. The full replay moved C-MATCH from 1,082 to 1,089 of 2,214, with 0 DIVERGE. The additional six matches are spillover from the shared field-identity path.
