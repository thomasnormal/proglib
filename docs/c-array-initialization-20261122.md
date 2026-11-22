# Parser-native array initialization, 2026-11-22

The extractor already carries an array `QualType`, extent, element type, and element size. `Layout.elemDeclAt` now admits a bounded parser-native array shape, and `initObject` uses the element observations for each initializer and for §6.7.11p10 tail zeroing. The element spelling passed through this compatibility key is diagnostic only. Scalar and aggregate behavior comes from the carried `QualType` and layout facts.

The pre-registered rows `00117.c`, `20000819-1.c`, `20010222-1.c`, `20040805-1.c`, `920506-1.c`, `931110-2.c`, and `pr42142.c` moved to `passed`. `20031214-1.c` remains refused because its enclosing anonymous record member path is incomplete. The full replay moved C-MATCH from 1,012 to 1,082 of 2,214 and introduced no DIVERGE after the two new parser-native refusals.

The two clean-sanitizer failures exposed by this family are now loud refusals. Pointer-record bit-field resolution reaches the existing width boundary for `pr31448.c`, and incompatible character-to-integer pointer bit-casts refuse for `pr90025.c`. The pinned Clang 21.1.8 native and sanitizer runs for both rows exit 0.
