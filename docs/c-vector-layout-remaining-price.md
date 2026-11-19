# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic walls: `unsupported:no layout for declared type 'V'`, `unsupported:no layout for compound literal type 'V'`, `unsupported:no layout for compound literal type 'v2si'`, `unsupported:no layout for compound literal type 'v4hi'`, `unsupported:no layout for declared type 'V2SF'`, `unsupported:no layout for declared type 'V2SI'`, `unsupported:no layout for declared type 'V32'`, `unsupported:no layout for declared type 'V[32]'`, `unsupported:no layout for declared type '__attribute__((__vector_size__(16 * sizeof(char)))) char'`, `unsupported:no layout for declared type '__attribute__((__vector_size__(4 * sizeof(float)))) float'`, `unsupported:no layout for declared type '__attribute__((__vector_size__(8 * sizeof(short)))) short'`, `unsupported:no layout for declared type '__m128i'`, `unsupported:no layout for declared type 'v4qi'`, `unsupported:no layout for declared type 'v4si'`, `unsupported:no layout for declared type 'v8qi'`, `unsupported:no layout for declared type 'vecint'`, `unsupported:sizeof: no layout for operand type 'v4flt'`, `unsupported:no layout for declared type 'Q'`
- candidate files: **26**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `20050316-2.c` | 7 | `8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `20050316-3.c` | 4 | `8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `20050604-1.c` | 5 | `8/8, 16/16, 4/4, 8/8, 16/16` |
| `gcc.c-torture/execute` | `20060420-1.c` | 20 | `8/8, 8/8, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 16/16, 16/16, 16/16, 16/16, 4/4, 256/4, 4/4, 8/8, 16/8, 8/8, 4/4` |
| `gcc.c-torture/execute` | `ieee/fp-cmp-cond-1.c` | 22 | `4/4, 4/4, 4/4, 4/4, 1/1, 1/1, 4/4, 4/4, 4/4, 4/4, 1/1, 1/1, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `ieee/pr72824-2.c` | 5 | `8/8, 16/16, 4/4, 512/16, 16/16` |
| `gcc.c-torture/execute` | `pr105613.c` | 6 | `16/16, 8/8, 16/16, 16/16, 16/16, 16/16` |
| `gcc.c-torture/execute` | `pr109040.c` | 11 | `2/2, 2/2, 2/2, 2/2, 32/32, 8/8, 32/32, 32/32, 2/2, 2/2, 32/32` |
| `gcc.c-torture/execute` | `pr110817-1.c` | 3 | `8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr110817-2.c` | 3 | `8/8, 1/1, 8/8` |
| `gcc.c-torture/execute` | `pr110817-3.c` | 4 | `4/4, 1/1, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr23135.c` | 19 | `4/4, 8/8, 8/8, 8/8, 8/8, 4/4, 4/4, 4/4, 4/4, 131072/1, 131072/1, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr60960.c` | 8 | `4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr70903.c` | 7 | `32/32, 32/32, 32/32, 32/32, 32/32, 32/32, 32/32` |
| `gcc.c-torture/execute` | `pr71626-1.c` | 2 | `8/8, 8/8` |
| `gcc.c-torture/execute` | `pr85169.c` | 5 | `8/8, 64/64, 64/64, 64/64, 4/4` |
| `gcc.c-torture/execute` | `pr92618.c` | 14 | `32/8, 32/8, 4/4, 16/16, 8/8, 16/16, 8/8, 16/16, 16/16, 8/8, 16/16, 16/16, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr94412.c` | 10 | `8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr94524-1.c` | 3 | `16/16, 16/16, 16/16` |
| `gcc.c-torture/execute` | `pr94524-2.c` | 5 | `16/16, 16/16, 16/16, 16/16, 16/16` |
| `gcc.c-torture/execute` | `scal-to-vec1.c` | 61 | `4/4, 4/4, 8/8, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4` |
| `gcc.c-torture/execute` | `scal-to-vec2.c` | 20 | `4/4, 8/8, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `scal-to-vec3.c` | 40 | `4/4, 8/8, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4, 16/16, 4/4` |
| `gcc.c-torture/execute` | `simd-4.c` | 5 | `8/8, 8/8, 8/8, 4/4, 8/8` |
| `gcc.c-torture/execute` | `simd-5.c` | 17 | `8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 4/4, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `simd-6.c` | 9 | `8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
