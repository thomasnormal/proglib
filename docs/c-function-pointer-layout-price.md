# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic walls: `unsupported:no layout for declared type 'double (*)(float)'`, `unsupported:no layout for declared type 'int (*(*)(int, int))(int, int)'`, `unsupported:no layout for declared type 'int (*)(int, int)'`, `unsupported:no layout for parameter type 'double (*)(double)'`, `unsupported:no layout for parameter type 'double (*)(int, ...)'`, `unsupported:no layout for parameter type 'int (*)(int)'`, `unsupported:no layout for parameter type 'int **restrict'`, `unsupported:no layout for parameter type 'int *restrict'`, `unsupported:no layout for parameter type 'void (*)(double)'`, `unsupported:no size for pointee of 'const char (*)[1]'`, `unsupported:no size for pointee of 'int (*)[4]'`, `unsupported:sizeof: no layout for operand type 'int (*volatile[6])(void)'`
- candidate files: **12**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `c-testsuite/single-exec` | `00124.c` | 11 | `4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 8/8, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `20021118-2.c` | 22 | `4/4, 8/8, 4/4, 8/8, 8/8, 8/8, 4/4, 4/4, 8/8, 4/4, 8/8, 8/8, 8/8, 4/4, 4/4, 8/8, 4/4, 8/8, 4/4, 4/4, 4/4, 12/4` |
| `gcc.c-torture/execute` | `20080506-2.c` | 5 | `8/8, 8/8, 4/4, 8/8, 8/8` |
| `gcc.c-torture/execute` | `921208-1.c` | 5 | `4/4, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `991112-1.c` | 7 | `4/4, 4/4, 4/4, 4/4, 8/8, 4/4, 4/4` |
| `gcc.c-torture/execute` | `bcp-1.c` | 16 | `4/4, 4/4, 4/4, 4/4, 8/8, 4/4, 10/1, 8/8, 48/8, 24/8, 4/4, 16/8, 8/8, 24/8, 24/8, 4/4` |
| `gcc.c-torture/execute` | `func-ptr-1.c` | 5 | `4/4, 4/4, 8/8, 4/4, 4/4` |
| `gcc.c-torture/execute` | `memchr-1.c` | 18 | `8/8, 4/4, 8/8, 1/1, 1/1, 4/1, 8/1, 15/1, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr124358.c` | 6 | `4/4, 4/4, 16/4, 8/8, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr38212.c` | 7 | `8/8, 4/4, 8/8, 8/8, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr42231.c` | 8 | `4/4, 4/4, 8/8, 4/4, 4/4, 8/8, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr68390.c` | 7 | `4/4, 8/8, 4/4, 4/4, 8/8, 8/8, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
