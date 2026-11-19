# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type 'int[n % 1000 + 1]'`
- candidate files: **3**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `20040811-1.c` | 3 | `8/8, 4/4, 0/4` |
| `gcc.c-torture/execute` | `pr43220.c` | 4 | `8/8, 4/4, 0/4, 0/4` |
| `gcc.c-torture/execute` | `vla-dealloc-1.c` | 3 | `8/8, 4/4, 0/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
