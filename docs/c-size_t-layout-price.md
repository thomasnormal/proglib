# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type 'size_t'`
- candidate files: **3**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `strcmp-1.c` | 17 | `4/4, 96/16, 96/16, 8/8, 8/8, 4/4, 4/4, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `strlen-1.c` | 7 | `4/4, 96/16, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `strncmp-1.c` | 18 | `4/4, 80/16, 80/16, 8/8, 8/8, 8/8, 4/4, 4/4, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
