# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type '_Complex double'`
- candidate files: **5**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `20030910-1.c` | 3 | `4/4, 16/8, 8/8` |
| `gcc.c-torture/execute` | `960512-1.c` | 4 | `4/4, 160/4, 16/8, 16/8` |
| `gcc.c-torture/execute` | `complex-1.c` | 7 | `4/4, 8/8, 8/8, 8/8, 16/8, 8/8, 16/8` |
| `gcc.c-torture/execute` | `complex-2.c` | 8 | `4/4, 16/8, 16/8, 16/8, 16/8, 16/8, 16/8, 16/8` |
| `gcc.c-torture/execute` | `ieee/cdivchkd.c` | 30 | `4/4, 8/8, 16/8, 16/8, 16/8, 16/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 4/4, 4/4, 8/8, 16/8, 16/8, 16/8, 16/8, 32/8, 32/8, 32/8, 32/8, 32/8, 32/8, 8/8, 8/8, 4/4, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
