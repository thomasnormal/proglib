# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type '_Complex float'`
- candidate files: **3**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `complex-6.c` | 21 | `4/4, 8/4, 8/4, 8/4, 8/4, 16/8, 16/8, 16/8, 16/8, 32/16, 32/16, 32/16, 32/16, 8/4, 8/4, 8/4, 8/4, 16/8, 16/8, 16/8, 16/8` |
| `gcc.c-torture/execute` | `ieee/cdivchkf.c` | 30 | `4/4, 8/8, 8/4, 8/4, 8/4, 8/4, 4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 8/8, 4/4, 4/4, 8/8, 8/4, 8/4, 8/4, 8/4, 16/4, 16/4, 16/4, 16/4, 16/4, 16/4, 4/4, 4/4, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr38969.c` | 4 | `8/4, 8/4, 8/4, 8/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
