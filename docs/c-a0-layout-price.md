# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic walls: `unsupported:no layout for declared type 'A0'`
- candidate files: **1**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `va-arg-22.c` | 51 | `4/4, 4/4, 4/4, 4/4, 4/4, 4/4, 0/1, 1/1, 2/1, 3/1, 4/1, 5/1, 6/1, 7/1, 8/1, 9/1, 10/1, 11/1, 12/1, 13/1, 14/1, 15/1, 16/1, 31/1, 32/1, 35/1, 72/1, 24/8, 4/4, 0/1, 1/1, 2/1, 3/1, 4/1, 5/1, 6/1, 7/1, 8/1, 9/1, 10/1, 11/1, 12/1, 13/1, 14/1, 15/1, 16/1, 31/1, 32/1, 35/1, 72/1, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
