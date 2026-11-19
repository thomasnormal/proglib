# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic walls: `unsupported:no layout for declared type '_Complex double[12]'`, `unsupported:no layout for declared type '_Complex double[1]'`
- candidate files: **2**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `20020411-1.c` | 3 | `4/4, 8/4, 16/8` |
| `gcc.c-torture/execute` | `pr49644.c` | 6 | `192/8, 8/8, 16/8, 96/8, 8/8, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
