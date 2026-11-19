# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type 'jmp_buf'`
- candidate files: **2**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `20210505-1.c` | 3 | `200/8, 1/1, 8/8` |
| `gcc.c-torture/execute` | `pr56982.c` | 9 | `4/4, 200/8, 4/4, 8/8, 4/4, 4/4, 4/4, 8/8, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
