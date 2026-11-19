# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type 'V'`
- candidate files: **9**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `pr105613.c` | 6 | `16/16, 8/8, 16/16, 16/16, 16/16, 16/16` |
| `gcc.c-torture/execute` | `pr110817-1.c` | 3 | `8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr110817-2.c` | 3 | `8/8, 1/1, 8/8` |
| `gcc.c-torture/execute` | `pr110817-3.c` | 4 | `4/4, 1/1, 4/4, 4/4` |
| `gcc.c-torture/execute` | `pr71626-1.c` | 2 | `8/8, 8/8` |
| `gcc.c-torture/execute` | `pr85169.c` | 5 | `8/8, 64/64, 64/64, 64/64, 4/4` |
| `gcc.c-torture/execute` | `pr94412.c` | 10 | `8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8, 8/8` |
| `gcc.c-torture/execute` | `pr94524-1.c` | 3 | `16/16, 16/16, 16/16` |
| `gcc.c-torture/execute` | `pr94524-2.c` | 5 | `16/16, 16/16, 16/16, 16/16, 16/16` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
