# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic wall: `unsupported:no layout for declared type 'v16di'`
- candidate files: **2**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c-torture/execute` | `pr123625-2.c` | 9 | `128/128, 128/128, 128/128, 128/128, 4/4, 4/4, 128/128, 128/128, 128/128` |
| `gcc.c-torture/execute` | `pr126405-3.c` | 10 | `128/128, 128/128, 1024/1, 4/4, 128/128, 128/128, 128/128, 128/128, 4/4, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
