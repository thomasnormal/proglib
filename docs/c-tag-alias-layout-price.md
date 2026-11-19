# C parser-native layout price

- survey commit: `5fa6f5cf7`
- dynamic walls: `unsupported:no layout for declared type 'struct product_iSfd_'`, `unsupported:no layout for declared type 'typeof (*(1 ? &x `
- candidate files: **2**
- all rows joined: **True**

| corpus | file | TypeLayout records | sizes / alignments |
| --- | --- | ---: | --- |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/c23-tag-5.c` | 8 | `24/8, 24/8, 24/8, 8/8, 4/4, 8/8, 4/4, 24/8` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/c23-tag-alias-7.c` | 6 | `4/4, 8/8, 8/8, 4/4, 8/8, 4/4` |

The selected files are the survey's sole dynamic layout wall. Every candidate has parser-native TypeLayout observations from the pinned Clang probe. The report prices the layout boundary only and claims no semantics or corpus flip.
