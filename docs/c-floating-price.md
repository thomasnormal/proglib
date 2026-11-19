# C floating-literal frontend price

- survey commit: `5fa6f5cf7`
- survey measured at: `2026-11-18T22:15:35Z`
- sole dynamic wall: `unsupported:long double floating literal`
- candidate files: **10**
- all parser-native records joined: **True**
- bit widths present: `{32: 3, 64: 7, 80: 10}`
- types present: `{'double': 7, 'float': 3, 'long double': 10}`

| corpus | file | literals | widths | types | static walls |
| --- | --- | ---: | --- | --- | --- |
| `gcc.c-torture/execute` | `20030914-1.c` | 2 | `[80]` | `['long double']` | `cast:IntegralToFloating, type-layout` |
| `gcc.c-torture/execute` | `20080502-1.c` | 4 | `[64, 80]` | `['double', 'long double']` | `cast:FloatingCast, libc-call: __builtin_signbit, type-layout` |
| `gcc.c23-run` | `gcc/testsuite/gcc.dg/c23-float-1.c` | 6 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `type-layout` |
| `gcc.c-torture/execute` | `ieee/20010226-1.c` | 5 | `[80]` | `['long double']` | `cast:FloatingToIntegral, type-layout` |
| `gcc.c-torture/execute` | `ieee/inf-2.c` | 3 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `libc-call: __builtin_inf, libc-call: __builtin_inff, libc-call: __builtin_infl, type-layout` |
| `gcc.c-torture/execute` | `ieee/inf-3.c` | 3 | `[32, 64, 80]` | `['double', 'float', 'long double']` | `libc-call: __builtin_huge_val, libc-call: __builtin_huge_valf, libc-call: __builtin_huge_vall, type-layout` |
| `gcc.c-torture/execute` | `ieee/pr36332.c` | 1 | `[80]` | `['long double']` | `libc-call: __builtin_abort, libc-call: __builtin_infl, type-layout` |
| `gcc.c-torture/execute` | `pr44942.c` | 31 | `[64, 80]` | `['double', 'long double']` | `libc-call: __builtin_abort, libc-call: __builtin_c23_va_start, libc-call: __builtin_va_end, type-layout` |
| `gcc.c-torture/execute` | `va-arg-5.c` | 16 | `[64, 80]` | `['double', 'long double']` | `libc-call: __builtin_c23_va_start, libc-call: __builtin_va_end, type-layout` |
| `gcc.c-torture/execute` | `va-arg-6.c` | 4 | `[64, 80]` | `['double', 'long double']` | `libc-call: __builtin_c23_va_start, libc-call: __builtin_va_end, type-layout` |

The candidate files are the survey's sole dynamic long-double floating-literal wall. Every FloatingLiteral observed in their approved Clang envelopes joined to a parser-native rounded bit pattern. This prices the frontend/value boundary only; no floating semantics or flip is claimed.
