# C admitted subset

Generated from `docs/c-survey.json` and `harness/c_cases.json`.

The pinned GNU17 target currently has 1385/2114 MATCH rows in the active survey denominator. Measurement commit `65ed9007ac5005542246773a4998f613103e8fdb`, date `2026-11-24T02:14:07Z`.

A focused row is an admitted example when its harness expectation is `match`. A `refuse` row documents the exact refusal boundary. Corpus failures are listed as known wrong answers and remain separate from refusals.

## integers and conversions

- admitted: `isprint-c-locale-ascii` (match): `int isprint(int); int main(void) { return isprint('a') && !isprint('\002') ? 0 : 1; }`
- refused: `signed-overflow` (refuse): `int main(void) { int x = 2147483647; x += 1; return x; }`
- known wrong: no scored failure in the current survey

## enums

- admitted: no focused harness row
- refused: `structured-enum-object-layout` (refuse) — no layout for declared type 'enum E': `enum E { E0 = 0, E1 = 1 }; int main(void) { enum E e = E1; return e == E1 ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## control flow

- admitted: `choose-expr` (match): `int main(void) { return __builtin_choose_expr(1, 7, 9); }`
- refused: `pointer-goto-increment-refusal` (refuse) — goto-controlled pointer increment: `int main(void) { char a[2] = {0, 0}; char *p = a; goto out; out: p++; return p == a + 1 ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## arrays

- admitted: `sizeof-unevaluated-array-and-scalar` (match): `int main(void) { int n = 0; char a[13]; return sizeof(a) == 13 && sizeof(++n) + n == sizeof(int) && n == 0 ? 0 : 1; }`
- refused: `vla-bound-expression-refusal` (refuse) — variable-length array: `void f(int n) { double v[n]; for (int i = 0; i < n; ++i) v[i] = 0; } int main(void) { f(100); return 0; }`
- known wrong: no scored failure in the current survey

## pointers

- admitted: `pointer-signed-unsigned-object-alias` (match): `int main(void) { unsigned long value = 1; return *(long *)&value == 1 ? 0 : 1; }`
- refused: `aggregate-pointer-provenance-copy` (refuse) — no layout for declared type 'struct S': `struct S { int *p; }; int main(void) { int x = 7; struct S a = {&x}; struct S b = a; return *b.p == 7 ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## structs and layout forms

- admitted: `record-forward-size` (match): `typedef struct s S; struct s { int a; int b; }; int main(void) { return sizeof(S); }`
- refused: `local-anonymous-record` (refuse) — no layout for field 'x': `int main(void) { struct { int x; int y; } s; s.x = 3; s.y = 5; return s.y - s.x - 2; }`
- known wrong: no scored failure in the current survey

## unions

- admitted: no focused harness row
- refused: `local-anonymous-union` (refuse) — no layout for field 'a': `int main(void) { union { int a; int b; } u; u.a = 1; u.b = 3; return (u.a == 3 && u.b == 3) ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## bit-fields

- admitted: `bitfield-20031211-1-c` (match) — no layout for declared type 'struct a': `void abort (void); void exit (int); struct a { unsigned int bitfield : 1; }; unsigned int x; int main(void) { struct a a = {0}; x = 0xbeef; a.bitfield |= x; ...`
- refused: `bitfield-assignment-expression-converts` (refuse) — no layout for declared type: `void abort(void); void exit(int); int main(void) { int j = 1081; struct { signed int m:11; } l; if ((l.m = j) == j) abort(); exit(0); }`
- known wrong: no scored failure in the current survey

## casts between pointers and integers

- admitted: `char-pointer-long-index` (match): `void abort(void); int main(void) { static char a[10] = "deadbeef"; long i = 2000000000L; return a[i - 2000000000L] == 'd' ? 0 : 1; }`
- refused: `pointer-integer-roundtrip` (refuse) — no layout for declared type 'int *': `#include <stdint.h> int main(void) { int x = 3; uintptr_t u = (uintptr_t)&x; int *p = (int *)u; return *p == 3 ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## string functions

- admitted: `builtin-snprintf-hhd` (match): `int main(void) { char b[5]; int n = __builtin_snprintf(b, sizeof b, "%hhd", 105); return n == 3 && b[0] == '1' && b[1] == '0' && b[2] == '5' && b[3] == 0 ? 0...`
- refused: `plain-string-index` (refuse) — no layout for declared type 'const char *': `int main(void) { const char *p = "hello"; return p[0] == 'h' ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## malloc/free

- admitted: `allocated-flexible-array-member-subscript` (match): `#include <stdlib.h> struct S { long head; int tail[]; }; int main(void) { struct S *s = malloc(sizeof(*s) + 2 * sizeof(int)); if (!s) return 2; s->tail[0] = ...`
- refused: no refusal row in the current inputs
- known wrong: no scored failure in the current survey

## variadics

- admitted: `va-arg-signed-to-corresponding-unsigned` (match): `#include <stdarg.h> typedef unsigned long Result; static Result read(int fixed, ...) { va_list args; va_start(args, fixed); Result value = va_arg(args, Resul...`
- refused: `va-arg-distinct-equal-width-integers-refuse` (refuse) — va_arg incompatible argument type: `#include <stdarg.h> static long long read(int fixed, ...) { va_list args; va_start(args, fixed); long long value = va_arg(args, long long); va_end(args); ret...`
- known wrong: no scored failure in the current survey

## function pointers

- admitted: `function-pointer-after-memset` (match): `#include <string.h> static void f(void) {} int main(void) { void (*p)(void) = f; memset(&p, 0, sizeof p); return p != 0; }`
- refused: `type-function-pointer` (refuse) — no layout for declared type 'int (*)(int)': `int f(int x) { return x; } int main(void) { int (*p)(int) = f; return p(1); }`
- known wrong: no scored failure in the current survey

## floating point

- admitted: `builtin-islessgreater-ieee` (match): `double __builtin_nan(const char *); int main(void) { double n = __builtin_nan(""); return __builtin_islessgreater(1.0, 2.0) != 1 || __builtin_islessgreater(n...`
- refused: `long-double-floating-literal-refusal` (refuse) — long double floating literal: `int main(void) { return 1.5L == 1.5L ? 0 : 1; }`
- known wrong: no scored failure in the current survey
