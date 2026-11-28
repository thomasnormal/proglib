# C admitted subset

Generated from `docs/c-survey.json` and `harness/c_cases.json`.

The pinned GNU17 target currently has 1426/2114 MATCH rows in the active survey denominator. Measurement commit `a2357ed50`, date `2026-11-27T12:12:00Z`.

A focused row is an admitted example when its harness expectation is `match`. A `refuse` row documents the exact refusal boundary. Corpus failures are listed as known wrong answers and remain separate from refusals.

## integers and conversions

- admitted: `forward-declaration-definition` (match): `int f(int); int f(int x) { return x; } int main(void) { return f(3) == 3 ? 0 : 1; }`
- refused: `signed-overflow` (refuse): `int main(void) { int x = 2147483647; x += 1; return x; }`
- known wrong: no scored failure in the current survey

## enums

- admitted: `structured-enum-object-layout` (match): `enum E { E0 = 0, E1 = 1 }; int main(void) { enum E e = E1; return e == E1 ? 0 : 1; }`
- refused: `corpus-pr91597-enum-global-init` (refuse) — pointer-integer value requires an unchanged cast back: `/* PR tree-optimization/91597 */ enum E { A, B, C }; struct __attribute__((aligned (4))) S { enum E e; }; enum E foo (struct S *o) { if (((__UINTPTR_TYPE__) ...`
- known wrong: no scored failure in the current survey

## control flow

- admitted: `defined-goto-pointer-increment-boundary` (match): `int main(void) { int a[2] = { 0, 7 }; int *p = a; goto next; next: ++p; return *p == 7 ? 0 : 1; }`
- refused: `order-binary-write-write` (refuse) — unsequenced side effects: `int main(void) { int i = 0; i++ + i++; return i; }`
- known wrong: no scored failure in the current survey

## arrays

- admitted: `vla-bound-expression-refusal` (match): `void f(int n) { double v[n]; for (int i = 0; i < n; ++i) v[i] = 0; } int main(void) { f(100); return 0; }`
- refused: `vla-bound-expression-node-refusal` (refuse) — parser-provided VLA bound expression: `int f(int n) { int v[n + 1]; v[0] = 1; return v[0]; } int main(void) { return f(2) == 1 ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## pointers

- admitted: `aggregate-pointer-provenance-copy` (match): `struct S { int *p; }; int main(void) { int x = 7; struct S a = {&x}; struct S b = a; return *b.p == 7 ? 0 : 1; }`
- refused: `lifetime-block-dangling` (refuse) — deadObject: `int main(void) { int *p; { int x = 5; p = &x; } return *p; }`
- known wrong: no scored failure in the current survey

## structs and layout forms

- admitted: `incomplete-record-before-complete` (match): `struct F; struct S { char c; int x; }; int main(void) { struct S s = {1, 2}; return s.x; }`
- refused: `long-double-object-layout-refusal` (refuse) — long double floating literal: `int main(void) { long double x = 1.5L; return x == 1.5L ? 0 : 1; }`
- known wrong: no scored failure in the current survey

## unions

- admitted: `union-nested-selected-member` (match): `struct S { _Bool flag; union { float a; double b; }; }; int main(void) { struct S y = { 1, { .a = 1.0 } }; return y.a == 1.0 ? 0 : 1; }`
- refused: `gcc/testsuite/gcc.dg/c23-tag-5.c` (refused-unsupported) — union initializer has no single selected member
- known wrong: no scored failure in the current survey

## bit-fields

- admitted: `bitfield-assignment-expression-converts` (match): `void abort(void); void exit(int); int main(void) { int j = 1081; struct { signed int m:11; } l; if ((l.m = j) == j) abort(); exit(0); }`
- refused: `bitfield-pr32244-1-c` (refuse) — arithmetic on bit-fields wider than int requires exact promotion semantics: `struct foo { unsigned long long b:40; } x; extern void abort (void); void test1(unsigned long long res) { /* The shift is carried out in 40 bit precision. */...`
- known wrong: no scored failure in the current survey

## casts between pointers and integers

- admitted: `pointer-integer-roundtrip` (match): `#include <stdint.h> int main(void) { int x = 3; uintptr_t u = (uintptr_t)&x; int *p = (int *)u; return *p == 3 ? 0 : 1; }`
- refused: `pointer-address-difference-wall` (refuse) — pointer-integer value requires an unchanged cast back: `#include <stdint.h> int main(void) { int x[2]; uintptr_t a = (uintptr_t)&x[0]; uintptr_t b = (uintptr_t)&x[1]; return (int)(b - a); }`
- known wrong: no scored failure in the current survey

## string functions

- admitted: `stdio-with-user-record-layout` (match) — 2
: `#include <stdio.h> struct S { char c; int x; }; int main(void) { struct S s = {1, 2}; printf("%d\n", s.x); return 0; }`
- refused: `00174.c` (refused-unsupported) — compound assignment lacks parser-native compute type observations
- known wrong: no scored failure in the current survey

## malloc/free

- admitted: `allocated-flexible-array-member-subscript` (match): `#include <stdlib.h> struct S { long head; int tail[]; }; int main(void) { struct S *s = malloc(sizeof(*s) + 2 * sizeof(int)); if (!s) return 2; s->tail[0] = ...`
- refused: `malloc-retype-int-to-long` (refuse) — effectiveType: `#include <stdlib.h> int main(void) { void *p = malloc(sizeof(long)); if (!p) return 2; *(int *)p = 7; *(long *)p = 4294967297L; int bad = *(long *)p != 42949...`
- known wrong: no scored failure in the current survey

## variadics

- admitted: `va-arg-signed-to-corresponding-unsigned` (match): `#include <stdarg.h> typedef unsigned long Result; static Result read(int fixed, ...) { va_list args; va_start(args, fixed); Result value = va_arg(args, Resul...`
- refused: `va-arg-distinct-equal-width-integers-refuse` (refuse) — va_arg incompatible argument type: `#include <stdarg.h> static long long read(int fixed, ...) { va_list args; va_start(args, fixed); long long value = va_arg(args, long long); va_end(args); ret...`
- known wrong: no scored failure in the current survey

## function pointers

- admitted: `type-function-pointer` (match): `int f(int x) { return x; } int main(void) { int (*p)(int) = f; return p(1); }`
- refused: `f2-pointer-bytes-character-defined` (refuse) — function pointer byte representation is unavailable: `#include <string.h> static void f(void) {} int main(void) { void (*p)(void) = f; unsigned char first = ((unsigned char *)&p)[0]; unsigned char copy[sizeof p]...`
- known wrong: no scored failure in the current survey

## floating point

- admitted: `builtin-islessgreater-ieee` (match): `double __builtin_nan(const char *); int main(void) { double n = __builtin_nan(""); return __builtin_islessgreater(1.0, 2.0) != 1 || __builtin_islessgreater(n...`
- refused: `long-double-floating-literal-refusal` (refuse) — long double floating literal: `int main(void) { return 1.5L == 1.5L ? 0 : 1; }`
- known wrong: no scored failure in the current survey
