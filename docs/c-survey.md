# C torture survey

Generated from the pinned `gcc.c-torture/execute` manifest.

- verdicts: 1240/2117 MATCH (passed 1240, failed 4, oracle 0)
- excluded from denominator: no-entry-point 97
- manifest SHA-256: `f8c35baf66f6b9e46a62c5635c3b66aa0b4016033be8be68fa9f858fd47c8c91`
- measured commit: `929600ebd`
- measured at: `2026-11-19 05:34:27 UTC`

## Verdict counts

| verdict | files |
| --- | ---: |
| `failed` | 4 |
| `no-entry-point` | 97 |
| `not-parsed` | 567 |
| `oracle-tests-compiler` | 1 |
| `passed` | 1240 |
| `refused-libc` | 18 |
| `refused-ub` | 91 |
| `refused-unsupported` | 285 |
| `timeout` | 8 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `not-parsed` | 10 |
| `c-testsuite/single-exec` | `passed` | 187 |
| `c-testsuite/single-exec` | `refused-ub` | 4 |
| `c-testsuite/single-exec` | `refused-unsupported` | 18 |
| `c-testsuite/single-exec` | `timeout` | 1 |
| `gcc.c-torture/execute` | `failed` | 4 |
| `gcc.c-torture/execute` | `not-parsed` | 520 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 1 |
| `gcc.c-torture/execute` | `passed` | 1044 |
| `gcc.c-torture/execute` | `refused-libc` | 17 |
| `gcc.c-torture/execute` | `refused-ub` | 86 |
| `gcc.c-torture/execute` | `refused-unsupported` | 155 |
| `gcc.c-torture/execute` | `timeout` | 7 |
| `gcc.c23-run` | `not-parsed` | 37 |
| `gcc.c23-run` | `passed` | 9 |
| `gcc.c23-run` | `refused-libc` | 1 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 15 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 339 | 897 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call: __builtin_abort` | 140 | 322 | 20080719-1.c, 20081103-1.c, 20081218-1.c, 20110418-1.c, 20121108-1.c |
| `cast:IntegralToPointer` | 3 | 25 | 00214.c, 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsequenced-effects` | 3 | 13 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `libc-call` | 3 | 12 | 00087.c, 00089.c, 00159.c, 00216.c, 00219.c |
| `cast:PointerToIntegral` | 2 | 24 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `libc-call: malloc` | 2 | 12 | 20020406-1.c, 20051113-1.c, 920810-1.c, 941014-2.c, 960521-1.c |
| `libc-call: __builtin_return_address` | 2 | 4 | 20010122-1.c, 20030323-1.c, 20030811-1.c, pr17377.c |
| `libc-call: memset` | 1 | 22 | 00179.c, 20001203-2.c, 20031012-1.c, 20040823-1.c, 20050826-1.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `libc-call: __builtin_alloca` | 1 | 8 | 20021113-1.c, 20070824-1.c, alloca-1.c, built-in-setjmp.c, frame-address.c |
| `libc-call: __builtin_malloc` | 1 | 7 | 20071018-1.c, 20071120-1.c, pr15262-1.c, pr36765.c, pr43008.c |
| `unsupported:AddrLabelExpr` | 1 | 7 | 20040302-1.c, 20071210-1.c, 920501-4.c, 920501-5.c, 980526-1.c |
| `libc-call: link_error` | 1 | 6 | 20030330-1.c, builtins/abs-2.c, builtins/memcmp.c, builtins/uabs-2.c, ieee/fp-cmp-7.c |
| `libc-call: __builtin_ffs` | 1 | 4 | ffs-1.c, ffs-2.c, pr61725.c, pr97325.c |
| `libc-call: __builtin_constant_p` | 1 | 3 | 20030330-1.c, builtin-constant.c, pr19449.c |
| `libc-call: calloc` | 1 | 3 | 00040.c, 20020406-1.c, ipa-sra-2.c |
| `libc-call: __builtin_abs` | 1 | 2 | pr34130.c, pr42614.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `string-literal` | 0 | 218 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `libc-call: printf` | 0 | 65 | 00056.c, 00125.c, 00131.c, 00132.c, 00154.c |
| `cast:IntegralToFloating` | 0 | 64 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `cast:FloatingCast` | 0 | 37 | 00174.c, 00175.c, 20000605-1.c, 20020413-1.c, 20030125-1.c |
| `libc-call: __builtin_memcpy` | 0 | 25 | 20000703-1.c, 20011121-1.c, 20030408-1.c, 20040411-1.c, 20060930-2.c |
| `libc-call: __builtin_memset` | 0 | 25 | 20020619-1.c, 20030606-1.c, 20030717-1.c, 20041218-1.c, 20071108-1.c |
| `unsupported:PackedAttr` | 0 | 23 | 20010518-2.c, 20030224-2.c, 20040625-1.c, 20051113-1.c, 20100430-1.c |
| `libc-call: memcmp` | 0 | 22 | 00179.c, 20050502-2.c, 20050826-1.c, builtins/memcmp.c, builtins/memmove-2.c |
| `cast:FloatingToIntegral` | 0 | 20 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040831-1.c |
| `libc-call: strcpy` | 0 | 17 | 00179.c, 00180.c, 20031204-1.c, 20120207-1.c, 980707-1.c |
| `libc-call: memcpy` | 0 | 14 | 00179.c, 20010925-1.c, 20011024-1.c, 20011113-1.c, 20050826-1.c |
| `libc-call: strcmp` | 0 | 14 | 00179.c, 20001011-1.c, 20011024-1.c, 20030715-1.c, 20050502-1.c |
| `libc-call: strlen` | 0 | 14 | 00025.c, 00179.c, 20010409-1.c, 20011024-1.c, 20050218-1.c |
| `libc-call: __builtin_memcmp` | 0 | 13 | 20081103-1.c, ieee/mzero2.c, ieee/mzero3.c, ieee/mzero5.c, pr108498-2.c |
| `unsupported:AlignedAttr` | 0 | 13 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `libc-call: __builtin_strlen` | 0 | 11 | 20030221-1.c, 20031012-1.c, builtins/strlen.c, pr110914.c, pr116799.c |
| `libc-call: __builtin_printf` | 0 | 10 | 20020406-1.c, 20121108-1.c, 20141022-1.c, memchr-1.c, pr111863-1.c |
| `libc-call: __builtin_mul_overflow` | 0 | 9 | pr108789.c, pr64006.c, pr68381.c, pr71554.c, pr84169.c |
| `libc-call: __builtin_strcmp` | 0 | 9 | 20010915-1.c, 20021011-1.c, 921006-1.c, 921007-1.c, 921117-1.c |
| `libc-call: __builtin_inf` | 0 | 6 | ieee/compare-fp-1.c, ieee/compare-fp-4.c, ieee/fp-cmp-7.c, ieee/inf-1.c, ieee/inf-2.c |
| `libc-call: __builtin_prefetch` | 0 | 6 | builtin-prefetch-1.c, builtin-prefetch-2.c, builtin-prefetch-3.c, builtin-prefetch-4.c, builtin-prefetch-5.c |
| `libc-call: __builtin_strcpy` | 0 | 6 | 20021011-1.c, 921117-1.c, builtins/strcpy.c, pr84339.c, strcpy-2.c |
| `libc-call: abs` | 0 | 6 | 20041126-1.c, builtins/abs-1.c, builtins/abs-2.c, pr33142.c, ssad-run.c |
| `libc-call: strncmp` | 0 | 6 | 00179.c, 20050218-1.c, builtins/strncmp-2.c, builtins/strncmp.c, builtins/strstr-asm-lib.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:IndirectGotoStmt` | 0 | 6 | 20040302-1.c, 20071210-1.c, 920501-4.c, 920501-5.c, 980526-1.c |
| `libc-call: __builtin_add_overflow` | 0 | 5 | pr108789.c, pr85095.c, pr90311.c, pr91635.c, pr93494.c |
| `libc-call: __builtin_expect` | 0 | 5 | 00214.c, 20020418-1.c, ieee/unsafe-fp-assoc-1.c, pr115277.c, pr91597.c |
| `libc-call: __builtin_inff` | 0 | 5 | gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c, ieee/inf-1.c, ieee/inf-2.c, ieee/pr109386.c |
| `libc-call: strchr` | 0 | 5 | 00179.c, 20000910-2.c, builtins/strchr.c, builtins/strstr-asm-lib.c, string-opt-5.c |
| `unsupported:IndirectFieldDecl` | 0 | 5 | 00046.c, 00050.c, 00216.c, anon-1.c, pr87053.c |
| `libc-call: __builtin_isunordered` | 0 | 4 | ieee/compare-fp-1.c, ieee/compare-fp-3.c, ieee/compare-fp-4.c, ieee/fp-cmp-5.c |
| `libc-call: __builtin_longjmp` | 0 | 4 | built-in-setjmp.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: __builtin_nanf` | 0 | 4 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c, ieee/pr109386.c, ieee/pr119002.c |
| `libc-call: __builtin_setjmp` | 0 | 4 | built-in-setjmp.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: sprintf` | 0 | 4 | 00186.c, 960327-1.c, 980605-1.c, struct-ret-1.c |
| `unsupported:OffsetOfExpr` | 0 | 4 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr103255.c, pr30778.c, pr44468.c |
| `libc-call: __builtin_huge_val` | 0 | 3 | ieee/hugeval.c, ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_infl` | 0 | 3 | ieee/inf-1.c, ieee/inf-2.c, ieee/pr36332.c |
| `libc-call: __builtin_nan` | 0 | 3 | ieee/builtin-nan-1.c, ieee/compare-fp-1.c, ieee/compare-fp-4.c |
| `libc-call: __builtin_sprintf` | 0 | 3 | 20021120-3.c, pr78586.c, pr79327.c |
| `libc-call: __builtin_unreachable` | 0 | 3 | 20230509-1.c, pr81281.c, pr97888-1.c |
| `libc-call: bcopy` | 0 | 3 | builtins/memmove-2.c, builtins/memmove.c, builtins/memops-asm.c |
| `libc-call: memmove` | 0 | 3 | builtins/memmove-2.c, builtins/memmove.c, string-opt-18.c |
| `libc-call: mempcpy` | 0 | 3 | builtins/mempcpy-2.c, builtins/mempcpy.c, string-opt-18.c |
| `libc-call: strncpy` | 0 | 3 | 00179.c, builtins/strncpy.c, string-opt-5.c |
| `libc-call: strrchr` | 0 | 3 | 00179.c, builtins/strrchr.c, string-opt-5.c |
| `unsupported:ExprWithCleanups` | 0 | 3 | 20020320-1.c, 950628-1.c, pr30185.c |
| `unsupported:GCCAsmStmt` | 0 | 3 | 20071211-1.c, 990413-2.c, pr81588.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `libc-call: __builtin_copysign` | 0 | 2 | ieee/mzero6.c, pr44683.c |
| `libc-call: __builtin_fabs` | 0 | 2 | ieee/20010114-2.c, ieee/20030331-1.c |
| `libc-call: __builtin_huge_valf` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_huge_vall` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_islessgreater` | 0 | 2 | ieee/compare-fp-1.c, ieee/fp-cmp-5.c |
| `libc-call: __builtin_isnan` | 0 | 2 | gcc/testsuite/gcc.dg/c23-float-4.c, ieee/inf-4.c |
| `libc-call: __builtin_memmove` | 0 | 2 | builtins/memmove.c, pr93213.c |
| `libc-call: __builtin_mempcpy` | 0 | 2 | builtins/mempcpy-2.c, builtins/mempcpy.c |
| `libc-call: __builtin_signbit` | 0 | 2 | 20080502-1.c, pr35456.c |
| `libc-call: __builtin_stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: __builtin_strncpy` | 0 | 2 | builtins/strncpy.c, pr93249.c |
| `libc-call: __builtin_strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: __builtin_trap` | 0 | 2 | 20020418-1.c, pr125291.c |
| `libc-call: f` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: floor` | 0 | 2 | 990826-0.c, float-floor.c |
| `libc-call: fprintf` | 0 | 2 | fprintf-1.c, gofast.c |
| `libc-call: free` | 0 | 2 | ipa-sra-2.c, pr42614.c |
| `libc-call: g` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: labs` | 0 | 2 | builtins/abs-1.c, builtins/abs-2.c |
| `libc-call: memchr` | 0 | 2 | builtins/memchr.c, memchr-1.c |
| `libc-call: mmap` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: open` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: sin` | 0 | 2 | 00174.c, ieee/mzero4.c |
| `libc-call: stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: strcat` | 0 | 2 | 00179.c, builtins/strcat.c |
| `libc-call: strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: uabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `libc-call: ulabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `libc-call: __assert_fail` | 0 | 1 | pr58831.c |
| `libc-call: __builtin_bcopy` | 0 | 1 | builtins/memmove.c |
| `libc-call: __builtin_bswap16` | 0 | 1 | pr97386-1.c |
| `libc-call: __builtin_bswap32` | 0 | 1 | bswap-3.c |
| `libc-call: __builtin_bswap64` | 0 | 1 | bswap-1.c |
| `libc-call: __builtin_bzero` | 0 | 1 | builtins/memops-asm.c |
| `libc-call: __builtin_clz` | 0 | 1 | pr37780.c |
| `libc-call: __builtin_copysignf` | 0 | 1 | ieee/pr72824.c |
| `libc-call: __builtin_ctz` | 0 | 1 | pr37780.c |
| `libc-call: __builtin_fabsf` | 0 | 1 | ieee/pr109386.c |
| `libc-call: __builtin_frame_address` | 0 | 1 | frame-address.c |
| `libc-call: __builtin_free` | 0 | 1 | pr84339.c |
| `libc-call: __builtin_index` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_isfinite` | 0 | 1 | ieee/inf-4.c |
| `libc-call: __builtin_isgreater` | 0 | 1 | ieee/fp-cmp-5.c |
| `libc-call: __builtin_isgreaterequal` | 0 | 1 | ieee/fp-cmp-5.c |
| `libc-call: __builtin_isinf` | 0 | 1 | ieee/pr109386.c |
| `libc-call: __builtin_isless` | 0 | 1 | ieee/fp-cmp-5.c |
| `libc-call: __builtin_islessequal` | 0 | 1 | ieee/fp-cmp-5.c |
| `libc-call: __builtin_memchr` | 0 | 1 | builtins/memchr.c |
| `libc-call: __builtin_rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_snprintf` | 0 | 1 | pr78622.c |
| `libc-call: __builtin_strcat` | 0 | 1 | builtins/strcat.c |
| `libc-call: __builtin_strchr` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: __builtin_strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: __builtin_strncmp` | 0 | 1 | builtins/strncmp.c |
| `libc-call: __builtin_strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: __builtin_strrchr` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: __sync_add_and_fetch_8` | 0 | 1 | pr122000.c |
| `libc-call: alloca` | 0 | 1 | 20010122-1.c |
| `libc-call: atan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atoi` | 0 | 1 | 20221006-1.c |
| `libc-call: compare1` | 0 | 1 | pr34456.c |
| `libc-call: fabs` | 0 | 1 | 20020720-1.c |
| `libc-call: fetestexcept` | 0 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `libc-call: h1` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h2` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h3` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h4` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h5` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h6` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h7` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: imaxabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: index` | 0 | 1 | builtins/strchr.c |
| `libc-call: isprint` | 0 | 1 | 991112-1.c |
| `libc-call: llabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: p` | 0 | 1 | 00216.c |
| `libc-call: pow` | 0 | 1 | 980709-1.c |
| `libc-call: qsort` | 0 | 1 | pr34456.c |
| `libc-call: rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: sinf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: sqrt` | 0 | 1 | ieee/20041213-1.c |
| `libc-call: strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: tan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: tanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: terminate_me` | 0 | 1 | pr54937.c |
| `libc-call: ullabs` | 0 | 1 | builtins/uabs-2.c |
| `libc-call: umaxabs` | 0 | 1 | builtins/uabs-2.c |
| `libc-call: x` | 0 | 1 | 991112-1.c |
| `unsupported:BinaryConditionalOperator` | 0 | 1 | pr68249.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 567 | 567 | 00104.c, 00124.c, 00162.c, 00170.c, 00187.c |
| `undefined-behavior` | 91 | 91 | 00032.c, 00141.c, 00144.c, 00200.c, 20000113-1.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 25 | 25 | builtins/20010124-1-lib.c, builtins/lib/abs.c, builtins/lib/stpcpy.c, builtins/lib/strcat.c, builtins/lib/strchr.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 21 | 21 | 00103.c, 20001017-2.c, 20060412-1.c, 980617-1.c, 991228-1.c |
| `unsupported:integer-to-pointer conversion is not an unchanged uintptr_t/intptr_t round-trip` | 12 | 12 | 00214.c, 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c |
| `unsupported:long double floating literal` | 10 | 10 | 20030914-1.c, 20040208-1.c, 20080502-1.c, 960405-1.c, gcc/testsuite/gcc.dg/c23-float-1.c |
| `timeout` | 8 | 8 | 00040.c, 20011008-3.c, 960521-1.c, memcpy-1.c, memcpy-2.c |
| `unsupported:StmtExpr` | 7 | 7 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c |
| `unsupported:AddrLabelExpr` | 6 | 6 | 20040302-1.c, 20071210-1.c, 920501-4.c, 920501-5.c, 990208-1.c |
| `unsupported:aggregate used as a pointer` | 5 | 5 | 00218.c, 20011113-1.c, 20020406-1.c, 20090113-2.c, 20090113-3.c |
| `unsupported:pointer-integer value requires an unchanged cast back` | 5 | 5 | 20050215-1.c, 941014-2.c, pr38051.c, pr58209.c, pr97421-3.c |
| `unsupported:pointer-to-integer conversion outside uintptr_t/intptr_t` | 5 | 5 | 20011121-1.c, 980526-2.c, loop-2c.c, pr17133.c, pr23467.c |
| `unsupported:break, continue or goto escaped a function body` | 4 | 4 | 00199.c, 00207.c, 00213.c, 20040704-1.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `unsupported:floating cast has incompatible source and destination` | 4 | 4 | 20020413-1.c, 990413-2.c, align-2.c, ieee/20011123-1.c |
| `unsupported:type trait '__alignof'` | 4 | 4 | 20000223-1.c, align-3.c, alloca-1.c, zerolen-2.c |
| `libc-call: __builtin_setjmp` | 3 | 3 | built-in-setjmp.c, pr64242.c, pr84521.c |
| `unsupported:OffsetOfExpr` | 3 | 3 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr30778.c, pr44468.c |
| `unsupported:case label nested in a control statement` | 3 | 3 | 00051.c, 00143.c, medce-1.c |
| `unsupported:long double integer-to-floating conversion` | 3 | 3 | 930622-2.c, 960215-1.c, regstack-1.c |
| `unsupported:printf` | 3 | 3 | 00174.c, 00175.c, 00195.c |
| `libc-call: exit (an argument is not a literal 0 — which exit was reached is unknown)` | 2 | 2 | 970217-1.c, loop-8.c |
| `libc-call: open` | 2 | 2 | loop-2f.c, loop-2g.c |
| `unsupported:ExprWithCleanups` | 2 | 2 | 950628-1.c, pr30185.c |
| `unsupported:GCCAsmStmt` | 2 | 2 | 20071211-1.c, pr81588.c |
| `unsupported:GenericSelectionExpr` | 2 | 2 | gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-float-2.c |
| `unsupported:call to '__builtin_nanf' in a context with no program — call it through 'callByName'` | 2 | 2 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:floating value used as an integer` | 2 | 2 | 20000731-1.c, 20011217-1.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:non-object declaration in a block` | 2 | 2 | 00078.c, struct-cpy-1.c |
| `unsupported:operator '-' on pointers without array provenance` | 2 | 2 | 980701-1.c, pr36321.c |
| `unsupported:parameter array-bound effects are not retained by clang` | 2 | 2 | 921113-1.c, pr77767.c |
| `unsupported:subscript base is not an array or pointer type` | 2 | 2 | 20080519-1.c, strlen-4.c |
| `unsupported:unknown enum declaration 'id65' (name 'B')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-tag-alias-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-2.c |
| `cast:FloatingRealToComplex` | 1 | 1 | complex-4.c |
| `libc-call: __builtin_constant_p` | 1 | 1 | builtin-constant.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: __builtin_islessgreater` | 1 | 1 | ieee/compare-fp-1.c |
| `libc-call: __builtin_return_address` | 1 | 1 | pr17377.c |
| `libc-call: __builtin_snprintf` | 1 | 1 | pr78622.c |
| `libc-call: f` | 1 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: isprint` | 1 | 1 | 991112-1.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: pow` | 1 | 1 | 980709-1.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `libc-call: sin` | 1 | 1 | ieee/mzero4.c |
| `unsequenced-effects` | 1 | 1 | string-opt-5.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:TypeTraitExpr` | 1 | 1 | builtin-types-compatible-p.c |
| `unsupported:__builtin_infl` | 1 | 1 | ieee/inf-1.c |
| `unsupported:aggregate used as truth value` | 1 | 1 | pr39100.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 1 | 1 | call-trap-1.c |
| `unsupported:call to '__builtin_inff' in a context with no program — call it through 'callByName'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:call to '__builtin_nan' in a context with no program — call it through 'callByName'` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:cannot initialize aggregate 'int'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
| `unsupported:cannot initialize aggregate 'u8'` | 1 | 1 | 00216.c |
| `unsupported:cannot initialize aggregate 'void *(*[6])(void)'` | 1 | 1 | 20010122-1.c |
| `unsupported:explicit initializer for flexible array member 'a3p'` | 1 | 1 | 20010924-1.c |
| `unsupported:explicit initializer for flexible array member 'j'` | 1 | 1 | pr33382.c |
| `unsupported:explicit initializer for flexible array member 'z'` | 1 | 1 | 20030109-1.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:function pointer used as an object pointer` | 1 | 1 | 941014-1.c |
| `unsupported:function-to-pointer decay of an unresolved function` | 1 | 1 | 00219.c |
| `unsupported:no size for element type 'unsigned32'` | 1 | 1 | cbrt.c |
| `unsupported:no size for pointee of 'const char (*)[1]'` | 1 | 1 | memchr-1.c |
| `unsupported:no size for pointee of 'void *'` | 1 | 1 | pr48571-1.c |
| `unsupported:not an integer type: 'size_t'` | 1 | 1 | pr34456.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:operator '-' on pointers from different arrays` | 1 | 1 | 950710-1.c |
| `unsupported:operator operands have unsupported value kinds (C23 6.5)` | 1 | 1 | 20041212-1.c |
| `unsupported:sizeof: no layout for operand type 'c'` | 1 | 1 | 20040411-1.c |
| `unsupported:sprintf` | 1 | 1 | struct-ret-1.c |
| `unsupported:src/930628-1.c` | 1 | 1 | 930628-1.c |
| `unsupported:strcpy` | 1 | 1 | string-opt-18.c |
| `unsupported:union initializer has no member` | 1 | 1 | pr87053.c |
| `unsupported:unknown enum declaration 'id18' (name 'C')` | 1 | 1 | pr91597.c |
| `unsupported:unknown enum declaration 'id543' (name 'e')` | 1 | 1 | 00198.c |
| `unsupported:unnamed pointer parameter (array-bound effects are not retained by clang)` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
| `unsupported:unsupported bit-field width 53 for 'long long'` | 1 | 1 | 991118-1.c |
