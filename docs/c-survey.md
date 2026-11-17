# C torture survey

Generated from the pinned `C1-C3 (gcc torture, c-testsuite, gcc c23-run)` manifest.

- verdicts: 1210/2112 MATCH (passed 1210, failed 3, oracle 0)
- excluded from denominator: no-entry-point 102
- manifest SHA-256: `3e6f6add513d9e002704d81e95c042c0d97b48506e37ce6c58c2666f464ab4e4`
- measured commit: `333e9c076`
- measured at: `2026-11-17T03:03:54Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `failed` | 3 |
| `no-entry-point` | 102 |
| `not-parsed` | 350 |
| `oracle-tests-compiler` | 1 |
| `passed` | 1210 |
| `refused-libc` | 21 |
| `refused-ub` | 86 |
| `refused-unsupported` | 354 |
| `timeout` | 87 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `not-parsed` | 1 |
| `c-testsuite/single-exec` | `passed` | 185 |
| `c-testsuite/single-exec` | `refused-libc` | 1 |
| `c-testsuite/single-exec` | `refused-ub` | 4 |
| `c-testsuite/single-exec` | `refused-unsupported` | 26 |
| `c-testsuite/single-exec` | `timeout` | 3 |
| `gcc.c-torture/execute` | `failed` | 3 |
| `gcc.c-torture/execute` | `not-parsed` | 321 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 1 |
| `gcc.c-torture/execute` | `passed` | 1017 |
| `gcc.c-torture/execute` | `refused-libc` | 18 |
| `gcc.c-torture/execute` | `refused-ub` | 78 |
| `gcc.c-torture/execute` | `refused-unsupported` | 307 |
| `gcc.c-torture/execute` | `timeout` | 84 |
| `gcc.c23-run` | `not-parsed` | 28 |
| `gcc.c23-run` | `passed` | 8 |
| `gcc.c23-run` | `refused-libc` | 2 |
| `gcc.c23-run` | `refused-ub` | 4 |
| `gcc.c23-run` | `refused-unsupported` | 21 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 356 | 1035 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `libc-call: __builtin_abort` | 158 | 377 | 20080719-1.c, 20081103-1.c, 20081218-1.c, 20110418-1.c, 20121108-1.c |
| `libc-call` | 4 | 18 | 00087.c, 00089.c, 00124.c, 00159.c, 00189.c |
| `cast:IntegralToPointer` | 3 | 26 | 00214.c, 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `unsequenced-effects` | 3 | 20 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `cast:PointerToIntegral` | 2 | 26 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `libc-call: malloc` | 2 | 13 | 20020406-1.c, 20051113-1.c, 920810-1.c, 941014-2.c, 960521-1.c |
| `libc-call: __builtin_return_address` | 2 | 4 | 20010122-1.c, 20030323-1.c, 20030811-1.c, pr17377.c |
| `libc-call: memset` | 1 | 22 | 00179.c, 20001203-2.c, 20031012-1.c, 20040823-1.c, 20050826-1.c |
| `libc-call: memcmp` | 1 | 20 | 00179.c, 20050502-2.c, 20050826-1.c, builtins/memops-asm.c, builtins/mempcpy-2.c |
| `libc-call: __builtin_memcmp` | 1 | 17 | 20081103-1.c, ieee/mzero2.c, ieee/mzero3.c, ieee/mzero5.c, pr108498-2.c |
| `unsupported:StmtExpr` | 1 | 10 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `libc-call: __builtin_alloca` | 1 | 9 | 20021113-1.c, 20070824-1.c, alloca-1.c, built-in-setjmp.c, frame-address.c |
| `unsupported:AddrLabelExpr` | 1 | 8 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `libc-call: __builtin_malloc` | 1 | 7 | 20071018-1.c, 20071120-1.c, pr15262-1.c, pr36765.c, pr43008.c |
| `libc-call: __builtin_ffs` | 1 | 5 | builtin-bitops-1.c, ffs-1.c, ffs-2.c, pr61725.c, pr97325.c |
| `libc-call: __builtin_constant_p` | 1 | 4 | 20030330-1.c, bcp-1.c, builtin-constant.c, pr19449.c |
| `libc-call: calloc` | 1 | 3 | 00040.c, 20020406-1.c, ipa-sra-2.c |
| `libc-call: link_error` | 1 | 3 | 20030330-1.c, ieee/fp-cmp-7.c, medce-1.c |
| `libc-call: __builtin_abs` | 1 | 2 | pr34130.c, pr42614.c |
| `libc-call: __c11_atomic_is_lock_free` | 1 | 1 | gcc/testsuite/gcc.dg/atomic/c23-stdatomic-lockfree-char8_t.c |
| `libc-call: fun` | 1 | 1 | pr42231.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `string-literal` | 0 | 241 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `cast:IntegralToFloating` | 0 | 81 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `libc-call: printf` | 0 | 73 | 00056.c, 00125.c, 00131.c, 00132.c, 00154.c |
| `libc-call: __builtin_c23_va_start` | 0 | 66 | 00204.c, 20000519-1.c, 20041113-1.c, 20071213-1.c, 920501-8.c |
| `libc-call: __builtin_va_end` | 0 | 64 | 20041214-1.c, 20071213-1.c, 920501-8.c, 920625-1.c, 920726-1.c |
| `cast:FloatingCast` | 0 | 53 | 00174.c, 00175.c, 00204.c, 20000605-1.c, 20020411-1.c |
| `libc-call: __builtin_memcpy` | 0 | 27 | 20000703-1.c, 20011121-1.c, 20030408-1.c, 20040411-1.c, 20060930-2.c |
| `libc-call: __builtin_memset` | 0 | 27 | 20020619-1.c, 20030606-1.c, 20030717-1.c, 20041218-1.c, 20071108-1.c |
| `cast:FloatingToIntegral` | 0 | 26 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c |
| `unsupported:PackedAttr` | 0 | 26 | 00210.c, 20010518-2.c, 20020227-1.c, 20030224-2.c, 20040625-1.c |
| `libc-call: strlen` | 0 | 21 | 00025.c, 00179.c, 20010409-1.c, 20011024-1.c, 20050218-1.c |
| `unsupported:AlignedAttr` | 0 | 15 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `libc-call: memcpy` | 0 | 14 | 00179.c, 20010925-1.c, 20011024-1.c, 20011113-1.c, 20050826-1.c |
| `libc-call: strcmp` | 0 | 14 | 00179.c, 20001011-1.c, 20011024-1.c, 20030715-1.c, 20041214-1.c |
| `libc-call: __builtin_printf` | 0 | 13 | 20020406-1.c, 20121108-1.c, 20141022-1.c, memchr-1.c, pr111863-1.c |
| `libc-call: __builtin_strcmp` | 0 | 12 | 20010915-1.c, 20021011-1.c, 920501-8.c, 920726-1.c, 921006-1.c |
| `libc-call: __builtin_strlen` | 0 | 12 | 20030221-1.c, 20031012-1.c, 920726-1.c, pr110914.c, pr116799.c |
| `libc-call: strcpy` | 0 | 12 | 00179.c, 00180.c, 20031204-1.c, 20041214-1.c, 20120207-1.c |
| `unsupported:ImaginaryLiteral` | 0 | 12 | 20041124-1.c, 20041201-1.c, 20070614-1.c, complex-1.c, complex-2.c |
| `libc-call: __builtin_mul_overflow` | 0 | 9 | pr108789.c, pr64006.c, pr68381.c, pr71554.c, pr84169.c |
| `libc-call: sprintf` | 0 | 9 | 00186.c, 20030626-1.c, 20030626-2.c, 20070201-1.c, 920501-8.c |
| `libc-call: __builtin_inf` | 0 | 8 | ieee/compare-fp-1.c, ieee/compare-fp-4.c, ieee/copysign1.c, ieee/copysign2.c, ieee/fp-cmp-7.c |
| `libc-call: __builtin_inff` | 0 | 7 | gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c, ieee/copysign1.c, ieee/copysign2.c, ieee/inf-1.c |
| `unsupported:IndirectGotoStmt` | 0 | 7 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `libc-call: __builtin_nan` | 0 | 6 | ieee/builtin-nan-1.c, ieee/compare-fp-1.c, ieee/compare-fp-4.c, ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_nanf` | 0 | 6 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c, ieee/copysign1.c, ieee/copysign2.c, ieee/pr109386.c |
| `libc-call: __builtin_prefetch` | 0 | 6 | builtin-prefetch-1.c, builtin-prefetch-2.c, builtin-prefetch-3.c, builtin-prefetch-4.c, builtin-prefetch-5.c |
| `libc-call: __builtin_strcpy` | 0 | 6 | 20021011-1.c, 921117-1.c, pr84339.c, pr86528.c, strcpy-2.c |
| `unsupported:ExprWithCleanups` | 0 | 6 | 00204.c, 20020320-1.c, 20041124-1.c, 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:IndirectFieldDecl` | 0 | 6 | 00046.c, 00050.c, 00216.c, anon-1.c, gcc/testsuite/gcc.dg/c23-tag-5.c |
| `libc-call: __builtin_add_overflow` | 0 | 5 | pr108789.c, pr85095.c, pr90311.c, pr91635.c, pr93494.c |
| `libc-call: __builtin_expect` | 0 | 5 | 00214.c, 20020418-1.c, ieee/unsafe-fp-assoc-1.c, pr115277.c, pr91597.c |
| `libc-call: __builtin_infl` | 0 | 5 | ieee/copysign1.c, ieee/copysign2.c, ieee/inf-1.c, ieee/inf-2.c, ieee/pr36332.c |
| `libc-call: __builtin_isunordered` | 0 | 5 | ieee/compare-fp-1.c, ieee/compare-fp-3.c, ieee/compare-fp-4.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_longjmp` | 0 | 5 | built-in-setjmp.c, builtins/lib/chk.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: strncmp` | 0 | 5 | 00179.c, 20050218-1.c, builtins/strstr-asm-lib.c, string-opt-18.c, strncmp-1.c |
| `libc-call: vprintf` | 0 | 5 | builtins/lib/printf.c, printf-chk-1.c, va-arg-21.c, vprintf-1.c, vprintf-chk-1.c |
| `libc-call: __builtin_copysign` | 0 | 4 | ieee/copysign1.c, ieee/copysign2.c, ieee/mzero6.c, pr44683.c |
| `libc-call: __builtin_copysignf` | 0 | 4 | ieee/copysign1.c, ieee/copysign2.c, ieee/pr72824-2.c, ieee/pr72824.c |
| `libc-call: __builtin_setjmp` | 0 | 4 | built-in-setjmp.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: __builtin_unreachable` | 0 | 4 | 20230509-1.c, gcc/testsuite/gcc.dg/c23-unreachable-1.c, pr81281.c, pr97888-1.c |
| `libc-call: abs` | 0 | 4 | 20041126-1.c, pr33142.c, ssad-run.c, usad-run.c |
| `libc-call: strchr` | 0 | 4 | 00179.c, 20000910-2.c, builtins/strstr-asm-lib.c, string-opt-5.c |
| `libc-call: vfprintf` | 0 | 4 | builtins/lib/fprintf.c, fprintf-chk-1.c, vfprintf-1.c, vfprintf-chk-1.c |
| `unsupported:GCCAsmStmt` | 0 | 4 | 20071211-1.c, 990413-2.c, pr56982.c, pr81588.c |
| `unsupported:OffsetOfExpr` | 0 | 4 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr103255.c, pr30778.c, pr44468.c |
| `libc-call: __builtin_fabs` | 0 | 3 | ieee/20010114-2.c, ieee/20030331-1.c, ieee/cdivchkd.c |
| `libc-call: __builtin_huge_val` | 0 | 3 | ieee/hugeval.c, ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_islessgreater` | 0 | 3 | ieee/compare-fp-1.c, ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isnan` | 0 | 3 | gcc/testsuite/gcc.dg/c23-float-4.c, ieee/inf-4.c, ieee/pr108540-1.c |
| `libc-call: __builtin_signbit` | 0 | 3 | 20080502-1.c, ieee/pr108540-1.c, pr35456.c |
| `libc-call: __builtin_sprintf` | 0 | 3 | 20021120-3.c, pr78586.c, pr79327.c |
| `libc-call: __builtin_va_copy` | 0 | 3 | stdarg-1.c, va-arg-10.c, va-arg-14.c |
| `libc-call: mempcpy` | 0 | 3 | builtins/mempcpy-2.c, builtins/mempcpy.c, string-opt-18.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `libc-call: __builtin_bswap32` | 0 | 2 | bswap-3.c, pr90025.c |
| `libc-call: __builtin_classify_type` | 0 | 2 | 20040709-1.c, 20040709-2.c |
| `libc-call: __builtin_clz` | 0 | 2 | builtin-bitops-1.c, pr37780.c |
| `libc-call: __builtin_copysignl` | 0 | 2 | ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_ctz` | 0 | 2 | builtin-bitops-1.c, pr37780.c |
| `libc-call: __builtin_fabsf` | 0 | 2 | ieee/cdivchkf.c, ieee/pr109386.c |
| `libc-call: __builtin_fmax` | 0 | 2 | ieee/cdivchkd.c, ieee/cdivchkf.c |
| `libc-call: __builtin_huge_valf` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_huge_vall` | 0 | 2 | ieee/inf-1.c, ieee/inf-3.c |
| `libc-call: __builtin_isgreater` | 0 | 2 | ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isgreaterequal` | 0 | 2 | ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_isinf` | 0 | 2 | ieee/pr108540-1.c, ieee/pr109386.c |
| `libc-call: __builtin_isless` | 0 | 2 | ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_islessequal` | 0 | 2 | ieee/fp-cmp-5.c, ieee/fp-cmp-8.c |
| `libc-call: __builtin_mempcpy` | 0 | 2 | builtins/mempcpy-2.c, builtins/mempcpy.c |
| `libc-call: __builtin_nanl` | 0 | 2 | ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: __builtin_trap` | 0 | 2 | 20020418-1.c, pr125291.c |
| `libc-call: __builtin_va_start` | 0 | 2 | 20041214-1.c, pr38151.c |
| `libc-call: _setjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: floor` | 0 | 2 | 990826-0.c, float-floor.c |
| `libc-call: fprintf` | 0 | 2 | fprintf-1.c, gofast.c |
| `libc-call: free` | 0 | 2 | ipa-sra-2.c, pr42614.c |
| `libc-call: fwrite` | 0 | 2 | 00187.c, builtins/fputs-lib.c |
| `libc-call: ilogb` | 0 | 2 | ieee/cdivchkd.c, ieee/cdivchkf.c |
| `libc-call: longjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: mmap` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: open` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: sin` | 0 | 2 | 00174.c, ieee/mzero4.c |
| `libc-call: stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: strcat` | 0 | 2 | 00179.c, builtins/strcat.c |
| `libc-call: strncpy` | 0 | 2 | 00179.c, string-opt-5.c |
| `libc-call: strrchr` | 0 | 2 | 00179.c, string-opt-5.c |
| `libc-call: vsprintf` | 0 | 2 | builtins/lib/chk.c, builtins/lib/sprintf.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `libc-call: __assert_fail` | 0 | 1 | pr58831.c |
| `libc-call: __builtin_bswap16` | 0 | 1 | pr97386-1.c |
| `libc-call: __builtin_bswap64` | 0 | 1 | bswap-1.c |
| `libc-call: __builtin_bzero` | 0 | 1 | builtins/memops-asm.c |
| `libc-call: __builtin_clrsb` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clrsbl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clrsbll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clzl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_clzll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_conjf` | 0 | 1 | 20020411-1.c |
| `libc-call: __builtin_ctzl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_ctzll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_fabsl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: __builtin_ffsl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_ffsll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_fmaxl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: __builtin_frame_address` | 0 | 1 | frame-address.c |
| `libc-call: __builtin_free` | 0 | 1 | pr84339.c |
| `libc-call: __builtin_isfinite` | 0 | 1 | ieee/inf-4.c |
| `libc-call: __builtin_memmove` | 0 | 1 | pr93213.c |
| `libc-call: __builtin_parity` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_parityl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_parityll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcount` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcountl` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_popcountll` | 0 | 1 | builtin-bitops-1.c |
| `libc-call: __builtin_snprintf` | 0 | 1 | pr78622.c |
| `libc-call: __builtin_strcat` | 0 | 1 | builtins/strcat.c |
| `libc-call: __builtin_strncpy` | 0 | 1 | pr93249.c |
| `libc-call: __sync_add_and_fetch_8` | 0 | 1 | pr122000.c |
| `libc-call: alloca` | 0 | 1 | 20010122-1.c |
| `libc-call: atan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: atoi` | 0 | 1 | 20221006-1.c |
| `libc-call: bcopy` | 0 | 1 | builtins/memops-asm.c |
| `libc-call: compare1` | 0 | 1 | pr34456.c |
| `libc-call: f` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: fabs` | 0 | 1 | 20020720-1.c |
| `libc-call: fclose` | 0 | 1 | 00187.c |
| `libc-call: fetestexcept` | 0 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `libc-call: fgetc` | 0 | 1 | 00187.c |
| `libc-call: fgets` | 0 | 1 | 00187.c |
| `libc-call: fopen` | 0 | 1 | 00187.c |
| `libc-call: fp` | 0 | 1 | func-ptr-1.c |
| `libc-call: fprintfptr` | 0 | 1 | 00189.c |
| `libc-call: fread` | 0 | 1 | 00187.c |
| `libc-call: func` | 0 | 1 | bcp-1.c |
| `libc-call: g` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: getc` | 0 | 1 | 00187.c |
| `libc-call: h1` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h2` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h3` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h4` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h5` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h6` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h7` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: ilogbl` | 0 | 1 | ieee/cdivchkld.c |
| `libc-call: indirect` | 0 | 1 | pr68390.c |
| `libc-call: isprint` | 0 | 1 | 991112-1.c |
| `libc-call: memchr` | 0 | 1 | memchr-1.c |
| `libc-call: memmove` | 0 | 1 | string-opt-18.c |
| `libc-call: not_defined` | 0 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `libc-call: p` | 0 | 1 | 00216.c |
| `libc-call: pow` | 0 | 1 | 980709-1.c |
| `libc-call: putchar` | 0 | 1 | 00204.c |
| `libc-call: qsort` | 0 | 1 | pr34456.c |
| `libc-call: sinf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: sqrt` | 0 | 1 | ieee/20041213-1.c |
| `libc-call: tan` | 0 | 1 | ieee/mzero4.c |
| `libc-call: tanf` | 0 | 1 | ieee/mzero4.c |
| `libc-call: terminate_me` | 0 | 1 | pr54937.c |
| `libc-call: x` | 0 | 1 | 991112-1.c |
| `unsupported:BinaryConditionalOperator` | 0 | 1 | pr68249.c |
| `unsupported:CXXNullPtrLiteralExpr` | 0 | 1 | gcc/testsuite/gcc.dg/c23-nullptr-5.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 350 | 350 | 00209.c, 20000112-1.c, 20000227-1.c, 20000314-3.c, 20000412-3.c |
| `timeout` | 87 | 87 | 00040.c, 00041.c, 00128.c, 20000121-1.c, 20000412-2.c |
| `undefined-behavior` | 86 | 86 | 00032.c, 00141.c, 00144.c, 00200.c, 20000910-1.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 40 | 40 | builtins/20010124-1-lib.c, builtins/complex-1-lib.c, builtins/fputs-lib.c, builtins/lib/abs.c, builtins/lib/bfill.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 24 | 24 | 00103.c, 00170.c, 20001017-2.c, 20050316-1.c, 20050607-1.c |
| `unsupported:implementation-defined bit-field conversion` | 18 | 18 | 00218.c, 20230630-1.c, 20230630-2.c, 20230630-3.c, 20230630-4.c |
| `unsupported:pointer-to-integer conversion outside uintptr_t/intptr_t` | 14 | 14 | 20011121-1.c, 20050215-1.c, 20060420-1.c, 941014-1.c, 941014-2.c |
| `unsupported:integer-to-pointer conversion is not an unchanged uintptr_t/intptr_t round-trip` | 13 | 13 | 00214.c, 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c |
| `unsequenced-effects` | 11 | 11 | 20001228-1.c, 20020406-1.c, 20051021-1.c, 20230510-1.c, 930930-2.c |
| `unsupported:long double floating literal` | 10 | 10 | 20030914-1.c, 20080502-1.c, gcc/testsuite/gcc.dg/c23-float-1.c, ieee/20010226-1.c, ieee/inf-2.c |
| `unsupported:no layout for declared type 'V'` | 9 | 9 | pr105613.c, pr110817-1.c, pr110817-2.c, pr110817-3.c, pr71626-1.c |
| `unsupported:AddrLabelExpr` | 7 | 7 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:StmtExpr` | 7 | 7 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c |
| `unsupported:printf` | 6 | 6 | 00174.c, 00175.c, 00195.c, 00205.c, 00213.c |
| `unsupported:no layout for declared type '_Complex double'` | 5 | 5 | 20030910-1.c, 960512-1.c, complex-1.c, complex-2.c, ieee/cdivchkd.c |
| `unsupported:case label nested in a control statement` | 4 | 4 | 00051.c, 00143.c, 20111208-1.c, medce-1.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `unsupported:floating cast has incompatible source and destination` | 4 | 4 | 00204.c, 20020413-1.c, 990413-2.c, align-2.c |
| `unsupported:no layout for declared type 'long double'` | 4 | 4 | 20040208-1.c, ieee/20011123-1.c, ieee/inf-1.c, ieee/pr29302-1.c |
| `libc-call: __builtin_abort` | 3 | 3 | gcc/testsuite/gcc.dg/c23-nullptr-5.c, pr58943.c, pr77767.c |
| `libc-call: __builtin_setjmp` | 3 | 3 | built-in-setjmp.c, pr64242.c, pr84521.c |
| `unsupported:ExprWithCleanups` | 3 | 3 | 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c, pr30185.c |
| `unsupported:OffsetOfExpr` | 3 | 3 | gcc/testsuite/gcc.dg/c23-empty-init-5.c, pr30778.c, pr44468.c |
| `unsupported:call to '__builtin_inff' in a context with no program — call it through 'callByName'` | 3 | 3 | gcc/testsuite/gcc.dg/c23-float-3.c, ieee/copysign1.c, ieee/copysign2.c |
| `unsupported:no layout for declared type '_Complex float'` | 3 | 3 | complex-6.c, ieee/cdivchkf.c, pr38969.c |
| `unsupported:no layout for declared type 'int[n % 1000 + 1]'` | 3 | 3 | 20040811-1.c, pr43220.c, vla-dealloc-1.c |
| `unsupported:no layout for declared type 'size_t'` | 3 | 3 | strcmp-1.c, strlen-1.c, strncmp-1.c |
| `unsupported:no layout for declared type 'struct S'` | 3 | 3 | pr52979-1.c, pr52979-2.c, pr79737-1.c |
| `unsupported:type trait '__alignof'` | 3 | 3 | 20000223-1.c, align-3.c, zerolen-2.c |
| `cast:FloatingRealToComplex` | 2 | 2 | complex-4.c, pr42248.c |
| `cast:IntegralComplexCast` | 2 | 2 | 20041124-1.c, 20041201-1.c |
| `cast:IntegralRealToComplex` | 2 | 2 | pr104604.c, pr38151.c |
| `libc-call: exit (an argument is not a literal 0 — which exit was reached is unknown)` | 2 | 2 | 970217-1.c, loop-8.c |
| `libc-call: open` | 2 | 2 | loop-2f.c, loop-2g.c |
| `unsupported:GCCAsmStmt` | 2 | 2 | 20071211-1.c, pr81588.c |
| `unsupported:GenericSelectionExpr` | 2 | 2 | gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-float-2.c |
| `unsupported:break, continue or goto escaped a function body` | 2 | 2 | 00199.c, 20040704-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 2 | 2 | 00210.c, call-trap-1.c |
| `unsupported:call to '__builtin_nanf' in a context with no program — call it through 'callByName'` | 2 | 2 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:floating value used as an integer` | 2 | 2 | 20000731-1.c, 20011217-1.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:no layout for declared type 'jmp_buf'` | 2 | 2 | 20210505-1.c, pr56982.c |
| `unsupported:no layout for declared type 'v16di'` | 2 | 2 | pr123625-2.c, pr126405-3.c |
| `unsupported:operator '-' on pointers without array provenance` | 2 | 2 | 980701-1.c, pr36321.c |
| `unsupported:sprintf` | 2 | 2 | 920501-8.c, struct-ret-1.c |
| `unsupported:unbound declaration 'id15' (name 'a')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-imaginary-constants-1.c, gcc/testsuite/gcc.dg/c23-imaginary-constants-7.c |
| `unsupported:unbound declaration 'id29' (name 'gap')` | 2 | 2 | stdarg-1.c, stdarg-2.c |
| `unsupported:unbound declaration 'id39' (name 'X')` | 2 | 2 | 960215-1.c, regstack-1.c |
| `cast:FloatingComplexCast` | 1 | 1 | 20070614-1.c |
| `libc-call: __builtin_classify_type` | 1 | 1 | 20040709-1.c |
| `libc-call: __builtin_constant_p` | 1 | 1 | builtin-constant.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: __builtin_islessgreater` | 1 | 1 | ieee/compare-fp-1.c |
| `libc-call: __builtin_snprintf` | 1 | 1 | pr78622.c |
| `libc-call: f` | 1 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: fopen` | 1 | 1 | 00187.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: pow` | 1 | 1 | 980709-1.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `libc-call: sin` | 1 | 1 | ieee/mzero4.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:TypeTraitExpr` | 1 | 1 | builtin-types-compatible-p.c |
| `unsupported:aggregate load without a layout '__attribute__((__vector_size__(4 * sizeof(unsigned short)))) unsigned short'` | 1 | 1 | 20050604-1.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call to '__builtin_nan' in a context with no program — call it through 'callByName'` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:cannot initialize aggregate 'int'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
| `unsupported:cannot initialize aggregate 'u8'` | 1 | 1 | 00216.c |
| `unsupported:explicit initializer for flexible array member 'a3p'` | 1 | 1 | 20010924-1.c |
| `unsupported:explicit initializer for flexible array member 'j'` | 1 | 1 | pr33382.c |
| `unsupported:explicit initializer for flexible array member 'z'` | 1 | 1 | 20030109-1.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:extern object 'p' has no definition in the translation unit` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:function-to-pointer decay of an unresolved function` | 1 | 1 | 00219.c |
| `unsupported:long double integer-to-floating conversion` | 1 | 1 | 930622-2.c |
| `unsupported:no layout for compound literal type 'V'` | 1 | 1 | pr109040.c |
| `unsupported:no layout for compound literal type 'v2si'` | 1 | 1 | simd-4.c |
| `unsupported:no layout for declared type 'A'` | 1 | 1 | strct-pack-2.c |
| `unsupported:no layout for declared type 'A0'` | 1 | 1 | va-arg-22.c |
| `unsupported:no layout for declared type 'Q'` | 1 | 1 | simd-5.c |
| `unsupported:no layout for declared type 'TRIAL'` | 1 | 1 | strct-pack-1.c |
| `unsupported:no layout for declared type 'V2SF'` | 1 | 1 | 20050316-2.c |
| `unsupported:no layout for declared type 'V2SI'` | 1 | 1 | 20050316-3.c |
| `unsupported:no layout for declared type 'V32'` | 1 | 1 | pr70903.c |
| `unsupported:no layout for declared type 'V[32]'` | 1 | 1 | ieee/pr72824-2.c |
| `unsupported:no layout for declared type '_Complex double[12]'` | 1 | 1 | pr49644.c |
| `unsupported:no layout for declared type '_Complex double[1]'` | 1 | 1 | 20020411-1.c |
| `unsupported:no layout for declared type '_Complex long double'` | 1 | 1 | ieee/cdivchkld.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(16 * sizeof(char)))) char'` | 1 | 1 | scal-to-vec2.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(4 * sizeof(float)))) float'` | 1 | 1 | scal-to-vec3.c |
| `unsupported:no layout for declared type '__attribute__((__vector_size__(8 * sizeof(short)))) short'` | 1 | 1 | scal-to-vec1.c |
| `unsupported:no layout for declared type '__m128i'` | 1 | 1 | pr92618.c |
| `unsupported:no layout for declared type 'char[argc]'` | 1 | 1 | 00207.c |
| `unsupported:no layout for declared type 'double (*)(float)'` | 1 | 1 | func-ptr-1.c |
| `unsupported:no layout for declared type 'double[n]'` | 1 | 1 | 920929-1.c |
| `unsupported:no layout for declared type 'int (*)(int, int)'` | 1 | 1 | 991112-1.c |
| `unsupported:no layout for declared type 'int (*)[++i]'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-auto-2.c |
| `unsupported:no layout for declared type 'int[len][len]'` | 1 | 1 | 20221006-1.c |
| `unsupported:no layout for declared type 'struct A'` | 1 | 1 | 20040709-2.c |
| `unsupported:no layout for declared type 'struct S[21]'` | 1 | 1 | pr70602.c |
| `unsupported:no layout for declared type 'struct S[6]'` | 1 | 1 | pr58570.c |
| `unsupported:no layout for declared type 'struct c'` | 1 | 1 | packed-aligned.c |
| `unsupported:no layout for declared type 'struct foo'` | 1 | 1 | bf-pack-1.c |
| `unsupported:no layout for declared type 'struct packed_ushort'` | 1 | 1 | pr45070.c |
| `unsupported:no layout for declared type 'struct product_iSfd_'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-5.c |
| `unsupported:no layout for declared type 'struct s'` | 1 | 1 | pr29006.c |
| `unsupported:no layout for declared type 'struct tty_driver'` | 1 | 1 | struct-cpy-1.c |
| `unsupported:no layout for declared type 'struct x'` | 1 | 1 | 20020227-1.c |
| `unsupported:no layout for declared type 'three_byte_t'` | 1 | 1 | struct-ret-2.c |
| `unsupported:no layout for declared type 'three_char_t'` | 1 | 1 | strct-pack-4.c |
| `unsupported:no layout for declared type 'typeof (*(1 ? &x ` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-alias-7.c |
| `unsupported:no layout for declared type 'v4qi'` | 1 | 1 | pr60960.c |
| `unsupported:no layout for declared type 'v4si'` | 1 | 1 | ieee/fp-cmp-cond-1.c |
| `unsupported:no layout for declared type 'v8qi'` | 1 | 1 | simd-6.c |
| `unsupported:no layout for declared type 'vecint'` | 1 | 1 | pr23135.c |
| `unsupported:no layout for declared type 'volatile a_struct'` | 1 | 1 | 20010518-2.c |
| `unsupported:no layout for declared type 'volatile long double'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-float-12.c |
| `unsupported:no layout for declared type 'wchar_t[21]'` | 1 | 1 | 00220.c |
| `unsupported:no layout for field 'Count'` | 1 | 1 | 20051113-1.c |
| `unsupported:no layout for field 'pst1'` | 1 | 1 | 20100430-1.c |
| `unsupported:no layout for parameter type 'double (*)(double)'` | 1 | 1 | 921208-1.c |
| `unsupported:no layout for parameter type 'double (*)(int, ...)'` | 1 | 1 | pr68390.c |
| `unsupported:no layout for parameter type 'int (*)(int)'` | 1 | 1 | pr42231.c |
| `unsupported:no layout for parameter type 'int **restrict'` | 1 | 1 | 20080506-2.c |
| `unsupported:no layout for parameter type 'int *restrict'` | 1 | 1 | pr38212.c |
| `unsupported:no layout for parameter type 'void (*)(double)'` | 1 | 1 | 20021118-2.c |
| `unsupported:no size for element type 'unsigned32'` | 1 | 1 | cbrt.c |
| `unsupported:no size for pointee of 'const char (*)[1]'` | 1 | 1 | memchr-1.c |
| `unsupported:no size for pointee of 'int (*)[4]'` | 1 | 1 | pr124358.c |
| `unsupported:non-object declaration in a block` | 1 | 1 | 00078.c |
| `unsupported:not an integer type: 'double'` | 1 | 1 | stdarg-4.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:operator '-' on pointers from different arrays` | 1 | 1 | 950710-1.c |
| `unsupported:sizeof: no layout for operand type '_Atomic(unsigned char)'` | 1 | 1 | gcc/testsuite/gcc.dg/atomic/c23-stdatomic-lockfree-char8_t.c |
| `unsupported:sizeof: no layout for operand type 'c'` | 1 | 1 | 20040411-1.c |
| `unsupported:sizeof: no layout for operand type 'int (*volatile[6])(void)'` | 1 | 1 | bcp-1.c |
| `unsupported:sizeof: no layout for operand type 'va_list'` | 1 | 1 | va-arg-21.c |
| `unsupported:src/20000412-5.c` | 1 | 1 | 20000412-5.c |
| `unsupported:src/930628-1.c` | 1 | 1 | 930628-1.c |
| `unsupported:src/ffs-2.c` | 1 | 1 | ffs-2.c |
| `unsupported:src/ieee/mul-subnormal-single-1.c` | 1 | 1 | ieee/mul-subnormal-single-1.c |
| `unsupported:strcpy` | 1 | 1 | string-opt-18.c |
| `unsupported:unary operator '__real'` | 1 | 1 | 20050121-1.c |
| `unsupported:unbound declaration 'id15' (name 'f1')` | 1 | 1 | complex-7.c |
| `unsupported:unbound declaration 'id15' (name 'fptr')` | 1 | 1 | 00088.c |
| `unsupported:unbound declaration 'id15' (name 'x')` | 1 | 1 | 20090623-1.c |
| `unsupported:unbound declaration 'id18' (name 'a')` | 1 | 1 | pr65427.c |
| `unsupported:unbound declaration 'id197' (name 'func1')` | 1 | 1 | 20010122-1.c |
| `unsupported:unbound declaration 'id21' (name 'a')` | 1 | 1 | pr56837.c |
| `unsupported:unbound declaration 'id22' (name 't')` | 1 | 1 | packed-2.c |
| `unsupported:unbound declaration 'id26' (name 'u')` | 1 | 1 | pr87053.c |
| `unsupported:unbound declaration 'id27' (name 'x')` | 1 | 1 | 960405-1.c |
| `unsupported:unbound declaration 'id28' (name 'terminate_me')` | 1 | 1 | pr54937.c |
| `unsupported:unbound declaration 'id30' (name 'b')` | 1 | 1 | 20131127-1.c |
| `unsupported:unbound declaration 'id31' (name 'ap')` | 1 | 1 | va-arg-trap-1.c |
| `unsupported:unbound declaration 'id31' (name 'global')` | 1 | 1 | va-arg-14.c |
| `unsupported:unbound declaration 'id32' (name 'node')` | 1 | 1 | 20030224-2.c |
| `unsupported:unbound declaration 'id33' (name 't')` | 1 | 1 | packed-1.c |
| `unsupported:unbound declaration 'id426' (name 'array')` | 1 | 1 | pr34456.c |
| `unsupported:unbound declaration 'id45' (name 'k')` | 1 | 1 | simd-1.c |
| `unsupported:unbound declaration 'id48' (name 'curval')` | 1 | 1 | 960117-1.c |
| `unsupported:unbound declaration 'id50' (name 'ws')` | 1 | 1 | widechar-2.c |
| `unsupported:unbound declaration 'id528' (name 'fprintfptr')` | 1 | 1 | 00189.c |
| `unsupported:unbound declaration 'id66' (name 'k')` | 1 | 1 | simd-2.c |
| `unsupported:unbound declaration 'id67' (name 'z')` | 1 | 1 | complex-5.c |
| `unsupported:union initializer has no member` | 1 | 1 | pr15296.c |
| `unsupported:unknown enum declaration 'id18' (name 'C')` | 1 | 1 | pr91597.c |
| `unsupported:unknown enum declaration 'id543' (name 'e')` | 1 | 1 | 00198.c |
| `unsupported:unnamed pointer parameter (array-bound effects are not retained by clang)` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
