# C torture survey

Generated from the pinned `gcc.c-torture/execute` manifest.

- verdicts: 1386/2114 MATCH (passed 1386, failed 0, oracle 0)
- excluded from denominator: no-entry-point 100
- manifest SHA-256: `722004ac2230d76ffb8f1cc321ccc877bfa7be6449cf8edc0af6cc34bb3c1363`
- measured commit: `7ba95a10396bf65e5538c93f2318b982dd11cff1`
- measured at: `2026-11-24T02:50:00Z`

## Verdict counts

| verdict | files |
| --- | ---: |
| `no-entry-point` | 100 |
| `not-ingested` | 1 |
| `not-parsed` | 432 |
| `oracle-tests-compiler` | 3 |
| `passed` | 1386 |
| `refused-libc` | 21 |
| `refused-ub` | 47 |
| `refused-unsupported` | 313 |
| `runner-error` | 11 |

## Counts by corpus

| corpus | verdict | files |
| --- | --- | ---: |
| `c-testsuite/single-exec` | `not-parsed` | 3 |
| `c-testsuite/single-exec` | `passed` | 193 |
| `c-testsuite/single-exec` | `refused-libc` | 1 |
| `c-testsuite/single-exec` | `refused-ub` | 5 |
| `c-testsuite/single-exec` | `refused-unsupported` | 17 |
| `c-testsuite/single-exec` | `runner-error` | 1 |
| `gcc.c-torture/execute` | `not-ingested` | 1 |
| `gcc.c-torture/execute` | `not-parsed` | 395 |
| `gcc.c-torture/execute` | `oracle-tests-compiler` | 3 |
| `gcc.c-torture/execute` | `passed` | 1183 |
| `gcc.c-torture/execute` | `refused-libc` | 19 |
| `gcc.c-torture/execute` | `refused-ub` | 41 |
| `gcc.c-torture/execute` | `refused-unsupported` | 178 |
| `gcc.c-torture/execute` | `runner-error` | 10 |
| `gcc.c23-run` | `not-parsed` | 34 |
| `gcc.c23-run` | `passed` | 10 |
| `gcc.c23-run` | `refused-libc` | 1 |
| `gcc.c23-run` | `refused-ub` | 1 |
| `gcc.c23-run` | `refused-unsupported` | 18 |

## Static wall ranking

`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `type-layout` | 548 | 1004 | 00015.c, 00016.c, 00017.c, 00018.c, 00019.c |
| `unsequenced-effects` | 7 | 17 | 00121.c, 20001228-1.c, 20020406-1.c, 20060102-1.c, 20230802-1.c |
| `libc-call` | 4 | 17 | 00087.c, 00089.c, 00124.c, 00159.c, 00189.c |
| `cast:IntegralToPointer` | 3 | 26 | 00214.c, 20000314-1.c, 20000622-1.c, 20010329-1.c, 20021010-2.c |
| `cast:PointerToIntegral` | 2 | 25 | 00144.c, 20000622-1.c, 20011121-1.c, 20030811-1.c, 20050215-1.c |
| `libc-call: link_error` | 2 | 6 | 20030330-1.c, builtins/abs-2.c, builtins/memcmp.c, builtins/uabs-2.c, ieee/fp-cmp-7.c |
| `libc-call: __builtin_return_address` | 2 | 4 | 20010122-1.c, 20030323-1.c, 20030811-1.c, pr17377.c |
| `unsupported:StmtExpr` | 1 | 9 | 00213.c, 00214.c, 20000703-1.c, 20000917-1.c, 20001203-2.c |
| `unsupported:AddrLabelExpr` | 1 | 8 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:GCCAsmStmt` | 1 | 4 | 20071211-1.c, 990413-2.c, pr56982.c, pr81588.c |
| `libc-call: fwrite` | 1 | 2 | 00187.c, builtins/fputs-lib.c |
| `libc-call: labs` | 1 | 2 | builtins/abs-1.c, builtins/abs-2.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: fun` | 1 | 1 | pr42231.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: not_defined` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `libc-call: x` | 1 | 1 | 991112-1.c |
| `unsupported:BinaryConditionalOperator` | 1 | 1 | pr68249.c |
| `string-literal` | 0 | 254 | 00025.c, 00026.c, 00056.c, 00058.c, 00112.c |
| `cast:IntegralToFloating` | 0 | 70 | 00113.c, 00119.c, 00123.c, 00174.c, 00175.c |
| `cast:FloatingCast` | 0 | 44 | 00174.c, 00175.c, 00204.c, 20000605-1.c, 20020413-1.c |
| `cast:FloatingToIntegral` | 0 | 26 | 00175.c, 20000605-1.c, 20010118-1.c, 20031003-1.c, 20040709-1.c |
| `unsupported:PackedAttr` | 0 | 24 | 20010518-2.c, 20030224-2.c, 20040625-1.c, 20040709-2.c, 20051113-1.c |
| `unsupported:AlignedAttr` | 0 | 14 | 20010904-1.c, 20010904-2.c, 20171008-1.c, 960117-1.c, 990326-1.c |
| `unsupported:IndirectGotoStmt` | 0 | 7 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:GenericSelectionExpr` | 0 | 6 | 00219.c, gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-float-2.c, gcc/testsuite/gcc.dg/c23-float-3.c |
| `unsupported:IndirectFieldDecl` | 0 | 6 | 00046.c, 00050.c, 00216.c, anon-1.c, gcc/testsuite/gcc.dg/c23-tag-5.c |
| `libc-call: __builtin_longjmp` | 0 | 5 | built-in-setjmp.c, builtins/lib/chk.c, pr60003.c, pr64242.c, pr84521.c |
| `unsupported:ExprWithCleanups` | 0 | 5 | 00204.c, 20020320-1.c, 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c, pr30185.c |
| `libc-call: __builtin_setjmp` | 0 | 4 | built-in-setjmp.c, pr60003.c, pr64242.c, pr84521.c |
| `libc-call: bcopy` | 0 | 3 | builtins/memmove-2.c, builtins/memmove.c, builtins/memops-asm.c |
| `unsupported:MaxFieldAlignmentAttr` | 0 | 3 | 20131127-1.c, pr58570.c, pr79737-1.c |
| `unsupported:MayAliasAttr` | 0 | 3 | mayalias-2.c, mayalias-3.c, pr43987.c |
| `unsupported:ModeAttr` | 0 | 3 | 20050107-1.c, 20050119-1.c, 20050119-2.c |
| `libc-call: __builtin_classify_type` | 0 | 2 | 20040709-1.c, 20040709-2.c |
| `libc-call: __builtin_copysignl` | 0 | 2 | ieee/copysign1.c, ieee/copysign2.c |
| `libc-call: __builtin_stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: __builtin_strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: __builtin_trap` | 0 | 2 | 20020418-1.c, pr125291.c |
| `libc-call: _setjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: f` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: g` | 0 | 2 | builtins/20010124-1.c, gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: longjmp` | 0 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: mmap` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: open` | 0 | 2 | loop-2f.c, loop-2g.c |
| `libc-call: stpcpy` | 0 | 2 | builtins/strpcpy-2.c, builtins/strpcpy.c |
| `libc-call: strstr` | 0 | 2 | builtins/strstr-asm.c, builtins/strstr.c |
| `libc-call: uabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `libc-call: ulabs` | 0 | 2 | builtins/uabs-1.c, builtins/uabs-2.c |
| `libc-call: vsprintf` | 0 | 2 | builtins/lib/chk.c, builtins/lib/sprintf.c |
| `unsupported:PredefinedExpr` | 0 | 2 | 20001011-1.c, pr58831.c |
| `unsupported:StaticAssertDecl` | 0 | 2 | gcc/testsuite/gcc.dg/c23-bool-2.c, gcc/testsuite/gcc.dg/c23-digit-separators-1.c |
| `libc-call: __assert_fail` | 0 | 1 | pr58831.c |
| `libc-call: __builtin_bcopy` | 0 | 1 | builtins/memmove.c |
| `libc-call: __builtin_bzero` | 0 | 1 | builtins/memops-asm.c |
| `libc-call: __builtin_index` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_strchr` | 0 | 1 | builtins/strchr.c |
| `libc-call: __builtin_strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: __builtin_strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: __builtin_strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: __builtin_strrchr` | 0 | 1 | builtins/strrchr.c |
| `libc-call: __builtin_strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: alloca` | 0 | 1 | 20010122-1.c |
| `libc-call: atoi` | 0 | 1 | 20221006-1.c |
| `libc-call: compare1` | 0 | 1 | pr34456.c |
| `libc-call: fclose` | 0 | 1 | 00187.c |
| `libc-call: fetestexcept` | 0 | 1 | gcc/testsuite/gcc.dg/c23-float-5.c |
| `libc-call: fgetc` | 0 | 1 | 00187.c |
| `libc-call: fgets` | 0 | 1 | 00187.c |
| `libc-call: fopen` | 0 | 1 | 00187.c |
| `libc-call: fp` | 0 | 1 | func-ptr-1.c |
| `libc-call: fprintfptr` | 0 | 1 | 00189.c |
| `libc-call: fread` | 0 | 1 | 00187.c |
| `libc-call: func` | 0 | 1 | bcp-1.c |
| `libc-call: getc` | 0 | 1 | 00187.c |
| `libc-call: h1` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h2` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h3` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h4` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h5` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h6` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: h7` | 0 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: imaxabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: index` | 0 | 1 | builtins/strchr.c |
| `libc-call: indirect` | 0 | 1 | pr68390.c |
| `libc-call: llabs` | 0 | 1 | builtins/abs-2.c |
| `libc-call: p` | 0 | 1 | 00216.c |
| `libc-call: pow` | 0 | 1 | 980709-1.c |
| `libc-call: qsort` | 0 | 1 | pr34456.c |
| `libc-call: rindex` | 0 | 1 | builtins/strrchr.c |
| `libc-call: strcspn` | 0 | 1 | builtins/strcspn.c |
| `libc-call: strncat` | 0 | 1 | builtins/strncat.c |
| `libc-call: strpbrk` | 0 | 1 | builtins/strpbrk.c |
| `libc-call: strspn` | 0 | 1 | builtins/strspn.c |
| `libc-call: terminate_me` | 0 | 1 | pr54937.c |
| `libc-call: ullabs` | 0 | 1 | builtins/uabs-2.c |
| `libc-call: umaxabs` | 0 | 1 | builtins/uabs-2.c |
| `unsupported:LabelDecl` | 0 | 1 | 980526-1.c |
| `unsupported:TypeTraitExpr` | 0 | 1 | builtin-types-compatible-p.c |

## Dynamic first-refusal ranking

The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.

| wall | sole | present | example files |
| --- | ---: | ---: | --- |
| `frontend` | 432 | 432 | 00162.c, 00209.c, 00210.c, 20000112-1.c, 20000227-1.c |
| `undefined-behavior` | 47 | 47 | 00032.c, 00141.c, 00144.c, 00200.c, 00216.c |
| `unsupported:extern object 'inside_main' has no definition in the translation unit` | 39 | 39 | builtins/20010124-1-lib.c, builtins/fputs-lib.c, builtins/lib/abs.c, builtins/lib/bfill.c, builtins/lib/bzero.c |
| `unsupported:pointer bit-cast across incompatible effective types` | 20 | 20 | 00103.c, 00170.c, 20060412-1.c, 991228-1.c, alias-1.c |
| `unsupported:nonValueRepresentation` | 17 | 17 | 20011121-1.c, 20050215-1.c, 941014-1.c, 941014-2.c, 980526-2.c |
| `unsupported:long double floating literal` | 14 | 14 | 20030914-1.c, 20040208-1.c, 20080502-1.c, 960405-1.c, gcc/testsuite/gcc.dg/c23-float-1.c |
| `unsupported:isolated non-null integer-to-pointer cast requires PNVI-ae exposure and recovery` | 12 | 12 | 00214.c, 20000622-1.c, 20010329-1.c, 20021010-2.c, 20041112-1.c |
| `unsupported:indeterminate lvalue read requires a representation choice` | 10 | 10 | 20071120-1.c, 20090113-1.c, 20090527-1.c, 20100430-1.c, builtin-prefetch-2.c |
| `unsupported:AddrLabelExpr` | 7 | 7 | 20040302-1.c, 20041214-1.c, 20071210-1.c, 920501-4.c, 920501-5.c |
| `unsupported:StmtExpr` | 6 | 6 | 20000703-1.c, 20000917-1.c, 20020206-1.c, 20020320-1.c, 930406-1.c |
| `unsupported:floating cast has incompatible source and destination` | 6 | 6 | 00204.c, 20020413-1.c, 990413-2.c, align-2.c, ieee/20011123-1.c |
| `unsupported:extern object 'b' has no definition in the translation unit` | 4 | 4 | alias-2.c, alias-3.c, alias-4.c, gcc/testsuite/gcc.dg/c23-bool-2.c |
| `libc-call: __builtin_setjmp` | 3 | 3 | built-in-setjmp.c, pr64242.c, pr84521.c |
| `unsupported:ExprWithCleanups` | 3 | 3 | 950628-1.c, gcc/testsuite/gcc.dg/c23-stdarg-9.c, pr30185.c |
| `unsupported:arithmetic on bit-fields wider than int requires exact promotion semantics` | 3 | 3 | bitfld-3.c, pr32244-1.c, pr34971.c |
| `unsupported:break, continue or goto escaped a function body` | 3 | 3 | 00199.c, 00213.c, 20040704-1.c |
| `unsupported:call to '__builtin_inff' in a context with no program — call it through 'callByName'` | 3 | 3 | gcc/testsuite/gcc.dg/c23-float-3.c, ieee/copysign1.c, ieee/copysign2.c |
| `unsupported:case label nested in a control statement` | 3 | 3 | 00051.c, 00143.c, medce-1.c |
| `unsupported:integer-to-floating conversion lacks parser-native destination type` | 3 | 3 | 930622-2.c, 960215-1.c, regstack-1.c |
| `unsupported:variable-length array 'int[n % 1000 + 1]' lacks parser-native bound expression` | 3 | 3 | 20040811-1.c, pr43220.c, vla-dealloc-1.c |
| `libc-call: __builtin_classify_type` | 2 | 2 | 20040709-1.c, 20040709-2.c |
| `libc-call: __builtin_return_address` | 2 | 2 | 20010122-1.c, pr17377.c |
| `libc-call: _setjmp` | 2 | 2 | 20210505-1.c, pr56982.c |
| `libc-call: exit (an argument is not a literal 0 — which exit was reached is unknown)` | 2 | 2 | 970217-1.c, loop-8.c |
| `libc-call: open` | 2 | 2 | loop-2f.c, loop-2g.c |
| `unsupported:GCCAsmStmt` | 2 | 2 | 20071211-1.c, pr81588.c |
| `unsupported:GenericSelectionExpr` | 2 | 2 | gcc/testsuite/gcc.dg/c23-bool-1.c, gcc/testsuite/gcc.dg/c23-float-2.c |
| `unsupported:byte copy spans a subobject boundary` | 2 | 2 | 20050826-1.c, strlen-7.c |
| `unsupported:call to '__builtin_nanf' in a context with no program — call it through 'callByName'` | 2 | 2 | gcc/testsuite/gcc.dg/c23-float-4.c, gcc/testsuite/gcc.dg/c23-float-5.c |
| `unsupported:compound assignment lacks parser-native compute type observations` | 2 | 2 | 00174.c, stdarg-4.c |
| `unsupported:extern object 'abs_called' has no definition in the translation unit` | 2 | 2 | builtins/abs-1-lib.c, builtins/uabs-1-lib.c |
| `unsupported:extern object 'x' has no definition in the translation unit` | 2 | 2 | 00094.c, 00110.c |
| `unsupported:goto skips a block declaration` | 2 | 2 | 00129.c, gcc/testsuite/gcc.dg/c23-labels-1.c |
| `unsupported:goto-controlled pointer increment lacks an exact parser path` | 2 | 2 | 950714-1.c, 990524-1.c |
| `unsupported:operator '-' on pointers without array provenance` | 2 | 2 | 980701-1.c, pr36321.c |
| `unsupported:unknown enum declaration 'id65' (name 'B')` | 2 | 2 | gcc/testsuite/gcc.dg/c23-tag-alias-1.c, gcc/testsuite/gcc.dg/c23-tag-alias-2.c |
| `ingestion` | 1 | 1 | 20040629-1.c |
| `libc-call: __builtin_frame_address` | 1 | 1 | frame-address.c |
| `libc-call: f` | 1 | 1 | gcc/testsuite/gcc.dg/torture/c23-stdarg-split-1a.c |
| `libc-call: fopen` | 1 | 1 | 00187.c |
| `libc-call: func` | 1 | 1 | bcp-1.c |
| `libc-call: main_test` | 1 | 1 | builtins/lib/main.c |
| `libc-call: pow` | 1 | 1 | 980709-1.c |
| `libc-call: qsort` | 1 | 1 | pr34456.c |
| `libc-call: signal` | 1 | 1 | 20101011-1.c |
| `unsupported:AlignedAttr` | 1 | 1 | pr108064.c |
| `unsupported:TypeTraitExpr` | 1 | 1 | builtin-types-compatible-p.c |
| `unsupported:__builtin_infl` | 1 | 1 | ieee/inf-1.c |
| `unsupported:block-scope storage class 'extern' is outside the tier` | 1 | 1 | scope-1.c |
| `unsupported:call through an incompatible function-pointer cast` | 1 | 1 | call-trap-1.c |
| `unsupported:call to '__builtin_nan' in a context with no program — call it through 'callByName'` | 1 | 1 | ieee/builtin-nan-1.c |
| `unsupported:default union initialization has no named member` | 1 | 1 | pr23324.c |
| `unsupported:enum bit-field lacks parser-native compatible integer type` | 1 | 1 | 00218.c |
| `unsupported:extern object 'ReadyFlag_NotProperlyInitialized' has no definition in the translation unit` | 1 | 1 | pr31072.c |
| `unsupported:extern object 'aa' has no definition in the translation unit` | 1 | 1 | 20000403-1.c |
| `unsupported:extern object 'i' has no definition in the translation unit` | 1 | 1 | pure-1.c |
| `unsupported:extern object 'p' has no definition in the translation unit` | 1 | 1 | gcc/testsuite/gcc.dg/c23-unreachable-1.c |
| `unsupported:function instrumentation is outside the tier` | 1 | 1 | eeprof-1.c |
| `unsupported:function-to-pointer decay of an unresolved function` | 1 | 1 | 00219.c |
| `unsupported:indirect function pointer declaration 'id18' is not defined` | 1 | 1 | pr54937.c |
| `unsupported:indirect function pointer declaration 'id227' is not defined` | 1 | 1 | 00189.c |
| `unsupported:no layout for parameter type 'int *'` | 1 | 1 | gcc/testsuite/gcc.dg/c23-parm-omit-3.c |
| `unsupported:no size for element type 'va_list'` | 1 | 1 | stdarg-2.c |
| `unsupported:non-null string initializer element exceeds the array extent` | 1 | 1 | pr86714.c |
| `unsupported:not an lvalue: PredefinedExpr` | 1 | 1 | 20001011-1.c |
| `unsupported:operator '-' on pointers from different arrays` | 1 | 1 | 950710-1.c |
| `unsupported:operator operands have unsupported value kinds (C23 6.5)` | 1 | 1 | 20041212-1.c |
| `unsupported:parameter array-bound effects are not retained by clang` | 1 | 1 | pr77767.c |
| `unsupported:pointer byte read requires an address placement oracle` | 1 | 1 | pr17252.c |
| `unsupported:sizeof` | 1 | 1 | 20040411-1.c |
| `unsupported:sprintf` | 1 | 1 | struct-ret-1.c |
| `unsupported:strcpy` | 1 | 1 | string-opt-18.c |
| `unsupported:union initializer has no single selected member` | 1 | 1 | gcc/testsuite/gcc.dg/c23-tag-5.c |
| `unsupported:unknown enum declaration 'id18' (name 'C')` | 1 | 1 | pr91597.c |
| `unsupported:unknown enum declaration 'id543' (name 'e')` | 1 | 1 | 00198.c |
| `unsupported:va_arg incompatible argument type` | 1 | 1 | stdarg-3.c |
| `unsupported:variable-length array 'char[argc]' lacks parser-native bound expression` | 1 | 1 | 00207.c |
| `unsupported:variable-length array 'double[n]' lacks parser-native bound expression` | 1 | 1 | 920929-1.c |
| `unsupported:variable-length array 'int[len][len]' lacks parser-native bound expression` | 1 | 1 | 20221006-1.c |
| `unsupported:variable-length array 'volatile int[a]' lacks parser-native bound expression` | 1 | 1 | gcc/testsuite/gcc.dg/c23-empty-init-1.c |
