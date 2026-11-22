# External-object wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 39 sole dynamic rows whose first refusal is `extern object 'inside_main' has no definition in the translation unit`. Every row is a GCC `builtins` helper translation unit and has no defined `main` function in its parser envelope. The corpus builds these helpers with a companion driver, usually `builtins/lib/main.c`, which defines `inside_main`, `main`, and the `main_test` call. The current single-envelope survey cannot claim the linked behavior.

| measurement | count |
| --- | ---: |
| sole rows | 39 |
| helper envelopes with a read of `inside_main` | 11 |
| helper envelopes with no read of `inside_main` | 28 |
| envelopes with a defined `main` | 0 |

The 11 envelopes that read the external are: `builtins/20010124-1-lib.c`, `builtins/memops-asm-lib.c`, `builtins/memops-asm.c`, `builtins/mempcpy-2.c`, `builtins/mempcpy.c`, `builtins/strcat.c`, `builtins/strlen-2.c`, `builtins/strlen-3.c`, `builtins/strpcpy-2.c`, `builtins/strpcpy.c`, `builtins/strstr-asm-lib.c`.

The remaining 28 rows reach the same setup-global refusal before any read: `builtins/fputs-lib.c`, `builtins/lib/abs.c`, `builtins/lib/bfill.c`, `builtins/lib/bzero.c`, `builtins/lib/chk.c`, `builtins/lib/fprintf.c`, `builtins/lib/memchr.c`, `builtins/lib/memcmp.c`, `builtins/lib/memmove.c`, `builtins/lib/mempcpy.c`, `builtins/lib/memset.c`, `builtins/lib/printf.c`, `builtins/lib/sprintf.c`, `builtins/lib/stpcpy.c`, `builtins/lib/strcat.c`, `builtins/lib/strchr.c`, `builtins/lib/strcmp.c`, `builtins/lib/strcpy.c`, `builtins/lib/strcspn.c`, `builtins/lib/strlen.c`, `builtins/lib/strncat.c`, `builtins/lib/strncmp.c`, `builtins/lib/strncpy.c`, `builtins/lib/strnlen.c`, `builtins/lib/strpbrk.c`, `builtins/lib/strrchr.c`, `builtins/lib/strspn.c`, `builtins/lib/strstr.c`.

The cheapest sound route is a manifest-level companion closure. It must select the helper and its driver sources, run Clang on the unchanged linked translation unit, and emit one parser envelope from that invocation. Adding a default value for an unresolved external would change the program and is not admissible. Until that closure exists, the 39 rows remain excluded from executable MATCH claims and the refusal is retained.

Price: one extractor closure and manifest schema change, followed by one full C1 replay. No evaluator change is priced by this measurement.

