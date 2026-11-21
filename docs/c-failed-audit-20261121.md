# C failed-row sanitizer audit, 2026-11-21

The focused replay admitted five rows whose current verdict is `failed`.
The pinned Clang 21.1.8 sanitizer command used `-fsanitize=undefined,address`
and `-fno-sanitize-recover=all`.

| row | native | sanitizer | sanitizer finding |
| --- | ---: | ---: | --- |
| `20031204-1.c` | exit 0 | exit 0 | none |
| `20121108-1.c` | exit 0 | exit 1 | signed left-shift overflow at the compound-assignment site |
| `20230630-2.c` | abort | abort | no sanitizer diagnostic |
| `20230630-4.c` | abort | abort | no sanitizer diagnostic |
| `960321-1.c` | exit 0 | exit 0 | none |

`20121108-1.c` is a cleanly compiling native UB case. Its current failed
verdict is therefore an unwitnessed-UB classification until the evaluator
returns a loud UB refusal. The other four rows have no sanitizer finding in
this audit. No DIVERGE verdict is claimed by this receipt.

The follow-up replay after the signed-shift boundary reports four failed rows
and one loud unsupported refusal. The remaining failed rows are
`20031204-1.c`, `20230630-2.c`, `20230630-4.c`, and `960321-1.c`. Their native
and sanitizer outcomes remain the same as the table above. The two aborting
rows abort without a sanitizer diagnostic. The two clean rows need evaluator
diagnosis before they can be counted as MATCH or a named refusal.
