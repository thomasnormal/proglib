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
