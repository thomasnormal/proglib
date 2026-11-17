# PY-REAL baseline

## 2026-11-17 measurement

A fresh built-runner survey covered all 183 manifest modules and 8,677 calls.
It recorded 4,095 MATCH, 4,533 REFUSED, 41 UNCOMPARABLE, one TIMEOUT, and
seven RUNNER rows whose batch did not finish. The run is an incomplete refresh;
the prior complete baseline below remains authoritative. It found no DIVERGE.
The artifact is `library-2026-11-17.json` (gate/ls-python artifact).

The standard-library wild sweep covered 166 files: 7 MATCH, 159 REFUSE, and
zero DIVERGE, TIMEOUT, ORACLE, HUNG, or RUNNER failures. Its current sole-wall
price is Import 26/150, no-static-wall 6/6, and
ImportFrom:accelerator-outside-domain 3/3; the remaining present walls are
class-creation 102, Set:display 27, Lambda 23, accelerator-unmeasured 21,
Delete 14, YieldFrom:delegation 12, ListComp 7, SetComp 6, and Starred:display
5, all with zero sole blockers. The artifact is
`stdlib-2026-11-17.json` (gate/ls-python artifact).

The focused import-wall price drove the 11 sole-import manifest modules:
18 public functions and 135 calls produced 59 MATCH calls, with one fully
VERIFIED module (`email.charset`), five PARTIAL modules, and five REFUSED
modules. The five partial rows have independent walls in their calls; this
price predicts zero new VERIFIED functions from an import-only change. The
artifact is `import-wall-2026-11-17.json` (gate/ls-python artifact), and the
next measured choice is the class-creation wall by agreed calls (2,015).

The exact class-creation price drove 62 modules, 2,015 calls and 183
MATCH calls. It contained 41 PARTIAL rows, 18 REFUSED rows, and 3 BODY-ONLY
rows; the 383 public names include skipped/non-drivable entries, while the
ranked denominator counts 282 modeled functions. No class-creation row
produced a new VERIFIED function, so this wall also has zero measured
function flips. The artifact is `class-creation-exact-2026-11-17.json` (gate/ls-python artifact).

## 2026-11-16 refresh

The verified runner survey covered the current 183-module manifest and 1,542
public functions. It drove 8,677 calls: 138 were MATCH, one module was
INCOMPLETE (`fib`, with 1 of 8 calls completed and matching), and 44 modules
had no drivable call result. No DIVERGE was observed. The standard-library
wild sweep covered 166 files: 7 MATCH, 159 REFUSE, and 0 DIVERGE, TIMEOUT,
ORACLE, HUNG, or RUNNER failures.

The current sole-wall price from the standard-library sweep is:

| Wall | Sole | Present | Static nodes | Files |
|---|---:|---:|---:|---:|
| `import` | 20 | 150 | 807 | 139 |
| no static wall | 4 | 4 | — | — |
| `ImportFrom:accelerator-outside-domain` | 3 | 3 | 3 | 3 |
| `Starred:call` | 1 | 68 | 188 | 69 |
| `DictComp` | 1 | 18 | 22 | 18 |
| `class-creation` | 0 | 102 | — | — |
| `Set:display` | 0 | 27 | 63 | 27 |
| `Lambda` | 0 | 23 | 80 | 23 |
| `ImportFrom:accelerator-unmeasured` | 0 | 21 | 35 | 21 |
| `Delete` | 0 | 14 | 21 | 14 |
| `YieldFrom:delegation` | 0 | 12 | 32 | 13 |
| `ListComp` | 0 | 7 | 10 | 7 |

The next item is therefore the `import` wall: it is the only wall with twenty
sole blockers, while the survey does not yet claim function flips for those
stdlib files. The historical artifacts were moved to the lane gate directory; the current run is recorded above.

The earlier focused function-level price used nine sole-import modules and
112 calls; the fresh 11-module price above supersedes it for planning. No
DIVERGE was observed in either run.

The complete sole-wall price over the 14 sole-wall modules that are in the
manifest is 47 public functions and 161 calls:

| Sole wall | Modules | Public functions | Calls | Matching calls |
|---|---:|---:|---:|---:|
| `import` | 9 | 18 | 112 | 29 |
| `ImportFrom:accelerator-outside-domain` | 3 | 21 | 0 | 0 |
| `Starred:call` | 1 | 5 | 25 | 8 |
| `DictComp` | 1 | 3 | 24 | 16 |

There were no observed DIVERGEs in this focused run; 53 of the 161 calls
matched. The import wall remains
the largest measured sole wall by module count, but its function-level payoff
is limited by the 18 functions and by unmeasured sole-import files outside the
manifest.

The next semantic wall is `DictComp`, chosen by measured payoff over
`Starred:call`: `token.py` is its one sole-wall module, with 3 public functions,
24 driven calls, and 16 matches. The implementation price is a structured
`ast.DictComp` envelope and a direct comprehension semantic case with ordered
generator/filter evaluation and fresh comprehension scope; the extractor must
not lower it to a call or reparse source text. Differential rows must include
empty and nonempty iterables, filters, duplicate keys, and exceptions. The
measured Starred alternative is one sole-wall module with 5 public functions,
25 calls, and 8 matches, so it remains the fallback wall.

The DictComp one-clause/no-filter slice is now admitted end to end: `Expr.dictComp`
has synchronized AST/JSON support, direct trunk and monadic workers, the
`Obs.lean` fuel/world-invariance cases, and the approved CPython extractor emits
the node without lowering or source reparsing. The direct worker preserves
ordered target/key/value evaluation, duplicate-key replacement, hashability
errors, fresh scope and fresh dict allocation. Focused CPython 3.9.25 rows for
`dictcomp_lab` match in both interpreter modes (6/6 rows, 0 refusals).
The remaining filtered and multi-clause forms stay loud. The focused rerun of
the manifest's `token` module used the built runner and 24 battery calls: 16
matched and 8 calls refused on independent ordering comparisons, so no
additional DictComp-only function flip is claimed by that module-level probe.
The subsequent full manifest rerun with the built runner covered all 183
modules and 8,677 calls: 4,095 MATCH, 4,533 REFUSED, 41 UNCOMPARABLE, 1
TIMEOUT, and 7 RUNNER rows whose batch did not finish. It is recorded as an
explicit incomplete refresh rather than replacing the prior complete baseline;
the `token` row remains 16/24 MATCH with no DictComp-only flip.
The direct worker now exists for the one-clause/no-filter shape, and its
`evalDictCompStep` fuel-monotonicity conjunct is included in `Obs.lean`'s
fixed-order mutual induction. The evaluator admits the AST arm for this shape;
filtered and multi-clause forms remain loud. The monadic continuation is now implemented as a
`Kont.dictComp` field with a structural stepper, but its evaluator-side proof
bundle and the trunk/monadic agreement row remain outstanding. No local
shortcut or theorem weakening is sound. The extractor remains loud, so no
semantic flip is claimed before those remaining bundles are built.

The current admission boundary is now exact: the trunk worker, fuel proof,
standalone `PBAllWithDict`, and monadic `Kont.dictComp` continuation all build.
The remaining theorem is the full `pbEvalExpr_succ` arm with a
`PBAllWithDict` hypothesis; changing the old `PBAll` product in place breaks
every established right-associated projection. The extractor therefore still
refuses DictComp, and no differential row is changed until that product
integration is completed.

The admitted-arm probe found a declaration-order constraint: `pbEvalExpr_succ`
is defined before `pbAll` and `pbDictAll`, but its DictComp branch needs the
all-fuel `PBDictCompStep` relation. A direct call to `pbDictAll` is therefore
not in scope; passing it as an extra arm hypothesis requires threading the
relation through the mutual product, while moving the induction block would
rewrite all existing declarations. The probe was reverted after the dependent
build failed, and the extractor remains loud until this structural choice is
implemented as one complete item.

The projection-rewrite price is measured in
`gate/ls-python/pball-rewrite-inventory.txt`: 31
`PBAll` references, 34 conjunction destructures, and 21 successor-arm
theorems. The old product is consumed by 20 existing arms plus the final
`payloadBlind` reduction; the new DictComp component can be threaded through a
named product without changing those declarations. This is the next proof
item, before any extractor or differential-row change.

The priced `PayloadBlind` sub-item is the theorem
`PB-evalDictCompStep`: for every `PayloadTwin o₀ o`, every frame whose heap
slot `pa` contains `o₀`, and every key/value/target expression, the two
`evalDictCompStep` runs on `st` and `st.swapAt pa o` must be related by `PBF`.
Its obligations are target assignment transport, the existing filter and
expression transport lemmas, identical `hashableKey`/`keyRefusal` decisions,
`dictStore`'s heap-independent duplicate-key update, and the fresh-dict
allocation slot/address lemmas. The theorem must then be appended to `PBAll`
and threaded through all existing tuple projections before the DictComp arm is
admitted. This is a finite proof-bundle extension; no fixed-count examples or
payload-insensitive shortcut is sound.

The fallback `Starred:call` probe has now crossed its extractor boundary: the
extractor admits `ast.Starred` positional arguments into the existing synthetic
`<star-arg>` marker, while `**` keyword unpacking remains loud. The monadic
evaluator build remains green; the focused copyreg price (5 public functions,
25 calls, 8 matches) is the next differential check before claiming a wall flip.

The fallback re-ranking is now closed: the eight matching copyreg calls already
use the admitted synthetic marker, while the remaining 17 calls refuse because
the callee observes the unmodelled `callable` protocol. No Starred-only function
flip is measured, so implementing Starred further would not change PY-REAL;
the next fallback wall must be selected from the import/function price or the
callable protocol's own measured surface.

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The full post-stall survey (141 pinned CPython 3.9.25 library rows, run 2026-11-12) has **13 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The targeted import refresh flipped `email.charset` from body REFUSED to VERIFIED with 24/24 matching calls; the call denominator is unchanged because those calls were already driven through the closed-function surface. The 13 VERIFIED modules are `email.charset`, `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The function-level scoreboard has **21 VERIFIED functions out of 540 modeled public functions**, with 503 matching calls among the function calls driven by this survey. A function is counted when at least one pinned CPython call returns normally and every driven call for that function matches; C-accelerator and unsafe-call entries are explicit skips and are outside the modeled-function denominator. A module-level refusal does not turn an independently matching function back into a potential flip. After the targeted import refresh, no remaining wall has a measured function flip; the next price is by newly agreed calls and module rows.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by function flips first, then newly agreed calls, with `sole` and `present` retained as context. The required stall-rule rerun used the complete 141-row survey JSON on 2026-11-12 with
`python3 harness/library_rank.py --provenance census:library --json /tmp/library-rank-current.json /tmp/library-current.json`.
The published figures were revalidated on 2026-11-15 against the post-opaque-import
survey artifact `/tmp/library-full-next.json`; the pre-refresh `/tmp/library-current.json`
artifact predates the `email.charset` flip and is not a comparable ranking input.
The price columns are measured surfaces, not promises: modules, public functions, driven calls, matched calls, rows that would become verified, and functions that would become verified if that wall alone were removed.

| Wall | Present | Sole | Modules | Public functions | Driven calls | Matched calls | Potential rows | Function flips |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `class-creation` | 62 | 0 | 62 | 282 | 2,015 | 183 | 1 | 0 |
| `definition-order` | 34 | 0 | 34 | 178 | 1,288 | 162 | 0 | 0 |
| `import` | 29 | 6 | 29 | 74 | 536 | 118 | 0 | 0 |
| `node:DictComp` | 1 | 1 | 1 | 3 | 24 | 16 | 0 | 0 |
| `accelerator-unmeasured` | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `accelerator-outside-domain` | 2 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| `frozenset` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `heap-plus` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `method call '.extend' on a list is outside the tier` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `try-except` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |

The measured opaque arm now admits the imports needed by `email.charset`; its three public functions are body- and call-verified. `rsa_inverse` remains a separate annotation-observation check. The next ranked wall remains `class-creation`, priced by its 183 newly matching calls and one potential whole-row verification; it has **0 function flips**. The three-item stall rule therefore requires a replan before another zero-flip semantic tier.

The remaining observed messages are one accelerator-domain wall, one heap `+` wall, one unsupported `try/except` wall, one missing `frozenset` builtin, and one list `.extend` wall. They remain recorded per module in the JSON result and are not silently omitted from the ranking.

The baseline command used pinned `python3.9`, fixed fuel (`200000` body, `10000` call), eight calls per public function, a 900-second body bound, and a 120-second per-module call bound. The complete run covered all 183 manifest and in-repo rows in one survey; its eight unfinished calls remain explicit and are not counted as agreement.
